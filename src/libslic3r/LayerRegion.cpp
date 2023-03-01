#include "ExPolygon.hpp"
#include "Layer.hpp"
#include "BridgeDetector.hpp"
#include "ClipperUtils.hpp"
#include "Geometry.hpp"
#include "PerimeterGenerator.hpp"
#include "Print.hpp"
#include "Surface.hpp"
#include "BoundingBox.hpp"
#include "SVG.hpp"

#include <algorithm>
#include <string>
#include <map>

#include <boost/log/trivial.hpp>

namespace Slic3r {

Flow LayerRegion::flow(FlowRole role) const
{
    return this->flow(role, m_layer->height);
}

Flow LayerRegion::flow(FlowRole role, double layer_height) const
{
    return m_region->flow(*m_layer->object(), role, layer_height, m_layer->id() == 0);
}

Flow LayerRegion::bridging_flow(FlowRole role) const
{
    const PrintRegion       &region         = this->region();
    const PrintRegionConfig &region_config  = region.config();
    const PrintObject       &print_object   = *this->layer()->object();
    if (print_object.config().thick_bridges) {
        // The old Slic3r way (different from all other slicers): Use rounded extrusions.
        // Get the configured nozzle_diameter for the extruder associated to the flow role requested.
        // Here this->extruder(role) - 1 may underflow to MAX_INT, but then the get_at() will follback to zero'th element, so everything is all right.
        auto nozzle_diameter = float(print_object.print()->config().nozzle_diameter.get_at(region.extruder(role) - 1));
        // Applies default bridge spacing.
        return Flow::bridging_flow(float(sqrt(region_config.bridge_flow_ratio)) * nozzle_diameter, nozzle_diameter);
    } else {
        // The same way as other slicers: Use normal extrusions. Apply bridge_flow_ratio while maintaining the original spacing.
        return this->flow(role).with_flow_ratio(region_config.bridge_flow_ratio);
    }
}

// Fill in layerm->fill_surfaces by trimming the layerm->slices by layerm->fill_expolygons.
void LayerRegion::slices_to_fill_surfaces_clipped()
{
    // Collect polygons per surface type.
    std::array<std::vector<const Surface*>, size_t(stCount)> by_surface;
    for (const Surface &surface : this->slices())
        by_surface[size_t(surface.surface_type)].emplace_back(&surface);
    // Trim surfaces by the fill_boundaries.
    m_fill_surfaces.surfaces.clear();
    for (size_t surface_type = 0; surface_type < size_t(stCount); ++ surface_type) {
        const std::vector<const Surface*> &this_surfaces = by_surface[surface_type];
        if (! this_surfaces.empty())
            m_fill_surfaces.append(intersection_ex(this_surfaces, this->fill_expolygons()), SurfaceType(surface_type));
    }
}

inline void run_perimeter_generator(
    bool                                    use_arachne,
    // Inputs:
    const PerimeterGenerator::Parameters    &params,
    const ExPolygons                        *surface_polygons,
    const ExPolygons                        *lower_slices,
    int                                     loop_number,
    bool                                    no_external_perimeters,
    // Cache:
    Polygons                                &lower_slices_polygons_cache,
    // Output:
    // Loops with the external thin walls
    ExtrusionEntityCollection               &out_loops,
    // Gaps without the thin walls
    ExtrusionEntityCollection               &out_gap_fill,
    // Infills without the gap fills
    ExPolygons                              &out_fill_expolygons
) {
    if (use_arachne)
        PerimeterGenerator::process_arachne(
            // input:
            params,
            surface_polygons,
            lower_slices,
            loop_number,
            no_external_perimeters,
            lower_slices_polygons_cache,
            // output:
            out_loops,
            out_gap_fill,
            out_fill_expolygons
        );
    else
        PerimeterGenerator::process_classic(
            // input:
            params,
            surface_polygons,
            lower_slices,
            loop_number,
            no_external_perimeters,
            lower_slices_polygons_cache,
            // output:
            out_loops,
            out_gap_fill,
            out_fill_expolygons
        );
}

// Produce perimeter extrusions, gap fill extrusions and fill polygons for input slices.
void LayerRegion::make_perimeters(
    // Input slices for which the perimeters, gap fills and fill expolygons are to be generated.
    const SurfaceCollection                                &slices,
    // Ranges of perimeter extrusions and gap fill extrusions per suface, referencing
    // newly created extrusions stored at this LayerRegion.
    std::vector<std::pair<ExtrusionRange, ExtrusionRange>> &perimeter_and_gapfill_ranges,
    // All fill areas produced for all input slices above.
    ExPolygons                                             &fill_expolygons,
    // Ranges of fill areas above per input slice.
    std::vector<ExPolygonRange>                            &fill_expolygons_ranges)
{
    m_perimeters.clear();
    m_thin_fills.clear();

    perimeter_and_gapfill_ranges.reserve(perimeter_and_gapfill_ranges.size() + slices.size());
    // There may be more expolygons produced per slice, thus this reserve is conservative.
    fill_expolygons.reserve(fill_expolygons.size() + slices.size());
    fill_expolygons_ranges.reserve(fill_expolygons_ranges.size() + slices.size());

    const PrintConfig       &print_config  = this->layer()->object()->print()->config();
    const PrintRegionConfig &region_config = this->region().config();
    // This needs to be in sync with PrintObject::_slice() slicing_mode_normal_below_layer!
    bool spiral_vase = print_config.spiral_vase &&
        //FIXME account for raft layers.
        (this->layer()->id() >= size_t(region_config.bottom_solid_layers.value) &&
         this->layer()->print_z >= region_config.bottom_solid_min_thickness - EPSILON);

    PerimeterGenerator::Parameters params(
        this->layer()->height,
        int(this->layer()->id()),
        this->flow(frPerimeter),
        this->flow(frExternalPerimeter),
        this->bridging_flow(frPerimeter),
        this->flow(frSolidInfill),
        region_config,
        this->layer()->object()->config(),
        print_config,
        spiral_vase
    );

    // Cummulative sum of polygons over all the regions.
    const ExPolygons *lower_slices = this->layer()->lower_layer ? &this->layer()->lower_layer->lslices : nullptr;
    const ExPolygons *upper_slices = this->layer()->upper_layer ? &this->layer()->upper_layer->lslices : nullptr;
    // Cache for offsetted lower_slices
    Polygons          lower_layer_polygons_cache;

    for (const Surface &surface : slices) {
        auto perimeters_begin       = uint32_t(m_perimeters.size());
        auto gap_fills_begin        = uint32_t(m_thin_fills.size());
        auto fill_expolygons_begin  = uint32_t(fill_expolygons.size());
        bool no_external_perimeters = false;

        coord_t ext_perimeter_width = params.ext_perimeter_flow.scaled_width();
        coord_t ext_perimeter_spacing = params.ext_perimeter_flow.scaled_spacing();
        coord_t perimeter_width = params.perimeter_flow.scaled_width();

        ExPolygons surface_polygons;
        if (this->layer()->object()->config().perimeter_generator.value == PerimeterGeneratorType::Arachne && !spiral_vase)
            surface_polygons = offset_ex(surface.expolygon.simplify_p(params.scaled_resolution), - float(ext_perimeter_width / 2. - ext_perimeter_spacing / 2.));
        else
            surface_polygons = union_ex(surface.expolygon.simplify_p(params.scaled_resolution));

        // we need to process each island separately because we might have different
        // extra perimeters for each one
        // detect how many perimeters must be generated for this island
        int loop_number = params.config.perimeters + surface.extra_perimeters - 1; // 0-indexed loops

        // If we are on the topmost layer and only_one_perimeter_top is active
        // directly switch to only 1 perimeter (if before we had more than 1)
        if (loop_number > 0 && params.config.only_one_perimeter_top != OnePerimeterTopType::None && upper_slices == nullptr) {
            loop_number = 0;
        }

        // If we are on the bottommost layer and only_one_perimeter_bottom is active
        // we set the number of loops to 0 to only generate 1 perimeter (if before we had more than 1)
        if (loop_number > 0 && params.config.only_one_perimeter_bottom && lower_slices == nullptr) {
            loop_number = 0;
        }

        // If we have more than one perimeter
        // and the parameter only_one_perimeter_top active for all surfaces
        // and are not on the topmost layer
        if (loop_number > 0 && params.config.only_one_perimeter_top == OnePerimeterTopType::TopSurfaces && upper_slices != nullptr) {
            // Split the polygons into top surface/not top surface

            // Don't take too thin areas into account
            double min_width_top_surface = std::max(double(ext_perimeter_spacing / 2 + 10), double(perimeter_width * 2));
            ExPolygons grown_upper_slices = expand_ex(*upper_slices, min_width_top_surface);

            // Get the part of the current layer that is pure top surface
            ExPolygons top_surface_polygons = diff_ex(surface_polygons, grown_upper_slices, ApplySafetyOffset::Yes);
            
            // If we have a top-surface we switch to only one perimeter
            if (!top_surface_polygons.empty()) {
                // Get the offset from solid surface anchor
                coord_t offset_top_surface = scale_(EXTERNAL_INFILL_MARGIN);
                coord_t perimeter_spacing  = params.perimeter_flow.scaled_spacing();

                // If possible, try to not push the extra perimeters inside the sparse infill
                if (offset_top_surface > 0.9 * (params.config.perimeters.value <= 1 ? 0. : (perimeter_spacing * (params.config.perimeters.value - 1))))
                    offset_top_surface -= coord_t(0.9 * (params.config.perimeters.value <= 1 ? 0. : (perimeter_spacing * (params.config.perimeters.value - 1))));
                else
                    offset_top_surface = 0;

                // Generate external perimeter for current surface
                ExPolygons temp_infill;
                ExtrusionEntityCollection temp_gap_fills;
                run_perimeter_generator(
                    this->layer()->object()->config().perimeter_generator.value == PerimeterGeneratorType::Arachne && !spiral_vase,
                    // input:
                    params,
                    &surface_polygons,
                    lower_slices,
                    0,
                    false,
                    lower_layer_polygons_cache,
                    // output:
                    m_perimeters,
                    temp_gap_fills,
                    temp_infill
                );

                // Offset surface ext_perimeter_width inside
                // to compensate for the already created external perimeter
                //surface_polygons = offset_ex(surface_polygons, -ext_perimeter_width);
                coord_t ext_min_spacing = coord_t(ext_perimeter_spacing * (1 - INSET_OVERLAP_TOLERANCE));
                surface_polygons = params.config.thin_walls ? 
                    offset2_ex(
                        surface_polygons,
                        - float(ext_perimeter_width / 2. + ext_min_spacing / 2. - 1),
                        + float(ext_min_spacing / 2. - 1)) :
                    offset_ex(surface_polygons, - float(ext_perimeter_width / 2.));

                // Get the not-top surface, from the "real top" but enlarged by EXTERNAL_INFILL_MARGIN (and the min_width_top_surface we removed a bit before)
                ExPolygons inner_polygons = diff_ex(surface_polygons, offset_ex(top_surface_polygons, offset_top_surface + min_width_top_surface), ApplySafetyOffset::Yes);

                // Get polygons for the top fill
                ExPolygons top_fill_polygons = diff_ex(surface_polygons, inner_polygons, ApplySafetyOffset::Yes);

                // Remove the top fill polygons from the rest of the surface
                surface_polygons = diff_ex(surface_polygons, top_fill_polygons);

                // Generate top infill
                run_perimeter_generator(
                    this->layer()->object()->config().perimeter_generator.value == PerimeterGeneratorType::Arachne && !spiral_vase,
                    // input:
                    params,
                    &top_fill_polygons,
                    lower_slices,
                    -1,
                    false,
                    lower_layer_polygons_cache,
                    // output:
                    m_perimeters,
                    temp_gap_fills,
                    fill_expolygons
                );

                // // Remove two perimeters as we already created them
                loop_number = std::max(-1, loop_number - 1);
                no_external_perimeters = true;
            }
        }

        // Generate other perimeter
        run_perimeter_generator(
            this->layer()->object()->config().perimeter_generator.value == PerimeterGeneratorType::Arachne && !spiral_vase,
            // input:
            params,
            &surface_polygons,
            lower_slices,
            loop_number,
            no_external_perimeters,
            lower_layer_polygons_cache,
            // output:
            m_perimeters,
            m_thin_fills,
            fill_expolygons
        );
        
        perimeter_and_gapfill_ranges.emplace_back(
            ExtrusionRange{ perimeters_begin, uint32_t(m_perimeters.size()) }, 
            ExtrusionRange{ gap_fills_begin,  uint32_t(m_thin_fills.size()) });
        fill_expolygons_ranges.emplace_back(ExtrusionRange{ fill_expolygons_begin, uint32_t(fill_expolygons.size()) });
    }
}

//#define EXTERNAL_SURFACES_OFFSET_PARAMETERS ClipperLib::jtMiter, 3.
//#define EXTERNAL_SURFACES_OFFSET_PARAMETERS ClipperLib::jtMiter, 1.5
#define EXTERNAL_SURFACES_OFFSET_PARAMETERS ClipperLib::jtSquare, 0.

void LayerRegion::process_external_surfaces(const Layer *lower_layer, const Polygons *lower_layer_covered)
{
    const bool      has_infill = this->region().config().fill_density.value > 0.;
    const float		margin 	   = float(scale_(EXTERNAL_INFILL_MARGIN));

#ifdef SLIC3R_DEBUG_SLICE_PROCESSING
    export_region_fill_surfaces_to_svg_debug("3_process_external_surfaces-initial");
#endif /* SLIC3R_DEBUG_SLICE_PROCESSING */

    // 1) Collect bottom and bridge surfaces, each of them grown by a fixed 3mm offset
    // for better anchoring.
    // Bottom surfaces, grown.
    Surfaces                    bottom;
    // Bridge surfaces, initialy not grown.
    Surfaces                    bridges;
    // Top surfaces, grown.
    Surfaces                    top;
    // Internal surfaces, not grown.
    Surfaces                    internal;
    // Areas, where an infill of various types (top, bottom, bottom bride, sparse, void) could be placed.
    Polygons                    fill_boundaries = to_polygons(this->fill_expolygons());
    Polygons  					lower_layer_covered_tmp;

    // Collect top surfaces and internal surfaces.
    // Collect fill_boundaries: If we're slicing with no infill, we can't extend external surfaces over non-existent infill.
    // This loop destroys the surfaces (aliasing this->fill_surfaces.surfaces) by moving into top/internal/fill_boundaries!

    {
        // Voids are sparse infills if infill rate is zero.
        Polygons voids;
        for (const Surface &surface : this->fill_surfaces()) {
            if (surface.is_top()) {
                // Collect the top surfaces, inflate them and trim them by the bottom surfaces.
                // This gives the priority to bottom surfaces.
                surfaces_append(top, offset_ex(surface.expolygon, margin, EXTERNAL_SURFACES_OFFSET_PARAMETERS), surface);
            } else if (surface.surface_type == stBottom || (surface.surface_type == stBottomBridge && lower_layer == nullptr)) {
                // Grown by 3mm.
                surfaces_append(bottom, offset_ex(surface.expolygon, margin, EXTERNAL_SURFACES_OFFSET_PARAMETERS), surface);
            } else if (surface.surface_type == stBottomBridge) {
                if (! surface.empty())
                    bridges.emplace_back(surface);
            }
            if (surface.is_internal()) {
            	assert(surface.surface_type == stInternal || surface.surface_type == stInternalSolid);
            	if (! has_infill && lower_layer != nullptr)
            		polygons_append(voids, surface.expolygon);
            	internal.emplace_back(std::move(surface));
            }
        }
        if (! has_infill && lower_layer != nullptr && ! voids.empty()) {
        	// Remove voids from fill_boundaries, that are not supported by the layer below.
            if (lower_layer_covered == nullptr) {
            	lower_layer_covered = &lower_layer_covered_tmp;
            	lower_layer_covered_tmp = to_polygons(lower_layer->lslices);
            }
            if (! lower_layer_covered->empty())
            	voids = diff(voids, *lower_layer_covered);
            fill_boundaries = diff(fill_boundaries, voids);
        }
    }

#if 0
    {
        static int iRun = 0;
        bridges.export_to_svg(debug_out_path("bridges-before-grouping-%d.svg", iRun ++), true);
    }
#endif

    if (bridges.empty())
    {
        fill_boundaries = union_safety_offset(fill_boundaries);
    } else
    {
        // 1) Calculate the inflated bridge regions, each constrained to its island.
        ExPolygons               fill_boundaries_ex = union_safety_offset_ex(fill_boundaries);
        std::vector<Polygons>    bridges_grown;
        std::vector<BoundingBox> bridge_bboxes;

#ifdef SLIC3R_DEBUG_SLICE_PROCESSING
        {
            static int iRun = 0;
            SVG svg(debug_out_path("3_process_external_surfaces-fill_regions-%d.svg", iRun ++).c_str(), get_extents(fill_boundaries_ex));
            svg.draw(fill_boundaries_ex);
            svg.draw_outline(fill_boundaries_ex, "black", "blue", scale_(0.05)); 
            svg.Close();
        }

//        export_region_fill_surfaces_to_svg_debug("3_process_external_surfaces-initial");
#endif /* SLIC3R_DEBUG_SLICE_PROCESSING */
 
        {
            // Bridge expolygons, grown, to be tested for intersection with other bridge regions.
            std::vector<BoundingBox> fill_boundaries_ex_bboxes = get_extents_vector(fill_boundaries_ex);
            bridges_grown.reserve(bridges.size());
            bridge_bboxes.reserve(bridges.size());
            for (size_t i = 0; i < bridges.size(); ++ i) {
                // Find the island of this bridge.
                const Point pt = bridges[i].expolygon.contour.points.front();
                int idx_island = -1;
                for (int j = 0; j < int(fill_boundaries_ex.size()); ++ j)
                    if (fill_boundaries_ex_bboxes[j].contains(pt) && 
                        fill_boundaries_ex[j].contains(pt)) {
                        idx_island = j;
                        break;
                    }
                // Grown by 3mm.
                Polygons polys = offset(bridges[i].expolygon, margin, EXTERNAL_SURFACES_OFFSET_PARAMETERS);
                if (idx_island == -1) {
				    BOOST_LOG_TRIVIAL(trace) << "Bridge did not fall into the source region!";
                } else {
                    // Found an island, to which this bridge region belongs. Trim it,
                    polys = intersection(polys, fill_boundaries_ex[idx_island]);
                }
                bridge_bboxes.push_back(get_extents(polys));
                bridges_grown.push_back(std::move(polys));
            }
        }

        // 2) Group the bridge surfaces by overlaps.
        std::vector<size_t> bridge_group(bridges.size(), (size_t)-1);
        size_t n_groups = 0; 
        for (size_t i = 0; i < bridges.size(); ++ i) {
            // A grup id for this bridge.
            size_t group_id = (bridge_group[i] == size_t(-1)) ? (n_groups ++) : bridge_group[i];
            bridge_group[i] = group_id;
            // For all possibly overlaping bridges:
            for (size_t j = i + 1; j < bridges.size(); ++ j) {
                if (! bridge_bboxes[i].overlap(bridge_bboxes[j]))
                    continue;
                if (intersection(bridges_grown[i], bridges_grown[j]).empty())
                    continue;
                // The two bridge regions intersect. Give them the same group id.
                if (bridge_group[j] != size_t(-1)) {
                    // The j'th bridge has been merged with some other bridge before.
                    size_t group_id_new = bridge_group[j];
                    for (size_t k = 0; k < j; ++ k)
                        if (bridge_group[k] == group_id)
                            bridge_group[k] = group_id_new;
                    group_id = group_id_new;
                }
                bridge_group[j] = group_id;
            }
        }

        // 3) Merge the groups with the same group id, detect bridges.
        {
			BOOST_LOG_TRIVIAL(trace) << "Processing external surface, detecting bridges. layer" << this->layer()->print_z << ", bridge groups: " << n_groups;
            for (size_t group_id = 0; group_id < n_groups; ++ group_id) {
                size_t n_bridges_merged = 0;
                size_t idx_last = (size_t)-1;
                for (size_t i = 0; i < bridges.size(); ++ i) {
                    if (bridge_group[i] == group_id) {
                        ++ n_bridges_merged;
                        idx_last = i;
                    }
                }
                if (n_bridges_merged == 0)
                    // This group has no regions assigned as these were moved into another group.
                    continue;
                // Collect the initial ungrown regions and the grown polygons.
                ExPolygons  initial;
                Polygons    grown;
                for (size_t i = 0; i < bridges.size(); ++ i) {
                    if (bridge_group[i] != group_id)
                        continue;
                    initial.push_back(std::move(bridges[i].expolygon));
                    polygons_append(grown, bridges_grown[i]);
                }
                // detect bridge direction before merging grown surfaces otherwise adjacent bridges
                // would get merged into a single one while they need different directions
                // also, supply the original expolygon instead of the grown one, because in case
                // of very thin (but still working) anchors, the grown expolygon would go beyond them
                double custom_angle = Geometry::deg2rad(this->region().config().bridge_angle.value);
                if (custom_angle > 0.0) {
                    bridges[idx_last].bridge_angle = custom_angle;
                } else {
                    auto [bridging_dir, unsupported_dist] = detect_bridging_direction(to_polygons(initial), to_polygons(lower_layer->lslices));
                    bridges[idx_last].bridge_angle = PI + std::atan2(bridging_dir.y(), bridging_dir.x());

                    // #if 1
                    //     coordf_t    stroke_width = scale_(0.06);
                    //     BoundingBox bbox         = get_extents(initial);
                    //     bbox.offset(scale_(1.));
                    //     ::Slic3r::SVG
                    //     svg(debug_out_path(("bridge"+std::to_string(bridges[idx_last].bridge_angle)+"_"+std::to_string(this->layer()->bottom_z())).c_str()),
                    //     bbox);

                    //     svg.draw(initial, "cyan");
                    //     svg.draw(to_lines(lower_layer->lslices), "green", stroke_width);
                    // #endif
                }

                /*
                BridgeDetector bd(initial, lower_layer->lslices, this->bridging_flow(frInfill).scaled_width());
                #ifdef SLIC3R_DEBUG
                printf("Processing bridge at layer %zu:\n", this->layer()->id());
                #endif
				double custom_angle = Geometry::deg2rad(this->region().config().bridge_angle.value);
				if (bd.detect_angle(custom_angle)) {
                    bridges[idx_last].bridge_angle = bd.angle;
                    if (this->layer()->object()->has_support()) {
//                        polygons_append(this->bridged, bd.coverage());
                        append(m_unsupported_bridge_edges, bd.unsupported_edges());
                    }
				} else if (custom_angle > 0) {
					// Bridge was not detected (likely it is only supported at one side). Still it is a surface filled in
					// using a bridging flow, therefore it makes sense to respect the custom bridging direction.
					bridges[idx_last].bridge_angle = custom_angle;
				}
                */
                // without safety offset, artifacts are generated (GH #2494)
                surfaces_append(bottom, union_safety_offset_ex(grown), bridges[idx_last]);
            }

            fill_boundaries = to_polygons(fill_boundaries_ex);
			BOOST_LOG_TRIVIAL(trace) << "Processing external surface, detecting bridges - done";
		}

    #if 0
        {
            static int iRun = 0;
            bridges.export_to_svg(debug_out_path("bridges-after-grouping-%d.svg", iRun ++), true);
        }
    #endif
    }

    Surfaces new_surfaces;
    {
        // Merge top and bottom in a single collection.
        surfaces_append(top, std::move(bottom));
        // Intersect the grown surfaces with the actual fill boundaries.
        Polygons bottom_polygons = to_polygons(bottom);
        for (size_t i = 0; i < top.size(); ++ i) {
            Surface &s1 = top[i];
            if (s1.empty())
                continue;
            Polygons polys;
            polygons_append(polys, to_polygons(std::move(s1)));
            for (size_t j = i + 1; j < top.size(); ++ j) {
                Surface &s2 = top[j];
                if (! s2.empty() && surfaces_could_merge(s1, s2)) {
                    polygons_append(polys, to_polygons(std::move(s2)));
                    s2.clear();
                }
            }
            if (s1.is_top())
                // Trim the top surfaces by the bottom surfaces. This gives the priority to the bottom surfaces.
                polys = diff(polys, bottom_polygons);
            surfaces_append(
                new_surfaces,
                // Don't use a safety offset as fill_boundaries were already united using the safety offset.
                intersection_ex(polys, fill_boundaries),
                s1);
        }
    }
    
    // Subtract the new top surfaces from the other non-top surfaces and re-add them.
    Polygons new_polygons = to_polygons(new_surfaces);
    for (size_t i = 0; i < internal.size(); ++ i) {
        Surface &s1 = internal[i];
        if (s1.empty())
            continue;
        Polygons polys;
        polygons_append(polys, to_polygons(std::move(s1)));
        for (size_t j = i + 1; j < internal.size(); ++ j) {
            Surface &s2 = internal[j];
            if (! s2.empty() && surfaces_could_merge(s1, s2)) {
                polygons_append(polys, to_polygons(std::move(s2)));
                s2.clear();
            }
        }
        ExPolygons new_expolys = diff_ex(polys, new_polygons);
        polygons_append(new_polygons, to_polygons(new_expolys));
        surfaces_append(new_surfaces, std::move(new_expolys), s1);
    }
    
    m_fill_surfaces.surfaces = std::move(new_surfaces);

#ifdef SLIC3R_DEBUG_SLICE_PROCESSING
    export_region_fill_surfaces_to_svg_debug("3_process_external_surfaces-final");
#endif /* SLIC3R_DEBUG_SLICE_PROCESSING */
}

void LayerRegion::prepare_fill_surfaces()
{
#ifdef SLIC3R_DEBUG_SLICE_PROCESSING
    export_region_slices_to_svg_debug("2_prepare_fill_surfaces-initial");
    export_region_fill_surfaces_to_svg_debug("2_prepare_fill_surfaces-initial");
#endif /* SLIC3R_DEBUG_SLICE_PROCESSING */ 

    /*  Note: in order to make the psPrepareInfill step idempotent, we should never
        alter fill_surfaces boundaries on which our idempotency relies since that's
        the only meaningful information returned by psPerimeters. */
    
    bool spiral_vase = this->layer()->object()->print()->config().spiral_vase;

    // if no solid layers are requested, turn top/bottom surfaces to internal
    // For Lightning infill, infill_only_where_needed is ignored because both
    // do a similar thing, and their combination doesn't make much sense.
    if (! spiral_vase && this->region().config().top_solid_layers == 0) {
        for (Surface &surface : m_fill_surfaces)
            if (surface.is_top())
                surface.surface_type = this->layer()->object()->config().infill_only_where_needed && this->region().config().fill_pattern != ipLightning ? stInternalVoid : stInternal;
    }
    if (this->region().config().bottom_solid_layers == 0) {
        for (Surface &surface : m_fill_surfaces)
            if (surface.is_bottom()) // (surface.surface_type == stBottom)
                surface.surface_type = stInternal;
    }

    // turn too small internal regions into solid regions according to the user setting
    if (! spiral_vase && this->region().config().fill_density.value > 0) {
        // scaling an area requires two calls!
        double min_area = scale_(scale_(this->region().config().solid_infill_below_area.value));
        for (Surface &surface : m_fill_surfaces)
            if (surface.surface_type == stInternal && surface.area() <= min_area)
                surface.surface_type = stInternalSolid;
    }

#ifdef SLIC3R_DEBUG_SLICE_PROCESSING
    export_region_slices_to_svg_debug("2_prepare_fill_surfaces-final");
    export_region_fill_surfaces_to_svg_debug("2_prepare_fill_surfaces-final");
#endif /* SLIC3R_DEBUG_SLICE_PROCESSING */
}

double LayerRegion::infill_area_threshold() const
{
    double ss = this->flow(frSolidInfill).scaled_spacing();
    return ss*ss;
}

void LayerRegion::trim_surfaces(const Polygons &trimming_polygons)
{
#ifndef NDEBUG
    for (const Surface &surface : this->slices())
        assert(surface.surface_type == stInternal);
#endif /* NDEBUG */
	m_slices.set(intersection_ex(this->slices().surfaces, trimming_polygons), stInternal);
}

void LayerRegion::elephant_foot_compensation_step(const float elephant_foot_compensation_perimeter_step, const Polygons &trimming_polygons)
{
#ifndef NDEBUG
    for (const Surface &surface : this->slices())
        assert(surface.surface_type == stInternal);
#endif /* NDEBUG */
    Polygons tmp = intersection(this->slices().surfaces, trimming_polygons);
    append(tmp, diff(this->slices().surfaces, opening(this->slices().surfaces, elephant_foot_compensation_perimeter_step)));
    m_slices.set(union_ex(tmp), stInternal);
}

void LayerRegion::export_region_slices_to_svg(const char *path) const
{
    BoundingBox bbox;
    for (const Surface &surface : this->slices())
        bbox.merge(get_extents(surface.expolygon));
    Point legend_size = export_surface_type_legend_to_svg_box_size();
    Point legend_pos(bbox.min(0), bbox.max(1));
    bbox.merge(Point(std::max(bbox.min(0) + legend_size(0), bbox.max(0)), bbox.max(1) + legend_size(1)));

    SVG svg(path, bbox);
    const float transparency = 0.5f;
    for (const Surface &surface : this->slices())
        svg.draw(surface.expolygon, surface_type_to_color_name(surface.surface_type), transparency);
    for (const Surface &surface : this->fill_surfaces())
        svg.draw(surface.expolygon.lines(), surface_type_to_color_name(surface.surface_type));
    export_surface_type_legend_to_svg(svg, legend_pos);
    svg.Close();
}

// Export to "out/LayerRegion-name-%d.svg" with an increasing index with every export.
void LayerRegion::export_region_slices_to_svg_debug(const char *name) const
{
    static std::map<std::string, size_t> idx_map;
    size_t &idx = idx_map[name];
    this->export_region_slices_to_svg(debug_out_path("LayerRegion-slices-%s-%d.svg", name, idx ++).c_str());
}

void LayerRegion::export_region_fill_surfaces_to_svg(const char *path) const
{
    BoundingBox bbox;
    for (const Surface &surface : this->fill_surfaces())
        bbox.merge(get_extents(surface.expolygon));
    Point legend_size = export_surface_type_legend_to_svg_box_size();
    Point legend_pos(bbox.min(0), bbox.max(1));
    bbox.merge(Point(std::max(bbox.min(0) + legend_size(0), bbox.max(0)), bbox.max(1) + legend_size(1)));

    SVG svg(path, bbox);
    const float transparency = 0.5f;
    for (const Surface &surface : this->fill_surfaces()) {
        svg.draw(surface.expolygon, surface_type_to_color_name(surface.surface_type), transparency);
        svg.draw_outline(surface.expolygon, "black", "blue", scale_(0.05)); 
    }
    export_surface_type_legend_to_svg(svg, legend_pos);
    svg.Close();
}

// Export to "out/LayerRegion-name-%d.svg" with an increasing index with every export.
void LayerRegion::export_region_fill_surfaces_to_svg_debug(const char *name) const
{
    static std::map<std::string, size_t> idx_map;
    size_t &idx = idx_map[name];
    this->export_region_fill_surfaces_to_svg(debug_out_path("LayerRegion-fill_surfaces-%s-%d.svg", name, idx ++).c_str());
}

}
 
