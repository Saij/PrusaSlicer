#ifndef slic3r_GUI_ObjectParts_hpp_
#define slic3r_GUI_ObjectParts_hpp_
// #include "OptionsGroup.hpp"

class wxWindow;
class wxSizer;
class wxBoxSizer;
class wxString;
class wxArrayString;
class wxMenu;
class wxDataViewEvent;
class wxKeyEvent;
class wxGLCanvas;
class wxBitmap;

namespace Slic3r {
class ModelObject;
class Model;

namespace GUI {
class ConfigOptionsGroup;
using t_optgroups = std::vector <std::shared_ptr<ConfigOptionsGroup>>;

enum ogGroup{
	ogFrequentlyChangingParameters,
	ogFrequentlyObjectSettings,
 	ogObjectSettings
};

enum LambdaTypeIDs{
	LambdaTypeBox,
	LambdaTypeCylinder,
	LambdaTypeSphere,
	LambdaTypeSlab
};

struct OBJECT_PARAMETERS
{
	LambdaTypeIDs	type = LambdaTypeBox;
	double			dim[3];// = { 1.0, 1.0, 1.0 };
	int				cyl_r = 1;
	int				cyl_h = 1;
	double			sph_rho = 1.0;
	double			slab_h = 1.0;
	double			slab_z = 0.0;
};

typedef std::map<std::string, wxBitmap> t_category_icon;
inline t_category_icon& get_category_icon();

void add_objects_list(wxWindow* parent, wxBoxSizer* sizer);
void add_object_settings(wxWindow* parent, wxBoxSizer* sizer, t_optgroups& optgroups);

wxMenu *create_add_settings_popupmenu(bool is_part);
wxMenu *create_add_part_popupmenu();
wxMenu *create_part_settings_popupmenu();

// Add object to the list
//void add_object(const std::string &name);
void add_object_to_list(const std::string &name, ModelObject* model_object);
// Delete object from the list
void delete_object_from_list();
// Delete all objects from the list
void delete_all_objects_from_list();
// Set count of object on c++ side
void set_object_count(int idx, int count);
// Unselect all objects in the list on c++ side
void unselect_objects();
// Select current object in the list on c++ side
void select_current_object(int idx);
// Select current volume in the list on c++ side
void select_current_volume(int idx, int vol_idx);
// Remove objects/sub-object from the list
void remove();

void object_ctrl_selection_changed();
void object_ctrl_context_menu();
void object_ctrl_key_event(wxKeyEvent& event);
void object_ctrl_item_value_change(wxDataViewEvent& event);
void show_context_menu();
bool is_splittable_object(const bool split_part);

void init_mesh_icons();
void set_event_object_selection_changed(const int& event);
void set_event_object_settings_changed(const int& event); 
void set_event_remove_object(const int& event);
void set_event_update_scene(const int& event);
void set_objects_from_model(Model &model);

bool is_parts_changed();
bool is_part_settings_changed();

void load_part(	ModelObject* model_object, 
				wxArrayString& part_names, const bool is_modifier); 

void load_lambda( ModelObject* model_object, 
				wxArrayString& part_names, const bool is_modifier); 
void load_lambda( const std::string& type_name);

void on_btn_load(bool is_modifier = false, bool is_lambda = false);
void on_btn_del();
void on_btn_split(const bool split_part);
void on_btn_move_up();
void on_btn_move_down();

void parts_changed(int obj_idx);
void part_selection_changed();

// show/hide "Extruder" column for Objects List
void set_extruder_column_hidden(bool hide);
// update extruder in current config
void update_extruder_in_config(const wxString& selection);

void set_uniform_scaling(const bool uniform_scale);

void on_begin_drag(wxDataViewEvent &event);
void on_drop_possible(wxDataViewEvent &event);
void on_drop(wxDataViewEvent &event);

// update extruder column for objects_ctrl according to extruders count
void update_objects_list_extruder_column(int extruders_count);

// Create/Update/Reset double slider on 3dPreview
void create_double_slider(wxWindow* parent, wxBoxSizer* sizer, wxGLCanvas* canvas);
void update_double_slider(bool force_sliders_full_range);
void reset_double_slider();
// update DoubleSlider after keyDown in canvas
void update_double_slider_from_canvas(wxKeyEvent& event);

void show_manipulation_sizer(const bool is_simple_mode);

} //namespace GUI
} //namespace Slic3r 
#endif  //slic3r_GUI_ObjectParts_hpp_