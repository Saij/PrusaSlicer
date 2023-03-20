#prusaslicer_add_cmake_project(JPEG
#    URL https://github.com/libjpeg-turbo/libjpeg-turbo/archive/refs/tags/2.0.6.zip
#    URL_HASH SHA256=017bdc33ff3a72e11301c0feb4657cb27719d7f97fa67a78ed506c594218bbf1
#    DEPENDS ${ZLIB_PKG}
#    CMAKE_ARGS
#        -DENABLE_SHARED=OFF
#        -DENABLE_STATIC=ON
#)

prusaslicer_add_cmake_project(JPEG
    URL https://github.com/libjpeg-turbo/libjpeg-turbo/archive/refs/tags/2.1.0.zip
    URL_HASH SHA256=9518d553961d3363148ac10a6a8b802fde24b6218475dd9b9e134d31718ab24d
    DEPENDS ${ZLIB_PKG}
    CMAKE_ARGS
        -DENABLE_SHARED=OFF
        -DENABLE_STATIC=ON
)
