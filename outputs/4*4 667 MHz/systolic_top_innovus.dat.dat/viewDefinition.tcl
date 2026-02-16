if {![namespace exists ::IMEX]} { namespace eval ::IMEX {} }
set ::IMEX::dataVar [file dirname [file normalize [info script]]]
set ::IMEX::libVar ${::IMEX::dataVar}/libs

create_library_set -name tt_libs\
   -timing\
    [list ${::IMEX::libVar}/mmmc/asap7sc7p5t_AO_LVT_TT_nldm_211120.lib\
    ${::IMEX::libVar}/mmmc/asap7sc7p5t_INVBUF_LVT_TT_nldm_220122.lib\
    ${::IMEX::libVar}/mmmc/asap7sc7p5t_OA_LVT_TT_nldm_211120.lib\
    ${::IMEX::libVar}/mmmc/asap7sc7p5t_SEQ_LVT_TT_nldm_220123.lib\
    ${::IMEX::libVar}/mmmc/asap7sc7p5t_SIMPLE_LVT_TT_nldm_211120.lib\
    ${::IMEX::libVar}/mmmc/asap7sc7p5t_AO_SLVT_TT_nldm_211120.lib\
    ${::IMEX::libVar}/mmmc/asap7sc7p5t_INVBUF_SLVT_TT_nldm_220122.lib\
    ${::IMEX::libVar}/mmmc/asap7sc7p5t_OA_SLVT_TT_nldm_211120.lib\
    ${::IMEX::libVar}/mmmc/asap7sc7p5t_SEQ_SLVT_TT_nldm_220123.lib\
    ${::IMEX::libVar}/mmmc/asap7sc7p5t_SIMPLE_SLVT_TT_nldm_211120.lib]
create_rc_corner -name rc_typical\
   -preRoute_res 1\
   -postRoute_res 1\
   -preRoute_cap 1\
   -postRoute_cap 1\
   -postRoute_xcap 1\
   -preRoute_clkres 0\
   -preRoute_clkcap 0
create_delay_corner -name tc_tt\
   -library_set tt_libs\
   -rc_corner rc_typical
create_constraint_mode -name func_mode\
   -sdc_files\
    [list ${::IMEX::dataVar}/mmmc/modes/func_mode/func_mode.sdc]
create_analysis_view -name view_tt -constraint_mode func_mode -delay_corner tc_tt -latency_file ${::IMEX::dataVar}/mmmc/views/view_tt/latency.sdc
set_analysis_view -setup [list view_tt] -hold [list view_tt]
catch {set_interactive_constraint_mode [list func_mode] } 
