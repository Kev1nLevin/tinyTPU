add_search_path ../lib/ ../lef/scaled/ ../techlef/ -library -both
read_library -liberty -both \
    /home/kevinlevin/Projects/Neural \
    Accelerator/run/../lib/asap7sc7p5t_AO_LVT_TT_nldm_211120.lib \
    Accelerator/run/../lib/asap7sc7p5t_AO_SLVT_TT_nldm_211120.lib \
    Accelerator/run/../lib/asap7sc7p5t_INVBUF_LVT_TT_nldm_220122.lib \
    Accelerator/run/../lib/asap7sc7p5t_INVBUF_SLVT_TT_nldm_220122.lib \
    Accelerator/run/../lib/asap7sc7p5t_OA_LVT_TT_nldm_211120.lib \
    Accelerator/run/../lib/asap7sc7p5t_OA_SLVT_TT_nldm_211120.lib \
    Accelerator/run/../lib/asap7sc7p5t_SEQ_LVT_TT_nldm_220123.lib \
    Accelerator/run/../lib/asap7sc7p5t_SEQ_SLVT_TT_nldm_220123.lib \
    Accelerator/run/../lib/asap7sc7p5t_SIMPLE_LVT_TT_nldm_211120.lib \
    Accelerator/run/../lib/asap7sc7p5t_SIMPLE_SLVT_TT_nldm_211120.lib \
    Network

