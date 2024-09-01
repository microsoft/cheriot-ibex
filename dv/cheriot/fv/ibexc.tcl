clear -all
set rtlRoot ../../../rtl
set primRoot ../../../prim
set verifRoot ..

# use sv2017 standard
# +define+FETCH_CORRECT_FORMAL 

analyze -sv17 -f ./ibexc.jp.f    
#analyze -sv17 +define+MEM_0DLY_FORMAL -f ./ibexc.jp.f    
#analyze -sv17 +define+FETCH_CORRECT_FORMAL -f ./ibexc.jp.f    

elaborate -parameter RV32E 1 -parameter CheriTBRE 1 -parameter CheriStkz 1 -top ibex_top
 
# use clock rising edge only be default
reset ~rst_ni
clock clk_i


prove -bg -all
#prove -bg -property ibex_top.u_ibex_core.ibex_core_dv_ext_i.IbexFetchLsbGood
#prove -bg -property ibex_top.u_ibex_core.ibex_core_dv_ext_i.IbexFetchMsbGood

