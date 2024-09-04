/************************************************************************\
|*                                                                      *|
|*    Copyright (c) 2008  Ashok B.Mehta. All rights reserved.           *|
|*                                                                      *|
|*  This example code should be used only for illustration purpose      *|
|*  This material is not to be reproduced,  copied,  or used  in any    *|
|*  manner without the authorization of the author's written permission *|
|*                                                                      *|
|*  Author: Ashok B. Mehta  (Email:ashokdefineview.com)                 *|
\************************************************************************/

module counter_property (
  input clk, rst_, ld_cnt_, updn_cnt, count_enb,
  input [7:0] data_in,
  input logic [7:0] data_out
  );

default disable iff !rst_;
//------------------------------------

//        CHECK # 1. Check that when 'rst_' is asserted (==0) that data_out == 8'b0

//------------------------------------
`ifdef check1
sequence data_rst_se;
	##1 data_out == 8'b0;
endsequence

property data_rst_pr_a;
	@(posedge clk) !rst_ |-> data_rst_se;
endproperty

property data_rst_pr_c;
	@(posedge clk) !rst_ ##0 data_rst_se;
endproperty

data_rst_a : assert property(data_rst_pr_a) $display($stime,,,"\t\t %m PASS"); 
	else $display($stime,,,"\t\tCOUNTER RESET CHECK FAIL:: rst_=%b data_out=%0d \n", rst_,data_out);
data_rst_c : cover property(data_rst_pr_c) $display($stime,,,"\t\t %m PASS");
`endif
//------------------------------------
//Check for count to hold if count_enb is disabled 

//        CHECK # 2. Check that if ld_cnt_ is deasserted (==1) and count_enb is not enabled
//                   (==0) that data_out HOLDS it's previous value.
//                   Disable this property 'iff (!rst)'

//------------------------------------
`ifdef check2

sequence counter_hold_se;
	$stable(data_out);
endsequence

property counter_hold_pr;
	@(posedge clk) ld_cnt_ && !count_enb |-> ##1 counter_hold_se;
endproperty

counter_hold_a: assert property(counter_hold_pr) $display($stime,,,"\t\t %m PASS"); 
  else $display($stime,,,"\t\tCOUNTER HOLD CHECK FAIL:: counter HOLD \n");
`endif

//------------------------------------

//        CHECK # 3. Check that if ld_cnt_ is deasserted (==1) and count_enb is enabled
//                   (==1) that if updn_cnt==1 the count goes UP and
//                              if updn_cnt==0 the count goes DOWN.
//                   Disable this property 'iff (!rst)'

//------------------------------------

`ifdef check3

sequence counter_count_down_se;
	$past(data_out)-1 == data_out;
endsequence

sequence counter_count_up_se;
	$past(data_out)+1 == data_out;
endsequence

property counter_count_down_pr;
	@(posedge clk) !updn_cnt && ld_cnt_ && count_enb |=> counter_count_down_se; //DUMMY - REMOVE  this line and code correct assertion
endproperty

property counter_count_up_pr;
	@(posedge clk) updn_cnt && ld_cnt_ && count_enb |=> counter_count_up_se; //DUMMY - REMOVE  this line and code correct assertion
endproperty


counter_count_down_check: assert property(counter_count_down_pr) $display($stime,,,"\t\t %m PASS"); 
  else $display($stime,,,"\t\tCOUNTER COUNT CHECK FAIL:: UPDOWN COUNT using $past \n"); 
counter_count_up_check: assert property(counter_count_up_pr) $display($stime,,,"\t\t %m PASS"); 
  else $display($stime,,,"\t\tCOUNTER COUNT CHECK FAIL:: UPDOWN COUNT using $past \n");

`endif

endmodule
