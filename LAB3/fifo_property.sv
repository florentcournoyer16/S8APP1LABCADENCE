`define rd_ptr test_fifo.fi1.rd_ptr
`define wr_ptr test_fifo.fi1.wr_ptr
`define cnt test_fifo.fi1.cnt

module fifo_property(
	input logic [7:0] fifo_data_out,
	input logic       fifo_full, fifo_empty,
	input logic       fifo_write, fifo_read, clk, rst_,
	input logic [7:0] fifo_data_in
);

parameter fifo_depth=8;
parameter fifo_width=8;
                                                                                              
// ------------------------------------------
// 1. Check that on reset, rd_ptr=0; wr_ptr=0; cnt=0; fifo_empty=1 and fifo_full=0
// ------------------------------------------

sequence default_values;
	`rd_ptr == 1'b0 && 
	`wr_ptr == 1'b0 &&
	`cnt == 8'b00000000 && 
	fifo_empty == 1'b1 &&
	fifo_full == 1'b0
endsequence

property prop_check_reset;
	@(posedge clk) !rst_ |-> ##0 default_values;
endproperty

property prop_check_reset_;
	@(posedge clk) !rst_ ##0 default_values;
endproperty

ass_check_reset: assert property (prop_check_reset) else $display($stime,"\t\t FAIL::check_reset\n");
cov_check_reset: cover property (prop_check_reset_) $display($stime,"\t\t PASS::check_reset\n");

// ------------------------------------------
// 2. Check that fifo_empty is asserted the same clock that fifo 'cnt' is 0. Disable this property 'iff (!rst)'
// ------------------------------------------

property prop_fifo_empty_when_cnt_0;
	@(posedge clk) disable iff(!rst_) (`cnt == 8'b00000000) |-> ##0 fifo_empty;
endproperty

property prop_fifo_empty_when_cnt_0_;
	@(posedge clk) disable iff(!rst_) (`cnt == 8'b00000000) ##0 fifo_empty;
endproperty

ass_fifo_empty_when_cnt_0: assert property (prop_fifo_empty_when_cnt_0) else $display($stime,"\t\t FAIL::fifo_empty_when_cnt_0 condition\n");
cov_fifo_empty_when_cnt_0: cover property (prop_fifo_empty_when_cnt_0_) $display($stime,"\t\t PASS::fifo_empty_when_cnt_0 condition\n");


// ------------------------------------------
// 3. Check that fifo_full is asserted any time fifo 'cnt' is greater than 7. Disable this property 'iff (!rst)'
// ------------------------------------------

sequence seq_fifo_saturated;
	(`cnt > 8'b00000111);
endsequence

property prop_fifo_full_when_cnt_8;
	@(posedge clk) disable iff(!rst_) seq_fifo_saturated |-> ##0 fifo_full;
endproperty

property prop_fifo_full_when_cnt_8_;
	@(posedge clk) disable iff(!rst_) seq_fifo_saturated ##0 fifo_full;
endproperty

ass_fifo_full_when_cnt_8: assert property (prop_fifo_full_when_cnt_8) else $display($stime,"\t\t FAIL::fifo_full_when_cnt_8 condition\n");
cov_fifo_full_when_cnt_8: cover property (prop_fifo_full_when_cnt_8_) $display($stime,"\t\t PASS::fifo_full_when_cnt_8 condition\n");

// ------------------------------------------
// 4. Check that if fifo is full and you attempt to write (but not read) that the wr_ptr does not change.
// ------------------------------------------

property prop_fifo_full_write_stable_wrptr;
	@(posedge clk) disable iff(!rst_) (seq_fifo_saturated ##0 fifo_write ##0 !fifo_read) |-> ##1 $stable(`wr_ptr);
endproperty

property prop_fifo_full_write_stable_wrptr_;
	@(posedge clk) disable iff(!rst_) (seq_fifo_saturated ##0 fifo_write ##0 !fifo_read) ##1 $stable(`wr_ptr);
endproperty

ass_fifo_full_write_stable_wrptr: assert property (prop_fifo_full_write_stable_wrptr)  else $display($stime,"\t\t FAIL::fifo_full_write_stable_wrptr condition\n");
cov_fifo_full_write_stable_wrptr: cover property (prop_fifo_full_write_stable_wrptr_) $display($stime,"\t\t PASS::fifo_full_write_stable_wrptr condition\n");

// ------------------------------------------
// 5. Check that if fifo is empty and you attempt to read (but not write) that the rd_ptr does not change.
// ------------------------------------------

sequence seq_fifo_empty;
	(`cnt == 8'b00000000);
endsequence


property prop_fifo_empty_read_stable_rdptr;
	@(posedge clk) disable iff(!rst_) (seq_fifo_empty ##0 fifo_read ##0 !fifo_write) |->  ##1 $stable(`rd_ptr);
endproperty

property prop_fifo_empty_read_stable_rdptr_;
	@(posedge clk) disable iff(!rst_) (seq_fifo_empty ##0 fifo_read ##0 !fifo_write) |->  ##1 $stable(`rd_ptr);
endproperty

ass_fifo_empty_read_stable_rdptr: assert property (prop_fifo_empty_read_stable_rdptr) else $display($stime,"\t\t FAIL::fifo_empty_read_stable_rdptr condition\n");
cov_fifo_empty_read_stable_rdptr: cover property (prop_fifo_empty_read_stable_rdptr_) $display($stime,"\t\t PASS::fifo_empty_read_stable_rdptr condition\n");

// ------------------------------------------
// 6. Write a property to Warn on write to a full fifo This property will give Warning with all simulations  
// ------------------------------------------

property prop_write_on_full_fifo;
	@(posedge clk) disable iff(!rst_) seq_fifo_saturated |-> !fifo_write;
endproperty

// ass_write_on_full_fifo: assert property (prop_write_on_full_fifo) else $display($stime,"\t\t WARNING::write_on_full_fifo\n");

// ------------------------------------------
// 7. Write a property to Warn on read from an empty fifo. This property will give Warning with all simulations  
// ------------------------------------------

property prop_read_on_empty_fifo;
	@(posedge clk) disable iff(!rst_) seq_fifo_empty |-> !fifo_read;
endproperty

// ASS_read_on_empty_fifo: assert property(prop_read_on_empty_fifo) $display($stime,"\t\t WARNING::read_on_empty_fifo condition\n");

// ------------------------------------------
// ------------------------------------------

covergroup covg_fifo
	@(negedge clk && rst_);

	cp_fifo_read: coverpoint fifo_read {
		bins read_0 = {0};
		bins read_1 = {1};
	}

	cp_fifo_write: coverpoint fifo_write {
		bins write_0 = {0};
		bins write_1 = {1};
	}

	cp_fifo_data_in: coverpoint fifo_data_in iff(fifo_read == 1) {
		bins data_min = {8'b00000000};
		bins data_max = {8'b11111111};
		bins data_all[] = {[0:$]};
		bins data_any = { [0:$] };
		bins data_onehot[] = {
			8'b00000001,
			8'b00000010,
			8'b00000100,
			8'b00001000,
			8'b00010000,
			8'b00100000,
			8'b01000000,
			8'b10000000
		};
	}

	cp_fifo_data_out: coverpoint fifo_data_out iff(fifo_write == 1) {
		bins data_min = { 8'b00000000 };
		bins data_max = { 8'b11111111 };
		bins data_all[] = { [0:$] };
		bins data_any = { [0:$] };
		bins data_onehot[] = {
			8'b1 << 0,
			8'b1 << 1,
			8'b1 << 2,
			8'b1 << 3,
			8'b1 << 4,
			8'b1 << 5,
			8'b1 << 6,
			8'b1 << 7
		};
	}

	cp_fifo_full: coverpoint fifo_full {
		bins not_full = {0};
		bins is_full = {1};
	}

	cp_fifo_empty: coverpoint fifo_empty {
		bins not_empty = {0};
		bins is_empty = {1};
	}

	crs_signals_cross: cross cp_fifo_read, cp_fifo_write {
        illegal_bins unwanted_combination = binsof(cp_fifo_read.read_1) && binsof(cp_fifo_write.write_1);
    }

	crs_full_empty: cross cp_fifo_full, cp_fifo_empty {
        illegal_bins unwanted_combination = binsof(cp_fifo_full.is_full) && binsof(cp_fifo_empty.is_empty);
    }

endgroup

covg_fifo covg_fifo_inst = new();

// ------------------------------------------
// ------------------------------------------

property prop_consecutive_write_;
	@(posedge clk) fifo_write[*3];
endproperty

cov_consecutive_writes: cover property(prop_consecutive_write_) $display($stime,,, "\t\t PASS::consecutive_writes condition\n");

// ------------------------------------------
// ------------------------------------------

property prop_non_consecutive_write_;
	@(posedge clk) $fell(rst_) |-> fifo_write[->11:18] ##1 !fifo_write;
endproperty

cov_non_consecutive_writes: assert property(prop_non_consecutive_write_) $display($stime,,, "\t\t PASS::non_consecutive_writes condition\n");


endmodule
