// Code your testbench here
// or browse Examples
`timescale 1ns / 1ps

// Fifo Interface
`include "fifo_interface.sv"
// Fifo test lib
`include "fifo_files_inc.sv"

module fifo_tb_top;
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  
  import fifo_pkg::*;
  
  bit clk, rst_n;
  base_intf #(.DATA_WIDTH(DATA_WIDTH)) vif(clk, rst_n);
  
  fifo_mem #(.DATA_WIDTH(DATA_WIDTH), .MEM_SIZE(MEM_SIZE)) DUT_inst (
    .clk           (vif.clk),
    .rst_n         (vif.rst_n),
    .wr            (vif.wr),
    .rd            (vif.rd),
    .data_in       (vif.data_in),
    .data_out      (vif.data_out),
    .fifo_full     (vif.fifo_full),
    .fifo_empty    (vif.fifo_empty),
    .fifo_overflow (vif.fifo_overflow),
    .fifo_underflow(vif.fifo_underflow),
    .fifo_threshold(vif.fifo_threshold)
  );
  assign vif.wr_ptr = fifo_tb_top.DUT_inst.top1.wptr;
  assign vif.rd_ptr = fifo_tb_top.DUT_inst.top2.rptr;

  initial begin
     clk = 1'b1;
     reset_fifo();
  end 
 
  initial forever #10 clk = ~clk;
  
 
  
  task reset_fifo();
    $display("Time = %0t --- Resetting the FIFO !!", $time);
     rst_n = 'b0;
     #65ns;
     rst_n = 'b1;
    $display("Time = %0t --- FIFO is out of Reset !!", $time);
  endtask : reset_fifo
  
  initial begin
    uvm_config_db#(virtual base_intf)::set(uvm_root::get(),"*","base_intf",vif);
    reset_fifo();
      run_test("write_test");
    //  run_test("raw_test");
    // run_test(" ");
      reset_fifo();
  end


  initial begin
      $dumpfile("sync_fifo_dump.vcd");
      $dumpvars(0,DUT_inst);
   end
  
endmodule : fifo_tb_top
