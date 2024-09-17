//Interface

interface base_intf #(parameter DATA_WIDTH = 8,MEM_SIZE = 16)(input bit clk);
  import uvm_pkg::*; 
 `include  "uvm_macros.svh" 
    logic 					rst_n;
   logic [DATA_WIDTH-1:0]  data_in;
   logic                   wr;
   logic                   rd;
   logic [DATA_WIDTH-1:0]  data_out;    
   logic                   fifo_full;
   logic                   fifo_empty;
   logic                   fifo_threshold;
   logic                   fifo_overflow;
   logic                   fifo_underflow;
   logic [4:0]               wptr;
   logic [4:0]             rptr;
   logic fifo_we;
   logic fifo_rd;
   
 property within_prop;
   @(posedge clk)
   wptr == 1 |=> wptr == 3;
 endproperty 
 
 property full_check;
   @(posedge clk) disable iff(!rst_n)
   (fifo_full) && (wr) |-> (fifo_we == 0 ##1 $stable(wptr));
 endproperty
 
 property empty_check;
   @(posedge clk) disable iff(!rst_n)
   (fifo_empty) && (rd) |=> (!fifo_rd) && $stable(rptr);
 endproperty
 
 property full_empty_onehot;
   @(posedge clk) disable iff(!rst_n)
   1'b1 |-> !(fifo_full & fifo_empty);
 endproperty
 
 property pre_full_check;
   @(posedge clk) disable iff(!rst_n)
   $rose(fifo_full) |-> $past(fifo_we);
 endproperty
 
 property pre_empty_check;
   @(posedge clk) disable iff(!rst_n)
   $rose(fifo_empty) |-> $past(fifo_rd);
 endproperty
 
 property post_write_check;
   @(posedge clk) disable iff(!rst_n)
   (fifo_empty) && (wr)  |=> $fell(fifo_empty);
 endproperty
 
 property post_read_check;
   @(posedge clk) disable iff(!rst_n)
   (fifo_full) && (rd) |=> $fell(fifo_full);
 endproperty
 
 property read_write_equal;
    @(negedge clk) disable iff (!rst_n)
    (rd)&&(wr) && !(wptr-rptr) |=>  $stable(fifo_full) && $stable(fifo_empty);    
 endproperty 
 
 property consecutive_write_check;
   @(posedge clk) disable iff (!rst_n)
   ((!fifo_rd) && (fifo_we))[*MEM_SIZE] |=> (fifo_full);
 endproperty
 
 property reset_check;
   @(posedge clk) disable iff(rst_n)
   !rst_n |=> (wptr == 1'b0) && (rptr == 1'b0);
 endproperty

 
 //////////// FIFO output check
 property empty_rw_check;
   @(posedge clk) disable iff(!rst_n)
   (fifo_empty) && (wr) && (rd) |=> $stable(rptr) && $fell(fifo_empty) && (wptr == $past(wptr) + 1);
 endproperty
 
 property full_rw_check;
   @(posedge clk) disable iff(!rst_n)
   (fifo_full) && (wr) && (rd) |=> $stable(wptr) && $fell(fifo_full) && (rptr == $past(rptr) + 1);
 endproperty
 
 property overflow_check;
   @(posedge clk) disable iff(!rst_n)
   (fifo_full) && (wr) && (!rd) |=> (fifo_overflow);
 endproperty
 
 property underflow_check;
   @(posedge clk) disable iff(!rst_n)
   (fifo_empty) && (rd) && (!wr) |=> (fifo_underflow);
 endproperty
 
 property post_overflow_check;
   @(posedge clk) disable iff(!rst_n)
   (fifo_full) && (fifo_overflow) && (rd) |=> ($fell(fifo_overflow)) && ($fell(fifo_full));
 endproperty
 
  property post_underflow_check;
   @(posedge clk) disable iff(!rst_n)
    (fifo_empty) && (fifo_underflow) && (wr) |=> ($fell(fifo_underflow)) && ($fell(fifo_empty));
 endproperty
 
 property write_check;
   @(posedge clk) disable iff(!rst_n)
   (!fifo_full) && (wr) |-> (fifo_we) ##1 (wptr == $past(wptr) + 1);
 endproperty
 
 property read_check;
   @(posedge clk) disable iff(!rst_n)
   (!fifo_empty) && (rd) |-> (fifo_rd) ##1 (rptr == $past(rptr) + 1);
 endproperty
 
 property threshhold_check;
   @(posedge clk) disable iff(!rst_n)
   ((wptr - rptr) >= 'h8) |-> (fifo_threshold);
 endproperty
 //// ASSERT PORPERTY
RESET_CHECK: assert property (reset_check) 
   `uvm_info("ASSERTION", "PASS RESET_CHECK", UVM_LOW)
   else `uvm_error("ASSERTION", "FAIL RESET_CHECK") 
 FULL_CHECK: assert property (full_check)
   `uvm_info("ASSERTION", "PASS FULL_CHECK", UVM_LOW)
   else `uvm_error("ASSERTION", "FAIL FULL_CHECK") 
 EMPTY_CHECK: assert property (empty_check) 
   `uvm_info("ASSERTION", "PASS EMPTY_CHECK", UVM_LOW)
   else `uvm_error("ASSERTION", "FAIL EMPTY_CHECK") 
 FULL_EMPTY_ONEHOT: assert property (full_empty_onehot)
   `uvm_info("ASSERTION", "PASS FULL_EMPTY_ONEHOT_CHECK", UVM_LOW)
   else `uvm_error("ASSERTION", "FAIL FULL_EMPTY_ONEHOT_CHECK") 
 PRE_FULL_CHECK: assert property (pre_full_check) 
   `uvm_info("ASSERTION", "PASS PRE_FULL_CHECK", UVM_LOW)
   else `uvm_error("ASSERTION", "FAIL PRE_FULL_CHECK") 
 PRE_EMPTY_CHECK: assert property (pre_empty_check) 
   `uvm_info("ASSERTION", "PASS PRE_EMPTY_CHECK", UVM_LOW)
   else `uvm_error("ASSERTION", "FAIL PRE_EMPTY_CHECK") 
 POST_WRITE_CHECK: assert property (post_write_check) 
   `uvm_info("ASSERTION", "PASS POST_WRITE_CHECK", UVM_LOW)
   else `uvm_error("ASSERTION", "FAIL POST_WRITE_CHECK") 
 POST_READ_CHECK: assert property (post_read_check) 
   `uvm_info("ASSERTION", "PASS POST_READ_CHECK", UVM_LOW)
   else `uvm_error("ASSERTION", "FAIL POST_READ_CHECK") 
 READ_WRITE_EQUAL: assert property (read_write_equal) 
   `uvm_info("ASSERTION", "PASS READ_WRITE_EQUAL_CHECK", UVM_LOW)
   else `uvm_error("ASSERTION", "FAIL READ_WRITE_EQUAL_CHECK") 
 CONSECUTIVE_WRITE_CHECK: assert property (consecutive_write_check) 
   `uvm_info("ASSERTION", "PASS CONSECUTIVE_WRITE_CHECK", UVM_LOW)
   else `uvm_error("ASSERTION", "FAIL CONSECUTIVE_WRITE_CHECK") 
   

     ///// ASSERT OUTPUT PROPERTY
EMPTY_RW_CHECK: assert property (empty_rw_check) 
   `uvm_info("ASSERTION", "PASS EMPTY_RW_CHECK", UVM_LOW)
   else `uvm_error("ASSERTION", "FAIL EMPTY_RW_CHECK") 
 FULL_RW_CHECK: assert property (full_rw_check) 
   `uvm_info("ASSERTION", "PASS FULL_RW_CHECK", UVM_LOW)
   else `uvm_error("ASSERTION", "FAIL FULL_RW_CHECK") 
 OVERFLOW_CHECK: assert property (overflow_check) 
   `uvm_info("ASSERTION", "PASS OVERFLOW_CHECK", UVM_LOW)
   else `uvm_error("ASSERTION", "FAIL OVERFLOW_CHECK") 
 UNDERFLOW_CHECK: assert property (underflow_check) 
   `uvm_info("ASSERTION", "PASS UNDERFLOW_CHECK", UVM_LOW)
   else `uvm_error("ASSERTION", "FAIL UNDERFLOW_CHECK") 
 POST_OVERFLOW_CHECK: assert property (post_overflow_check) 
   `uvm_info("ASSERTION", "PASS POST_OVERFLOW_CHECK", UVM_LOW)
   else `uvm_error("ASSERTION", "FAIL POST_OVERFLOW_CHECK") 
 POST_UNDERFLOW_CHECK: assert property (post_underflow_check) 
   `uvm_info("ASSERTION", "PASS UNDERFLOW_CHECK", UVM_LOW)
   else `uvm_error("ASSERTION", "FAIL UNDERFLOW_CHECK") 
 WRITE_CHECK: assert property (write_check) 
   `uvm_info("ASSERTION", "PASS WRITE_CHECK", UVM_LOW)
   else `uvm_error("ASSERTION", "FAIL WRITE_CHECK") 
 READ_CHECK: assert property (read_check) 
   `uvm_info("ASSERTION", "PASS READ_CHECK", UVM_LOW)
   else `uvm_error("ASSERTION", "FAIL READ_CHECK") 
 THRESHOLD_CHECK: assert property (threshhold_check) 
   `uvm_info("ASSERTION", "PASS THRESHOLD_CHECK", UVM_LOW)
   else `uvm_error("ASSERTION", "FAIL THRESHOLD_CHECK") 
   
endinterface : base_intf