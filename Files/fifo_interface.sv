//Interface

interface base_intf #(parameter DATA_WIDTH = 8)(input bit clk, rst_n);
   import uvm_pkg::*; 
  `include  "uvm_macros.svh" 
    
    logic [DATA_WIDTH-1:0]  data_in;
    logic                   wr;
    logic                   rd;
    logic [DATA_WIDTH-1:0]  data_out;    
    logic                   fifo_full;
    logic                   fifo_empty;
    logic                   fifo_threshold;
    logic                   fifo_overflow;
    logic                   fifo_underflow;
    logic [4:0]             wr_ptr;
    logic [4:0]             rd_ptr;
    
    
  property within_prop;
    @(posedge clk)
     wr_ptr == 1 |=> wr_ptr == 3;
  endproperty 
  
//   ap_test : assert property (within_prop) else
//     `uvm_error("MYERR", "This is an error")
    

    
endinterface : base_intf