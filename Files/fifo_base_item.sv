//Base_sequence_item
import uvm_pkg::*;
`include "uvm_macros.svh"

class base_seq_item extends uvm_sequence_item;
          
          logic                    rst_n;
      rand logic [DATA_WIDTH - 1:0] data_in;
      rand logic                    wr;
      rand logic                    rd;
          logic                    fifo_full;
          logic                    fifo_empty;
          logic                    fifo_threshold;
          logic                    fifo_overflow;
            logic                    fifo_underflow;
            logic [DATA_WIDTH - 1:0] data_out;
    
    `uvm_object_utils_begin(base_seq_item)
         `uvm_field_int(data_in,UVM_ALL_ON)
         `uvm_field_int(wr,UVM_ALL_ON)
         `uvm_field_int(rd,UVM_ALL_ON)
         `uvm_field_int(data_out,UVM_ALL_ON)
         `uvm_field_int(fifo_full,UVM_ALL_ON)
         `uvm_field_int(fifo_empty,UVM_ALL_ON)
         `uvm_field_int(fifo_threshold,UVM_ALL_ON)
         `uvm_field_int(fifo_overflow,UVM_ALL_ON)
         `uvm_field_int(fifo_underflow,UVM_ALL_ON)
    `uvm_object_utils_end

    function new(input string name="FIFO_SEQUENCE_ITEM");
       super.new(name);
    endfunction
            
  constraint data_in_range {data_in inside {[0:255]};}
  constraint data_out_range {data_out inside {[0:255]};}
  constraint wr_c {wr inside {[0:1]};}
  constraint rd_c {rd inside {[0:1]};}
  constraint wr_addr { wr_ptr inside {[0:MEM_SIZE]};}
  constraint rd_addr { rd_ptr inside {[0:MEM_SIZE]};}

endclass : base_seq_item