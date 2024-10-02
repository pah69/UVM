import uvm_pkg::*;
`include "uvm_macros.svh"

//Base sequence class
class base_sequence extends uvm_sequence#(base_seq_item);

    `uvm_object_utils(base_sequence)

    function new(input string name="BASE_SEQUENCE");
        super.new(name);
    endfunction 
endclass : base_sequence

// *************************** WRITE *****************************
////////////////////   Consecutive Write Sequence
class consecutive_write_seq extends base_sequence;

    `uvm_object_utils(consecutive_write_seq)

    function new(input string name="CONS_WRITE_SEQUENCE");
        super.new(name);
    endfunction

    task body();
      repeat(MEM_SIZE) begin
          `uvm_do_with(req, {wr == 1; rd == 0;});
        end
    endtask : body 
      
endclass : consecutive_write_seq


///////////////////// Single Write sequence
class single_write_seq extends base_sequence;

  `uvm_object_utils(single_write_seq)

  function new(input string name="SINGLE_WRITE_SEQ");
        super.new(name);
    endfunction

    task body();
         `uvm_do_with(req, {wr == 1; rd == 0;});
    endtask : body 
      
endclass : single_write_seq

///////////////////// HALF WRITE
class half_write_seq extends base_sequence;

  `uvm_object_utils(half_write_seq)

  function new(input string name="HALF_WRITE_SEQUENCE");
        super.new(name);
    endfunction

    task body();
      repeat(MEM_SIZE/2) begin
          `uvm_do_with(req, {wr == 1; rd == 0;});
        end
    endtask : body 
      
endclass : half_write_seq

// ********************** READ *******************
//////////////// Consecutive read Sequence
class consecutive_read_seq extends base_sequence;

    `uvm_object_utils(consecutive_read_seq)

    function new(input string name="CONS_READ_SEQUENCE");
        super.new(name);
    endfunction

    task body();
      repeat(MEM_SIZE) begin
        `uvm_do_with(req, {rd == 1; wr == 0; data_in == 0;});
        end
    endtask : body 
      
endclass : consecutive_read_seq


//////////////// Single read Sequence
class single_read_seq extends base_sequence;

    `uvm_object_utils(single_read_seq)

    function new(input string name="SINGLE_READ_SEQUENCE");
        super.new(name);
    endfunction

    task body();
       `uvm_do_with(req, {rd == 1; wr == 0; data_in == 0;});
    endtask : body 
      
endclass : single_read_seq

//// HALF READ
class half_read_seq extends base_sequence;

  `uvm_object_utils(half_read_seq)

  function new(input string name="HALF_READ_SEQUENCE");
        super.new(name);
    endfunction

    task body();
      repeat(MEM_SIZE/2) begin
        `uvm_do_with(req, {rd == 1; wr == 0; data_in == 0;});
        end
    endtask : body 
      
endclass : half_read_seq


//// //////////// NONE AND BOTH

///////////////// No_read_write sequence
class no_read_write_seq extends base_sequence;

  `uvm_object_utils(no_read_write_seq)

  function new(input string name="NO_READ_WRITE_SEQ");
        super.new(name);
    endfunction

    task body();
      `uvm_do_with(req, {wr == 0; rd == 0;data_in == 0;});
    endtask : body 
      
endclass : no_read_write_seq


/////////////// Both read_write sequence


class both_read_write_seq extends base_sequence;
  `uvm_object_utils(both_read_write_seq)
  
  function new(input string name = "BOTH_READ_WRITE_SEQ");
    super.new(name);
  endfunction
  
  task body();
    `uvm_do_with(req, {wr == 1; rd == 1;});
  endtask
  
endclass : both_read_write_seq

// ***********  RESET **************
class reset_seq extends base_sequence;

  `uvm_object_utils(reset_seq)
  function new(input string name="RESET_SEQUENCE");
        super.new(name);
    endfunction

    task body();    
		`uvm_do_with(req, {rst_n == 0;});
   #20ns;
    endtask : body 
endclass : reset_seq
