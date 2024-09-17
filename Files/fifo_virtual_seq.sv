// Virtual Sequence
class fifo_virtual_seq extends uvm_sequence#(uvm_sequence_item);

    `uvm_object_utils(fifo_virtual_seq)
    `uvm_declare_p_sequencer(fifo_virtual_sequencer)

    function new(input string name="FIFO_VIRTUAL_SEQUENCE");
        super.new(name);
    endfunction
    
    virtual task pre_body();
        uvm_phase phase;
        phase = starting_phase;
        if(phase != null) begin
            phase.raise_objection(this,{"Virtual sequence started : ",get_type_name()});
        end
    endtask
    
    virtual task post_body();
        uvm_phase phase;
        phase = starting_phase;
        if(phase != null) begin
            phase.drop_objection(this,{"Virtual sequence ended : ",get_type_name()});
        end
    endtask
    
endclass : fifo_virtual_seq

// // Single Write then Single Read

// class single_write_read_seq extends fifo_virtual_seq;
//   `uvm_object_utils(single_write_read_seq)
//       reset_seq rst_seq;
//       both_read_write_seq both_seq;
//       single_write_seq s_write_seq;
//       single_read_seq s_read_seq;
//       no_read_write_seq no_rw_seq;
  
//   function new(input string name="SINGLE_WR_RD_SEQUENCE");
//         super.new(name);
//     endfunction
  
//   virtual task body();
//       `uvm_info(get_full_name(),{"RESET Sequence! " ,get_type_name()},UVM_LOW)
//       `uvm_do_on(rst_seq, p_sequencer.base_seqr);
// //       `uvm_do_on(rst_seq, p_sequencer.base_seqr1);

//       `uvm_info(get_full_name(),{"Both Write and Read Sequence! " ,get_type_name()},UVM_LOW)
//       `uvm_do_on(both_seq, p_sequencer.base_seqr);
//       `uvm_do_on(both_seq, p_sequencer.base_seqr1);

//       `uvm_info(get_full_name(),{"S_Write start! " ,get_type_name()},UVM_LOW)
//       `uvm_do_on(s_write_seq, p_sequencer.base_seqr);

//       `uvm_info(get_full_name(),{"S_Read start! " ,get_type_name()},UVM_LOW)
//       `uvm_do_on(s_read_seq, p_sequencer.base_seqr1);

//       `uvm_info(get_full_name(),{"NO_RW start! " ,get_type_name()},UVM_LOW)
//       `uvm_do_on(no_rw_seq, p_sequencer.base_seqr);

//   endtask
  
// endclass: single_write_read_seq

// Read after Write Sequence
class raw_seq extends fifo_virtual_seq;
	
    `uvm_object_utils(raw_seq)
    reset_seq rst_seq;
    consecutive_write_seq c_write_seq;
    consecutive_read_seq c_read_seq;
    single_write_seq s_write_seq;
  	single_read_seq s_read_seq;
	half_write_seq h_write_seq;
  	half_read_seq h_read_seq;    
  	no_read_write_seq no_rw_seq;
   // both_read_write_seq both_rw_seq;
    function new(input string name="RAW_SEQUENCE");
        super.new(name);
    endfunction
    
    virtual task body();
      
      `uvm_do_on(rst_seq, p_sequencer.base_seqr); /// RESET
      `uvm_do_on(no_rw_seq, p_sequencer.base_seqr);	// Delay 1 cycle
      
      // Consecutive Write
      `uvm_info(get_full_name(),{"C_Write started : ",get_type_name()},UVM_LOW)
      `uvm_do_on(c_write_seq, p_sequencer.base_seqr);
      
      // Consective Read
 	  `uvm_info(get_full_name(),{"C_Read started ",get_type_name()},UVM_LOW)
      `uvm_do_on(c_read_seq, p_sequencer.base_seqr1);            
      
      


      
      
      
      
//         `uvm_info(get_full_name(),{"RESET Sequence! " ,get_type_name()},UVM_LOW)
//         `uvm_do_on(rst_seq, p_sequencer.base_seqr);

//         `uvm_info(get_full_name(),{"C_Write started : ",get_type_name()},UVM_LOW)
//          `uvm_do_on(c_write_seq, p_sequencer.base_seqr);

//         `uvm_info(get_full_name(),{"S_Write started ",get_type_name()},UVM_LOW)
//         `uvm_do_on(s_write_seq, p_sequencer.base_seqr);

//         `uvm_do_on(no_rw_seq, p_sequencer.base_seqr);
//         `uvm_info(get_full_name(),{"NO_RW finished ",get_type_name()},UVM_LOW)

//         `uvm_info(get_full_name(),{"C_Read started ",get_type_name()},UVM_LOW)
//         `uvm_do_on(c_read_seq, p_sequencer.base_seqr1);

//          `uvm_do_on(no_rw_seq, p_sequencer.base_seqr);
//           #30ns; // Wait for sequence ended
//          `uvm_info(get_full_name(),{"Sequence ended : ",get_type_name()},UVM_LOW)
      endtask

endclass : raw_seq


/// FIFO FULL
class fifo_full_seq extends fifo_virtual_seq;

    `uvm_object_utils(fifo_full_seq)
   
  	reset_seq rst_seq;
  	both_read_write_seq both_seq;
    consecutive_write_seq c_write_seq;
    single_write_seq      s_write_seq;
  	single_read_seq       s_read_seq;
    no_read_write_seq     no_rw_seq;
    
    function new(input string name="FIFO_FULL_SEQUENCE");
        super.new(name);
    endfunction
    
    virtual task body();
      `uvm_info(get_full_name(),{"Reset started : ",get_type_name()},UVM_LOW)
      `uvm_do_on(rst_seq, p_sequencer.base_seqr);
      
      `uvm_info(get_full_name(),{"Sequence started : ",get_type_name()},UVM_LOW)
      `uvm_do_on(c_write_seq, p_sequencer.base_seqr);
      
      `uvm_info(get_full_name(),{"First seq : ",get_type_name()},UVM_LOW)
      `uvm_do_on(s_read_seq, p_sequencer.base_seqr1);
      
      `uvm_info(get_full_name(),{"Sec seq ",get_type_name()},UVM_LOW)
      `uvm_do_on(no_rw_seq, p_sequencer.base_seqr);
      
      `uvm_info(get_full_name(),{"Third seq ",get_type_name()},UVM_LOW)
      `uvm_do_on(s_write_seq, p_sequencer.base_seqr);
      
//       `uvm_info(get_full_name(),{"Fourth seq ",get_type_name()},UVM_LOW)
//       `uvm_do_on(both_seq, p_sequencer.base_seqr );      
       #30ns; // Wait for sequence ended
      `uvm_info(get_full_name(),{"Sequence ended : ",get_type_name()},UVM_LOW)
    endtask

endclass : fifo_full_seq


// FIFO EMPTY
class fifo_empty_seq extends fifo_virtual_seq;
  `uvm_object_utils(fifo_empty_seq)
  reset_seq rst_seq;
  both_read_write_seq both_seq;
  single_write_seq      s_write_seq;
  single_read_seq       s_read_seq;
  consecutive_write_seq c_write_seq;
  consecutive_read_seq c_read_seq;
  no_read_write_seq     no_rw_seq;

  function new(input string name="FIFO_EMPTY_SEQUENCE");
        super.new(name);
    endfunction
  
    virtual task body();
      `uvm_info(get_full_name(),{"Reset started : ",get_type_name()},UVM_LOW)
      `uvm_do_on(rst_seq, p_sequencer.base_seqr);
      
      `uvm_info(get_full_name(),{"Sequence started : ",get_type_name()},UVM_LOW)
      `uvm_do_on(c_write_seq, p_sequencer.base_seqr);
      
      `uvm_info(get_full_name(),{"First seq : ",get_type_name()},UVM_LOW)
      `uvm_do_on(c_read_seq, p_sequencer.base_seqr1);
      
      `uvm_info(get_full_name(),{"Sec seq ",get_type_name()},UVM_LOW)
      `uvm_do_on(no_rw_seq, p_sequencer.base_seqr);
      
    `uvm_info(get_full_name(),{"Reset started : ",get_type_name()},UVM_LOW)
      `uvm_do_on(rst_seq, p_sequencer.base_seqr);
      
      `uvm_info(get_full_name(),{"Fourth seq ",get_type_name()},UVM_LOW)
      `uvm_do_on(both_seq, p_sequencer.base_seqr );
      
      `uvm_info(get_full_name(),{"Sequence started : ",get_type_name()},UVM_LOW)
      `uvm_do_on(c_write_seq, p_sequencer.base_seqr);
      
      `uvm_info(get_full_name(),{"First seq : ",get_type_name()},UVM_LOW)
      `uvm_do_on(c_read_seq, p_sequencer.base_seqr1);
       #30ns; // Wait for sequence ended
      `uvm_info(get_full_name(),{"Sequence ended : ",get_type_name()},UVM_LOW)
    endtask

endclass : fifo_empty_seq


////// Reset in the middle
class reset_mid_seq extends fifo_virtual_seq;
  `uvm_object_utils(reset_mid_seq)
  reset_seq rst_seq;
  both_read_write_seq both_seq;
  single_write_seq      s_write_seq;
  single_read_seq       s_read_seq;
  consecutive_write_seq c_write_seq;
  consecutive_read_seq c_read_seq;
  no_read_write_seq     no_rw_seq;
  half_write_seq h_write_seq;
  half_read_seq h_read_seq;

  function new(input string name= "RESET_MID_SEQUENCE");
        super.new(name);
    endfunction
  
    virtual task body();
      `uvm_info(get_full_name(),{"1ST Reset started : ",get_type_name()},UVM_LOW)
      `uvm_do_on(rst_seq, p_sequencer.base_seqr);
      
      `uvm_info(get_full_name(),{"Consecutive Write Started : ",get_type_name()},UVM_LOW)
      `uvm_do_on(c_write_seq, p_sequencer.base_seqr);
      
      `uvm_info(get_full_name(),{"Reset After Consecutive Write : ",get_type_name()},UVM_LOW)
      `uvm_do_on(rst_seq, p_sequencer.base_seqr);
      
      `uvm_info(get_full_name(),{"HALF WRITE started : ",get_type_name()},UVM_LOW)
      `uvm_do_on(h_write_seq, p_sequencer.base_seqr);
      
      `uvm_info(get_full_name(),{"Reset After Half Write : ",get_type_name()},UVM_LOW)
      `uvm_do_on(rst_seq, p_sequencer.base_seqr);
      
      `uvm_info(get_full_name(),{"Single Write started : ",get_type_name()},UVM_LOW)
      `uvm_do_on(s_write_seq, p_sequencer.base_seqr);
      
      `uvm_info(get_full_name(),{"Reset After Single Write : ",get_type_name()},UVM_LOW)
      `uvm_do_on(rst_seq, p_sequencer.base_seqr);
       #30ns; // Wait for sequence ended
      
      `uvm_info(get_full_name(),{"Sequence ended : ",get_type_name()},UVM_LOW)
    endtask

endclass : reset_mid_seq

//////////////// UNDERFLOW
class fifo_underflow_seq extends fifo_virtual_seq;
  `uvm_object_utils(fifo_underflow_seq)
  reset_seq rst_seq;
  both_read_write_seq both_seq;
  single_write_seq      s_write_seq;
  single_read_seq       s_read_seq;
  consecutive_write_seq c_write_seq;
  consecutive_read_seq c_read_seq;
  no_read_write_seq     no_rw_seq;
  half_write_seq h_write_seq;
  half_read_seq h_read_seq;

  function new(input string name= "fifo_underflow_SEQUENCE");
        super.new(name);
    endfunction
  
    virtual task body();
      `uvm_info(get_full_name(),{"1ST Reset started : ",get_type_name()},UVM_LOW)
      `uvm_do_on(rst_seq, p_sequencer.base_seqr);
      
      `uvm_info(get_full_name(),{"Consecutive Write Started : ",get_type_name()},UVM_LOW)
      `uvm_do_on(c_write_seq, p_sequencer.base_seqr);
      `uvm_do_on(c_read_seq, p_sequencer.base_seqr1);
      
      
      `uvm_info(get_full_name(),{"Reset After Consecutive Write : ",get_type_name()},UVM_LOW)
      `uvm_do_on(rst_seq, p_sequencer.base_seqr);
      
      `uvm_info(get_full_name(),{"HALF WRITE started : ",get_type_name()},UVM_LOW)
      `uvm_do_on(h_write_seq, p_sequencer.base_seqr);
      `uvm_do_on(h_read_seq, p_sequencer.base_seqr1);
      
      `uvm_info(get_full_name(),{"Reset After Half Write : ",get_type_name()},UVM_LOW)
      `uvm_do_on(rst_seq, p_sequencer.base_seqr);
      
      `uvm_info(get_full_name(),{"Single Write started : ",get_type_name()},UVM_LOW)
      `uvm_do_on(s_write_seq, p_sequencer.base_seqr);
      `uvm_do_on(s_read_seq, p_sequencer.base_seqr1);

      `uvm_info(get_full_name(),{"Reset After Single Write : ",get_type_name()},UVM_LOW)
      `uvm_do_on(rst_seq, p_sequencer.base_seqr);
       #30ns; // Wait for sequence ended
      
      `uvm_info(get_full_name(),{"Sequence ended : ",get_type_name()},UVM_LOW)
    endtask

endclass : fifo_underflow_seq

//////////////// OVERFLOW
class fifo_overflow_seq extends fifo_virtual_seq;
  `uvm_object_utils(fifo_overflow_seq)
  reset_seq rst_seq;
  both_read_write_seq both_seq;
  single_write_seq      s_write_seq;
  single_read_seq       s_read_seq;
  consecutive_write_seq c_write_seq;
  consecutive_read_seq c_read_seq;
  no_read_write_seq     no_rw_seq;
  half_write_seq h_write_seq;
  half_read_seq h_read_seq;

  function new(input string name= "fifo_underflow_SEQUENCE");
        super.new(name);
    endfunction
  
    virtual task body();
      `uvm_info(get_full_name(),{"1ST Reset started : ",get_type_name()},UVM_LOW)
      `uvm_do_on(rst_seq, p_sequencer.base_seqr);
      
      `uvm_info(get_full_name(),{"Consecutive Write Started : ",get_type_name()},UVM_LOW)
      `uvm_do_on(c_write_seq, p_sequencer.base_seqr);
      `uvm_do_on(s_write_seq, p_sequencer.base_seqr);
      `uvm_do_on(rst_seq, p_sequencer.base_seqr);
      
      `uvm_do_on(c_read_seq, p_sequencer.base_seqr);
      
      
      `uvm_info(get_full_name(),{"Reset After Consecutive Write : ",get_type_name()},UVM_LOW)
      `uvm_do_on(rst_seq, p_sequencer.base_seqr);
      
      `uvm_info(get_full_name(),{"HALF WRITE started : ",get_type_name()},UVM_LOW)
      `uvm_do_on(h_write_seq, p_sequencer.base_seqr);
      `uvm_do_on(h_read_seq, p_sequencer.base_seqr1);
      
      `uvm_info(get_full_name(),{"Reset After Half Write : ",get_type_name()},UVM_LOW)
      `uvm_do_on(rst_seq, p_sequencer.base_seqr);
      
      `uvm_info(get_full_name(),{"Single Write started : ",get_type_name()},UVM_LOW)
      `uvm_do_on(s_write_seq, p_sequencer.base_seqr);
      `uvm_do_on(s_read_seq, p_sequencer.base_seqr1);

      `uvm_info(get_full_name(),{"Reset After Single Write : ",get_type_name()},UVM_LOW)
      `uvm_do_on(rst_seq, p_sequencer.base_seqr);
       #30ns; // Wait for sequence ended
      
      `uvm_info(get_full_name(),{"Sequence ended : ",get_type_name()},UVM_LOW)
    endtask

endclass : fifo_overflow_seq

//----------------Equal ptr-----------
class equal_ptr_seq extends fifo_virtual_seq;

  `uvm_object_utils(equal_ptr_seq)
  
 	reset_seq rst_seq;
 	both_read_write_seq both_seq;
    single_write_seq  s_write_seq;
  	single_read_seq   s_read_seq;
    no_read_write_seq no_rw_seq;
    
  function new(input string name="EQUAL_PTR_SEQUENCE");
        super.new(name);
    endfunction
    
    virtual task body();
      `uvm_info(get_full_name(),{"Reset started : ",get_type_name()},UVM_LOW)
      `uvm_do_on(rst_seq, p_sequencer.base_seqr);
      
      `uvm_info(get_full_name(),{"Sequence started : ",get_type_name()},UVM_LOW)
      `uvm_do_on(s_write_seq, p_sequencer.base_seqr);
      
      `uvm_info(get_full_name(),{"First seq : ",get_type_name()},UVM_LOW)
      `uvm_do_on(s_read_seq, p_sequencer.base_seqr1);
      
      `uvm_info(get_full_name(),{"Sec seq ",get_type_name()},UVM_LOW)
      `uvm_do_on(no_rw_seq, p_sequencer.base_seqr);
      
       #30ns; // Wait for sequence ended
      `uvm_info(get_full_name(),{"Sequence ended : ",get_type_name()},UVM_LOW)
    endtask

endclass : equal_ptr_seq
