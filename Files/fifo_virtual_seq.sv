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


// Read after Write Sequence
class raw_seq extends fifo_virtual_seq;

    `uvm_object_utils(raw_seq)
   
    consecutive_write_seq c_write_seq;
    consecutive_read_seq c_read_seq;
    single_write_seq s_write_seq;
    no_read_write_seq no_rw_seq;
    
    function new(input string name="RAW_SEQUENCE");
        super.new(name);
    endfunction
    
    virtual task body();
        #70ns; // Wait for rst_n
       `uvm_info(get_full_name(),{"Sequence started : ",get_type_name()},UVM_LOW)
       `uvm_do_on(c_write_seq, p_sequencer.base_seqr);
      
       `uvm_info(get_full_name(),{"First seq ",get_type_name()},UVM_LOW)
      `uvm_do_on(s_write_seq, p_sequencer.base_seqr);
     // `uvm_do_on(no_rw_seq, p_sequencer.base_seqr);
       `uvm_info(get_full_name(),{"Sec seq ",get_type_name()},UVM_LOW)
      `uvm_do_on(c_read_seq, p_sequencer.base_seqr1);
      
       `uvm_info(get_full_name(),{"Third seq ",get_type_name()},UVM_LOW)
       `uvm_do_on(no_rw_seq, p_sequencer.base_seqr);
        #30ns; // Wait for sequence ended
       `uvm_info(get_full_name(),{"Sequence ended : ",get_type_name()},UVM_LOW)
    endtask

endclass : raw_seq


