//Base Test
class base_test extends uvm_test;   
    `uvm_component_utils(base_test)
    
    virtual base_intf base_vif;
    base_env base_env0;
    
    uvm_factory my_factory;
    uvm_objection base_test_objection; 

    function new(input string name="BASE_TEST", uvm_component parent=null);
        super.new(name,parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        uvm_config_int::set( this, "*", "recording_detail", 1);
        super.build_phase(phase);
        base_env0 = base_env::type_id::create("base_env0",this);
    endfunction
    
    virtual function void end_of_elaboration_phase(uvm_phase phase);
        `uvm_info(get_full_name(),{"Starting End of Elaboration phase for ",get_type_name()}, UVM_LOW)
        uvm_top.print_topology();
        my_factory = uvm_factory::get();
        my_factory.print();
    endfunction
    
    virtual function void start_of_simulation_phase(uvm_phase phase);
        `uvm_info(get_full_name(),{"Start of simulation phase for ",get_type_name()}, UVM_LOW)
    endfunction
    
    virtual function void check_phase(uvm_phase phase);
      	`uvm_info(get_type_name(),"We are in Check Phase",UVM_LOW);
      	`uvm_info(get_type_name(),"Check Config Usage:",UVM_LOW);
		check_config_usage();
	endfunction
    
    virtual task run_phase(uvm_phase phase);
         base_test_objection = phase.get_objection();
         base_test_objection.set_drain_time(this, 3000);
    endtask
    
endclass : base_test


//////////// RAW Test
class raw_test extends base_test;
    `uvm_component_utils(raw_test)
    
    raw_seq raw_vseq;
    uvm_objection raw_test_objection;
    
    function new(input string name="RAW_TEST", uvm_component parent=null);
        super.new(name,parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        //uvm_config_wrapper::set(this, "base_env0.vseqr.run_phase", "default_sequence", raw_seq::get_type());
        set_type_override_by_type(fifo_virtual_seq::get_type(), raw_seq::get_type());
        super.build_phase(phase);
    endfunction
    
    virtual function void end_of_elaboration_phase(uvm_phase phase);
        super.end_of_elaboration_phase(phase);
    endfunction
    
    virtual function void start_of_simulation_phase(uvm_phase phase);
        super.start_of_simulation_phase(phase);
    endfunction
    
    virtual function void check_phase(uvm_phase phase);
        super.check_phase(phase);
	endfunction
    
    task run_phase(uvm_phase phase);
        `uvm_info(get_full_name(),{"Starting Run phase for ",get_type_name()}, UVM_LOW)
        raw_vseq = raw_seq::type_id::create("vseq");
        if(phase != null) begin
            phase.raise_objection(this, {"Sequence started : ",get_name()});
            raw_vseq.start(base_env0.vseqr);
            #10ns;
            phase.drop_objection(this, {"Sequence ended : ",get_name()} );
            
            raw_test_objection = phase.get_objection();
            //raw_test_objection.set_drain_time(this, 1000);
        end
    endtask
    
endclass : raw_test


///// Single Write and Read Test

class single_write_read_test extends base_test;
    `uvm_component_utils(single_write_read_test)
    
    single_write_read_seq single_wr_red_vseq;
    uvm_objection single_wr_rd_test_objection;
    
  function new(input string name="SINGLE_WRITE_READ_TEST", uvm_component parent=null);
        super.new(name,parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        //uvm_config_wrapper::set(this, "base_env0.vseqr.run_phase", "default_sequence", raw_seq::get_type());
        set_type_override_by_type(fifo_virtual_seq::get_type(), single_write_read_seq::get_type());
        super.build_phase(phase);
    endfunction
    
    virtual function void end_of_elaboration_phase(uvm_phase phase);
        super.end_of_elaboration_phase(phase);
    endfunction
    
    virtual function void start_of_simulation_phase(uvm_phase phase);
        super.start_of_simulation_phase(phase);
    endfunction
    
    virtual function void check_phase(uvm_phase phase);
        super.check_phase(phase);
	endfunction
    
    task run_phase(uvm_phase phase);
        `uvm_info(get_full_name(),{"Starting Run phase for ",get_type_name()}, UVM_LOW)
        single_wr_red_vseq = single_write_read_seq::type_id::create("vseq");
        if(phase != null) begin
            phase.raise_objection(this, {"Sequence started : ",get_name()});
            single_wr_red_vseq.start(base_env0.vseqr);
            #10ns;
            phase.drop_objection(this, {"Sequence ended : ",get_name()} );
            
            single_wr_rd_test_objection = phase.get_objection();
            //raw_test_objection.set_drain_time(this, 1000);
        end
    endtask
    
endclass : single_write_read_test

////////// FIFO FULL
class fifo_full_test extends base_test;
  `uvm_component_utils(fifo_full_test)
    
    fifo_full_seq v_seq;
    uvm_objection fifo_full_objection;
    
  function new(input string name="FIFO_FULL_TEST", uvm_component parent=null);
        super.new(name,parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        //uvm_config_wrapper::set(this, "base_env0.vseqr.run_phase", "default_sequence", raw_seq::get_type());
      set_type_override_by_type(fifo_virtual_seq::get_type(), fifo_full_seq::get_type());
        super.build_phase(phase);
    endfunction
    
    virtual function void end_of_elaboration_phase(uvm_phase phase);
        super.end_of_elaboration_phase(phase);
    endfunction
    
    virtual function void start_of_simulation_phase(uvm_phase phase);
        super.start_of_simulation_phase(phase);
    endfunction
    
    virtual function void check_phase(uvm_phase phase);
        super.check_phase(phase);
	endfunction
    
    task run_phase(uvm_phase phase);
        `uvm_info(get_full_name(),{"Starting Run phase for ",get_type_name()}, UVM_LOW)
      v_seq = fifo_full_seq::type_id::create("v_seq");
        if(phase != null) begin
            phase.raise_objection(this, {"Sequence started : ",get_name()});
            v_seq.start(base_env0.vseqr);
            #10ns;
            phase.drop_objection(this, {"Sequence ended : ",get_name()} );
            
            fifo_full_objection = phase.get_objection();
            //raw_test_objection.set_drain_time(this, 1000);
        end
    endtask
endclass : fifo_full_test

////////   FIFO EMPTY
class fifo_empty_test extends base_test;
  `uvm_component_utils(fifo_empty_test)
    
    fifo_empty_seq vseq;
    uvm_objection fifo_empty_objection;
    
  function new(input string name="FIFO_FULL_TEST", uvm_component parent=null);
        super.new(name,parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        //uvm_config_wrapper::set(this, "base_env0.vseqr.run_phase", "default_sequence", raw_seq::get_type());
      set_type_override_by_type(fifo_virtual_seq::get_type(), fifo_empty_seq::get_type());
        super.build_phase(phase);
    endfunction
    
    virtual function void end_of_elaboration_phase(uvm_phase phase);
        super.end_of_elaboration_phase(phase);
    endfunction
    
    virtual function void start_of_simulation_phase(uvm_phase phase);
        super.start_of_simulation_phase(phase);
    endfunction
    
    virtual function void check_phase(uvm_phase phase);
        super.check_phase(phase);
	endfunction
    
    task run_phase(uvm_phase phase);
        `uvm_info(get_full_name(),{"Starting Run phase for ",get_type_name()}, UVM_LOW)
        vseq = fifo_empty_seq::type_id::create("vseq");
        if(phase != null) begin
            phase.raise_objection(this, {"Sequence started : ",get_name()});
            vseq.start(base_env0.vseqr);
            #10ns;
            phase.drop_objection(this, {"Sequence ended : ",get_name()} );
            
            fifo_empty_objection = phase.get_objection();
            //raw_test_objection.set_drain_time(this, 1000);
        end
    endtask
endclass : fifo_empty_test


////////    RESET MID TEST
class reset_mid_test extends base_test;
  `uvm_component_utils(reset_mid_test)
    
    reset_mid_seq vseq;
    uvm_objection reset_mid_objection;
    
  function new(input string name="RESET_MID_TEST", uvm_component parent=null);
        super.new(name,parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        //uvm_config_wrapper::set(this, "base_env0.vseqr.run_phase", "default_sequence", raw_seq::get_type());
      set_type_override_by_type(fifo_virtual_seq::get_type(), reset_mid_seq::get_type());
        super.build_phase(phase);
    endfunction
    
    virtual function void end_of_elaboration_phase(uvm_phase phase);
        super.end_of_elaboration_phase(phase);
    endfunction
    
    virtual function void start_of_simulation_phase(uvm_phase phase);
        super.start_of_simulation_phase(phase);
    endfunction
    
    virtual function void check_phase(uvm_phase phase);
        super.check_phase(phase);
	endfunction
    
    task run_phase(uvm_phase phase);
        `uvm_info(get_full_name(),{"Starting Run phase for ",get_type_name()}, UVM_LOW)
        vseq = reset_mid_seq::type_id::create("vseq");
        if(phase != null) begin
            phase.raise_objection(this, {"Sequence started : ",get_name()});
            vseq.start(base_env0.vseqr);
            #10ns;
            phase.drop_objection(this, {"Sequence ended : ",get_name()} );
            
            reset_mid_objection = phase.get_objection();
            //raw_test_objection.set_drain_time(this, 1000);
        end
    endtask
endclass : reset_mid_test

///////// UNDERFLOW TEST
class fifo_underflow_test extends base_test;
  `uvm_component_utils(fifo_underflow_test)
    
    fifo_underflow_seq vseq;
    uvm_objection fifo_underflow_objection;
    
  function new(input string name="fifo_underflow_test", uvm_component parent=null);
        super.new(name,parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        //uvm_config_wrapper::set(this, "base_env0.vseqr.run_phase", "default_sequence", raw_seq::get_type());
      set_type_override_by_type(fifo_virtual_seq::get_type(), fifo_underflow_seq::get_type());
        super.build_phase(phase);
    endfunction
    
    virtual function void end_of_elaboration_phase(uvm_phase phase);
        super.end_of_elaboration_phase(phase);
    endfunction
    
    virtual function void start_of_simulation_phase(uvm_phase phase);
        super.start_of_simulation_phase(phase);
    endfunction
    
    virtual function void check_phase(uvm_phase phase);
        super.check_phase(phase);
	endfunction
    
    task run_phase(uvm_phase phase);
        `uvm_info(get_full_name(),{"Starting Run phase for ",get_type_name()}, UVM_LOW)
        vseq = fifo_underflow_seq::type_id::create("vseq");
        if(phase != null) begin
            phase.raise_objection(this, {"Sequence started : ",get_name()});
            vseq.start(base_env0.vseqr);
            #10ns;
            phase.drop_objection(this, {"Sequence ended : ",get_name()} );
            
            fifo_underflow_objection = phase.get_objection();
            //raw_test_objection.set_drain_time(this, 1000);
        end
    endtask
endclass : fifo_underflow_test

///////// UNDERFLOW TEST
class fifo_overflow_test extends base_test;
  `uvm_component_utils(fifo_overflow_test)
    
    fifo_overflow_seq vseq;
    uvm_objection fifo_overflow_objection;
    
  function new(input string name="fifo_underflow_test", uvm_component parent=null);
        super.new(name,parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        //uvm_config_wrapper::set(this, "base_env0.vseqr.run_phase", "default_sequence", raw_seq::get_type());
      set_type_override_by_type(fifo_virtual_seq::get_type(),fifo_overflow_seq::get_type());
        super.build_phase(phase);
    endfunction
    
    virtual function void end_of_elaboration_phase(uvm_phase phase);
        super.end_of_elaboration_phase(phase);
    endfunction
    
    virtual function void start_of_simulation_phase(uvm_phase phase);
        super.start_of_simulation_phase(phase);
    endfunction
    
    virtual function void check_phase(uvm_phase phase);
        super.check_phase(phase);
	endfunction
    
    task run_phase(uvm_phase phase);
        `uvm_info(get_full_name(),{"Starting Run phase for ",get_type_name()}, UVM_LOW)
        vseq = fifo_overflow_seq::type_id::create("vseq");
        if(phase != null) begin
            phase.raise_objection(this, {"Sequence started : ",get_name()});
            vseq.start(base_env0.vseqr);
            #10ns;
            phase.drop_objection(this, {"Sequence ended : ",get_name()} );
            
            fifo_overflow_objection = phase.get_objection();
            //raw_test_objection.set_drain_time(this, 1000);
        end
    endtask
endclass : fifo_overflow_test


/// Equal pointer
class equal_ptr_test extends base_test;
  `uvm_component_utils(equal_ptr_test)
    
    equal_ptr_seq vseq;
    uvm_objection equal_ptr_objection;
    
  function new(input string name="equal_ptr_test", uvm_component parent=null);
        super.new(name,parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        //uvm_config_wrapper::set(this, "base_env0.vseqr.run_phase", "default_sequence", raw_seq::get_type());
      set_type_override_by_type(fifo_virtual_seq::get_type(),fifo_overflow_seq::get_type());
        super.build_phase(phase);
    endfunction
    
    virtual function void end_of_elaboration_phase(uvm_phase phase);
        super.end_of_elaboration_phase(phase);
    endfunction
    
    virtual function void start_of_simulation_phase(uvm_phase phase);
        super.start_of_simulation_phase(phase);
    endfunction
    
    virtual function void check_phase(uvm_phase phase);
        super.check_phase(phase);
	endfunction
    
    task run_phase(uvm_phase phase);
        `uvm_info(get_full_name(),{"Starting Run phase for ",get_type_name()}, UVM_LOW)
        vseq = equal_ptr_seq::type_id::create("vseq");
        if(phase != null) begin
            phase.raise_objection(this, {"Sequence started : ",get_name()});
            vseq.start(base_env0.vseqr);
            #10ns;
            phase.drop_objection(this, {"Sequence ended : ",get_name()} );
            
            equal_ptr_objection = phase.get_objection();
            //raw_test_objection.set_drain_time(this, 1000);
        end
    endtask
endclass : equal_ptr_test

// //Write Test
// class write_test extends base_test;
//     `uvm_component_utils(write_test)
    
//     consecutive_write_seq write_seq;
//     uvm_objection write_test_objection;
    
//     function new(input string name="write_test", uvm_component parent=null);
//         super.new(name,parent);
//     endfunction
    
//     function void build_phase(uvm_phase phase);
//         set_type_override_by_type(base_sequence::get_type(), consecutive_write_seq::get_type());
//         super.build_phase(phase);
//     endfunction
    
//     // End_of_elaboration_phase
//     virtual function void end_of_elaboration_phase(uvm_phase phase);
//         super.end_of_elaboration_phase(phase);
//     endfunction
    
//     virtual function void start_of_simulation_phase(uvm_phase phase);
//         super.start_of_simulation_phase(phase);
//     endfunction
    
//     virtual function void check_phase(uvm_phase phase);
//         super.check_phase(phase);
// 	endfunction
    
//     task run_phase(uvm_phase phase);
//         `uvm_info(get_full_name(),{"Starting Run phase for ",get_type_name()}, UVM_LOW)
//         write_seq = consecutive_write_seq::type_id::create("write_seq");
//         if(phase != null) begin
//             phase.raise_objection(this, {"Sequence started : ",get_name()});
//             write_seq.start(base_env0.base_agt.base_seqr);
//             #10ns;
//             phase.drop_objection(this, {"Sequence ended : ",get_name()} );
            
//             write_test_objection = phase.get_objection();
//             //write_test_objection.set_drain_time(this, 800);
//         end
//     endtask
    
// endclass : write_test

