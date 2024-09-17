//Base Environment
class base_env extends uvm_env;

    `uvm_component_utils(base_env)
    
    fifo_virtual_sequencer vseqr;
    base_agent base_agt;
    base_agent1 base_agt1;
    fifo_scoreboard fifo_sb;
    virtual base_intf base_vif;
    
    function new(input string name="BASE_ENV", uvm_component parent=null);
        super.new(name,parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        `uvm_info(get_full_name(),{"Starting Build phase for ",get_type_name()}, UVM_LOW)
        super.build_phase(phase);
        if(!uvm_config_db#(virtual base_intf)::get(this,"","base_intf",base_vif))
            `uvm_fatal(get_type_name(),"BASE_ENV VIF Configuration failure!")
        base_agt   = base_agent::type_id::create("base_agt",this);
        base_agt1  = base_agent1::type_id::create("base_agt1",this);
        fifo_sb    = fifo_scoreboard::type_id::create("fifo_sb",this);
        vseqr      = fifo_virtual_sequencer::type_id::create("vseqr",this);
    endfunction
    
    virtual function void start_of_simulation_phase(uvm_phase phase);
        `uvm_info(get_type_name(),{"Start of simulation phase for ",get_full_name()}, UVM_LOW)
    endfunction
    
    // connect handles of local sequencers to virtual sequencer
    virtual function void connect_phase(uvm_phase phase);
        `uvm_info(get_full_name(),{"Starting Connect phase for ",get_type_name()}, UVM_LOW)
        super.connect_phase(phase);
      //base seqer to virtual seqer
        vseqr.base_seqr = base_agt.base_seqr;
        vseqr.base_seqr1 = base_agt1.base_seqr1;
      
      // monitor to scb
      	base_agt.base_mon.mon_wr_ap.connect(fifo_sb.fifo_in.analysis_export);
	  	base_agt1.base_mon1.mon_rd_ap.connect(fifo_sb.fifo_out.analysis_export);
    endfunction
    
endclass : base_env