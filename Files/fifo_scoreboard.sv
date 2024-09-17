class fifo_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(fifo_scoreboard)
    
    
    // constructor
    function new(string name = "", uvm_component parent);
      super.new(name,parent);
    endfunction
    
    // TLM port
    uvm_tlm_analysis_fifo #(base_seq_item) fifo_in;
    uvm_tlm_analysis_fifo #(base_seq_item) fifo_out;
    
    uvm_get_port #(base_seq_item) get_in;
    uvm_get_port #(base_seq_item) get_out;
  
  
    base_seq_item base_in;
    base_seq_item base_out;
    
    function void build_phase (uvm_phase phase);
      super.build_phase(phase);
      
      fifo_in = new("fifo_in",this);
      fifo_out = new("fifo_out",this);
      
      get_in = new("get_in",this);
      get_out = new("get_out",this);
      
    endfunction : build_phase
    
    function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      
      get_in.connect(fifo_in.get_export);    
      get_out.connect(fifo_out.get_export);
      
    endfunction : connect_phase
    
    function void check_phase(uvm_phase phase);
      super.check_phase(phase);
      `uvm_info(get_full_name(),{"Starting ScoreBoard ",get_type_name()}, UVM_LOW)
  
      while(get_in.can_get() && get_out.can_get() ) begin
        
        base_in  = base_seq_item::type_id::create("base_in",this);
        base_out = base_seq_item::type_id::create("base_out",this);
        
        void'(get_out.try_get(base_out));
        void'(get_in.try_get(base_in));
        
        if(base_in.data_in != base_out.data_out)
          `uvm_info(get_type_name(),$sformatf("MISMATCH DATA_IN=0x%0h, DATA_OUT=0x%0h",base_in.data_in, base_out.data_out),UVM_LOW)
        
        else
          `uvm_info(get_type_name(),$sformatf("MATCH DATA_IN=0x%0h, DATA_OUT=0x%0h",base_in.data_in, base_out.data_out),UVM_LOW)
      end 
          
    endfunction : check_phase
  
    
  endclass : fifo_scoreboard
      
      
    
    