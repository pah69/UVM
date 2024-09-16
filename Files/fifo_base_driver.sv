//Base Driver class

//////////////////// WRITE
class base_driver1 extends uvm_driver#(base_seq_item);
    `uvm_component_utils(base_driver1)
    
    virtual base_intf base_vif;

    function new(input string name="base_driver1", uvm_component parent=null);
        super.new(name,parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        `uvm_info(get_full_name(),{"Starting Build phase for ",get_type_name()}, UVM_LOW)
        if(!uvm_config_db#(virtual base_intf)::get(this,"","base_intf",base_vif))
            `uvm_fatal(get_type_name(),"base_driver1 VIF Configuration failure!")
    endfunction
    
    virtual function void start_of_simulation_phase(uvm_phase phase);
        `uvm_info(get_full_name(),{"Start of simulation phase for ",get_type_name()}, UVM_LOW)
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        super.run_phase(phase);
        `uvm_info(get_full_name(),{"Starting base_driver1 Run phase for ",get_type_name()}, UVM_LOW)
        forever begin
           seq_item_port.get_next_item(req);
           drv_fifo_wr(req);            
           seq_item_port.item_done();
        end
    endtask
    
    task drv_fifo_wr(base_seq_item req_item);
        `uvm_info(get_type_name(),$sformatf("base_driver1 write item: %s",req_item.sprint()),UVM_LOW)
      @(negedge base_vif.clk)
     // @(base_vif.clk)
      //if (base_vif.rst_n && req_item.wr) begin
                base_vif.data_in = req_item.data_in;
                base_vif.wr   = req_item.wr;
                base_vif.rd   = req_item.rd;
     // end
    endtask : drv_fifo_wr
    
endclass : base_driver1



//Base Driver1 class


////////////////////////// READ
class base_driver2 extends uvm_driver#(base_seq_item);
    `uvm_component_utils(base_driver2)
    
    virtual base_intf base_vif;

    function new(input string name="base_driver1_1", uvm_component parent=null);
        super.new(name,parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        `uvm_info(get_full_name(),{"Starting Build phase for ",get_type_name()}, UVM_LOW)
        if(!uvm_config_db#(virtual base_intf)::get(this,"","base_intf",base_vif))
            `uvm_fatal(get_type_name(),"base_driver1_1 VIF Configuration failure!")
    endfunction
    
    virtual function void start_of_simulation_phase(uvm_phase phase);
        `uvm_info(get_full_name(),{"Start of simulation phase for ",get_type_name()}, UVM_LOW)
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        super.run_phase(phase);
        `uvm_info(get_full_name(),{"Starting base_driver1_1 Run phase for ",get_type_name()}, UVM_LOW)
        forever begin
           seq_item_port.get_next_item(req);
           drv_fifo_rd(req);            
           seq_item_port.item_done();
        end
    endtask
        
    task drv_fifo_rd(base_seq_item req_item);
        `uvm_info(get_type_name(),$sformatf("base_driver1_1 read item: %s",req_item.sprint()),UVM_LOW)
      @(negedge base_vif.clk)
      //@(base_vif.clk)
      if (base_vif.rst_n && req_item.rd) begin
                base_vif.rd   = req_item.rd;
                base_vif.wr   = req_item.wr;
                base_vif.data_in = req_item.data_in;
      end
    endtask : drv_fifo_rd
    
endclass : base_driver2