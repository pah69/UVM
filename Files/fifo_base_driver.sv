//Base Driver class

//////////////////// WRITE
class base_driver extends uvm_driver#(base_seq_item);
  `uvm_component_utils(base_driver)
  
  // VIF
  virtual base_intf base_vif;

// Constructor
  function new(input string name="BASE_DRIVER", uvm_component parent=null);
      super.new(name,parent);
  endfunction
  
// build phase
  virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      `uvm_info(get_full_name(),{"Starting Build phase for ",get_type_name()}, UVM_LOW)
      if(!uvm_config_db#(virtual base_intf)::get(this,"","base_intf",base_vif))
          `uvm_fatal(get_type_name(),"BASE_DRIVER VIF Configuration failure!")
  endfunction
  
  // start simu phase
  virtual function void start_of_simulation_phase(uvm_phase phase);
      `uvm_info(get_full_name(),{"Start of simulation phase for ",get_type_name()}, UVM_LOW)
  endfunction
  
// task run phase
  virtual task run_phase(uvm_phase phase);
      super.run_phase(phase);
      `uvm_info(get_full_name(),{"Starting BASE_DRIVER Run phase for ",get_type_name()}, UVM_LOW)
      forever begin
         seq_item_port.get_next_item(req);
         drv_fifo_wr(req);            
         seq_item_port.item_done();
      end
  endtask
  
// task driver_wr
  task drv_fifo_wr(base_seq_item req_item);
      `uvm_info(get_type_name(),$sformatf("BASE_DRIVER write item: %s",req_item.sprint()),UVM_LOW)
      
  if(req.rst_n) begin
    @(negedge base_vif.clk)
    base_vif.rst_n = req_item.rst_n;
    base_vif.data_in = req_item.data_in;
    base_vif.wr   = req_item.wr;
    base_vif.rd   = req_item.rd;
  end
  // else if reset, send rst_n signal immediatelly
  else begin
    base_vif.rst_n = req_item.rst_n;
  end
endtask : drv_fifo_wr
  
endclass : base_driver



//Base Driver1 class


////////////////////////// READ
class base_driver1 extends uvm_driver#(base_seq_item);
  `uvm_component_utils(base_driver1)
  
// VIF
  virtual base_intf base_vif;
// CONSTRUCTOR
  function new(input string name="BASE_DRIVER_1", uvm_component parent=null);
      super.new(name,parent);
  endfunction
  
  virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      `uvm_info(get_full_name(),{"Starting Build phase for ",get_type_name()}, UVM_LOW)
      if(!uvm_config_db#(virtual base_intf)::get(this,"","base_intf",base_vif))
          `uvm_fatal(get_type_name(),"BASE_DRIVER_1 VIF Configuration failure!")
  endfunction
  
  virtual function void start_of_simulation_phase(uvm_phase phase);
      `uvm_info(get_full_name(),{"Start of simulation phase for ",get_type_name()}, UVM_LOW)
  endfunction
  
  virtual task run_phase(uvm_phase phase);
      super.run_phase(phase);
      `uvm_info(get_full_name(),{"Starting BASE_DRIVER_1 Run phase for ",get_type_name()}, UVM_LOW)
      forever begin
         seq_item_port.get_next_item(req);
         drv_fifo_rd(req);            
         seq_item_port.item_done();
      end
  endtask
      
 task drv_fifo_rd(base_seq_item req_item);
      `uvm_info(get_type_name(),$sformatf("BASE_DRIVER_1 read item: %s",req_item.sprint()),UVM_LOW)
      
  // if no reset, send item at negedge clk
  if (req_item.rst_n) begin
    @(negedge base_vif.clk)
    base_vif.rst_n = req_item.rst_n;
    base_vif.rd    = req_item.rd;
    base_vif.wr    = req_item.wr;
    base_vif.data_in = req_item.data_in;
  end
  // else if reset, send rst_n signal immediatelly
  else begin
    base_vif.rst_n = req_item.rst_n;
  end
endtask : drv_fifo_rd
  
endclass : base_driver1