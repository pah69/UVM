// Write Monitor class
class base_monitor extends uvm_monitor;
    `uvm_component_utils(base_monitor)
    
    int write_cnt;
    virtual base_intf base_vif;

    uvm_analysis_port#(base_seq_item) mon_wr_ap;
    
  // Coverage 
    covergroup my_covergroup;
      option.per_instance = 1; // required for VCS
      
      // Data in
      in_cover: coverpoint base_vif.data_in;
      
      // Data out
      out_cover: coverpoint base_vif.data_out;
      
      // Write address
      wr_addr_cover: coverpoint base_vif.wr_ptr {
        bins addr_bins[] = {[0:MEM_SIZE]}; // Define bins for write pointer
    }
      
      // Read address
      rd_addr_cover: coverpoint base_vif.rd_ptr {
        bins addr_bins[] = {[0:MEM_SIZE]}; // Define bins for read pointer
    }
    // Status cover
    full_cov: coverpoint base_vif.fifo_full;
    empty_cov: coverpoint base_vif.fifo_empty;
    threshold_cov: coverpoint base_vif.fifo_threshold;
    overflow_cov: coverpoint base_vif.fifo_overflow;
    underflow_cov: coverpoint base_vif.fifo_underflow;

      // Cross coverage
      in_X_out : cross in_cover, out_cover;
      wr_X_rd : cross wr_addr_cover, rd_addr_cover;
    endgroup
   
    function new(input string name="BASE_MONITOR", uvm_component parent=null);
        super.new(name,parent);
        mon_wr_ap = new("mon_wr_ap", this);
        my_covergroup = new;
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        `uvm_info(get_full_name(),{"Starting Build phase for ",get_type_name()}, UVM_LOW)
        if(!uvm_config_db#(virtual base_intf)::get(this,"","base_intf",base_vif))
            `uvm_fatal(get_type_name(),"BASE_MONITOR VIF Configuration failure!")
    endfunction
    
    virtual function void start_of_simulation_phase(uvm_phase phase);
        `uvm_info(get_full_name(),{"Start of simulation phase for ",get_type_name()}, UVM_LOW)
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        super.run_phase(phase);
        `uvm_info(get_full_name(),{"Starting Run phase for ",get_type_name()}, UVM_LOW)
        forever begin
            base_seq_item base_seq = base_seq_item::type_id::create("base_seq");
            

          @(posedge base_vif.clk)
          if(base_vif.rst_n && base_vif.wr) begin
                    base_seq.data_in   = base_vif.data_in;
                    base_seq.wr        = base_vif.wr;   
                    base_seq.fifo_full = base_vif.fifo_full;
                   `uvm_info(get_type_name(),$sformatf("BASE_MONITOR write item: %s",base_seq.sprint()),UVM_LOW)
                    mon_wr_ap.write(base_seq);
                    write_cnt++;
                   `uvm_info(get_type_name(),$sformatf("BASE_MONITOR write items collected : %0d ",write_cnt),UVM_LOW);
                    my_covergroup.sample();
                    $display("STDOUT: %3.2f%% coverage achieved.", my_covergroup.get_inst_coverage());
           end    
        end
    endtask
    
    function void report_phase(uvm_phase phase);
        `uvm_info(get_type_name(),$sformatf("BASE_MONITOR write items collected : %0d ",write_cnt),UVM_LOW);
    endfunction
    
endclass : base_monitor


// Read Monitor class
class base_monitor1 extends uvm_monitor;
    `uvm_component_utils(base_monitor1)
    
    int read_cnt;
    virtual base_intf base_vif;

    uvm_analysis_port #(base_seq_item) mon_rd_ap;
    
    function new(input string name="BASE_MONITOR_1", uvm_component parent=null);
        super.new(name,parent);
        mon_rd_ap = new("mon_rd_ap", this);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        `uvm_info(get_full_name(),{"Starting Build phase for ",get_type_name()}, UVM_LOW)
        if(!uvm_config_db#(virtual base_intf)::get(this,"","base_intf",base_vif))
            `uvm_fatal(get_type_name(),"BASE_MONITOR_1 VIF Configuration failure!")
    endfunction
    
    virtual function void start_of_simulation_phase(uvm_phase phase);
        `uvm_info(get_full_name(),{"Start of simulation phase for ",get_type_name()}, UVM_LOW)
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        super.run_phase(phase);
        `uvm_info(get_full_name(),{"Starting Run phase for ",get_type_name()}, UVM_LOW)
        forever begin
            base_seq_item base_seq = base_seq_item::type_id::create("base_seq");
           
          @(posedge base_vif.clk)
          if(base_vif.rst_n && base_vif.rd) begin
                    base_seq.rd   = base_vif.rd;
                    base_seq.data_out = base_vif.data_out;
                    base_seq.fifo_empty = base_vif.fifo_empty;
                   `uvm_info(get_type_name(),$sformatf("BASE_MONITOR_1 read item: %s",base_seq.sprint()),UVM_LOW)
                    mon_rd_ap.write(base_seq);
                    read_cnt++;
                   `uvm_info(get_type_name(),$sformatf("BASE_MONITOR_1 read items collected : %0d",read_cnt),UVM_LOW);
          end
        end
    endtask
    
    function void report_phase(uvm_phase phase);
        `uvm_info(get_type_name(),$sformatf("BASE_MONITOR_1 read items collected : %0d ",read_cnt),UVM_LOW);
    endfunction
    
endclass : base_monitor1