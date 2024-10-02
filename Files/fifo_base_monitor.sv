// Write Monitor class
class base_monitor extends uvm_monitor;
  `uvm_component_utils(base_monitor)
  
  int write_cnt;
  virtual base_intf base_vif;

  uvm_analysis_port#(base_seq_item) mon_wr_ap;
  
/// *************   Coverage 
  covergroup data_cover;
    option.per_instance = 1; // required for VCS
    
    // Data in
    in_cover: coverpoint base_vif.data_in {
      bins data_i[] = {[0:DATA_WIDTH]};
    }      
    // Data out
    out_cover: coverpoint base_vif.data_out {
      bins data_o[] = {[0:DATA_WIDTH]};
    }      
  endgroup

  covergroup write_cover;
    option.per_instance = 1;
    write_cp: coverpoint base_vif.wr {
      bins in_wr[] = {1};
    }
    writeptr_cp : coverpoint base_vif.wptr {
      bins in_ptr[] = {[0:MEM_SIZE]};
    }
  endgroup


  covergroup status_cover;
  // Status cover
    option.per_instance = 1;

  full_cov: coverpoint base_vif.fifo_full;
  empty_cov: coverpoint base_vif.fifo_empty;
  threshold_cov: coverpoint base_vif.fifo_threshold;
  overflow_cov: coverpoint base_vif.fifo_overflow;
  underflow_cov: coverpoint base_vif.fifo_underflow;
  endgroup


//     covergroup cross_cover;
//       option.per_instance = 1;
//       full_X_overflow : cross full_cov, overflow_cov;
//       full_X_threshold : cross full_cov, threshold_cov;
//     endgroup
 ///////////////////

/// Constructor
  function new(input string name="BASE_MONITOR", uvm_component parent=null);
      super.new(name,parent);
      mon_wr_ap = new("mon_wr_ap", this);
      data_cover = new;
      write_cover = new;
      status_cover = new;
//         cross_cover = new;

  endfunction
  
/// Build
  virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      `uvm_info(get_full_name(),{"Starting Build phase for ",get_type_name()}, UVM_LOW)
      if(!uvm_config_db#(virtual base_intf)::get(this,"","base_intf",base_vif))
          `uvm_fatal(get_type_name(),"BASE_MONITOR VIF Configuration failure!")
  endfunction
  
        // start simu
  virtual function void start_of_simulation_phase(uvm_phase phase);
      `uvm_info(get_full_name(),{"Start of simulation phase for ",get_type_name()}, UVM_LOW)
  endfunction
  
// run phase
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
                    base_seq.fifo_empty = base_vif.fifo_empty;
                    base_seq.fifo_overflow = base_vif.fifo_overflow;
                 `uvm_info(get_type_name(),$sformatf("BASE_MONITOR write item: %s",base_seq.sprint()),UVM_LOW)
                    mon_wr_ap.write(base_seq);
                    write_cnt++;
                 `uvm_info(get_type_name(),$sformatf("BASE_MONITOR write items collected : %0d ",write_cnt),UVM_LOW);
                    data_cover.sample();
                    write_cover.sample();
                    status_cover.sample();
//                       cross_cover.sample();
         end    
      end
  endtask
  
  function void report_phase(uvm_phase phase);
      `uvm_info(get_type_name(),$sformatf("BASE_MONITOR write items collected : %0d ",write_cnt),UVM_LOW);
      $display("STDOUT: %3.2f%% coverage achieved.", data_cover.get_inst_coverage());
      $display("STDOUT: %3.2f%% coverage achieved.", write_cover.get_inst_coverage());
      $display("STDOUT: %3.2f%% coverage achieved.", status_cover.get_inst_coverage());         
//         $display("STDOUT: %3.2f%% coverage achieved.", cross_cover.get_inst_coverage());
  endfunction
  
endclass : base_monitor


// Read Monitor class
class base_monitor1 extends uvm_monitor;
  `uvm_component_utils(base_monitor1)
  
  int read_cnt;

  virtual base_intf base_vif;

  uvm_analysis_port #(base_seq_item) mon_rd_ap;
  
// ****** COVERGROUP
  covergroup data_cover;
    option.per_instance = 1; // required for VCS
    
    // Data in
    in_cover: coverpoint base_vif.data_in {
      bins data_i[] = {[0:DATA_WIDTH]};
    }      
    // Data out
    out_cover: coverpoint base_vif.data_out {
      bins data_o[] = {[0:DATA_WIDTH]};
    }      
  endgroup

  covergroup read_cover;
    option.per_instance = 1;
    read_cp: coverpoint base_vif.rd {
      bins in_wr[] = {1};
    }
    readtr_cp : coverpoint base_vif.rptr {
      bins in_ptr[] = {[0:MEM_SIZE]};
    }
  endgroup

covergroup status_cover;
  // Status cover
    option.per_instance = 1;

  full_cov: coverpoint base_vif.fifo_full;
  empty_cov: coverpoint base_vif.fifo_empty;
  threshold_cov: coverpoint base_vif.fifo_threshold;
  overflow_cov: coverpoint base_vif.fifo_overflow;
  underflow_cov: coverpoint base_vif.fifo_underflow;
  endgroup


//     covergroup cross_cover;

//       full_X_underflow : cross full_cov, underflow_cov;
//       empty_X_threshold : cross empty_cov, threshold_cov;
//     endgroup

// construct
  function new(input string name="BASE_MONITOR_1", uvm_component parent=null);
      super.new(name,parent);
      mon_rd_ap = new("mon_rd_ap", this);
      data_cover = new;
      read_cover = new;
      status_cover = new;
//         cross_cover = new;

  endfunction
  
// build
  virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      `uvm_info(get_full_name(),{"Starting Build phase for ",get_type_name()}, UVM_LOW)
      if(!uvm_config_db#(virtual base_intf)::get(this,"","base_intf",base_vif))
          `uvm_fatal(get_type_name(),"BASE_MONITOR_1 VIF Configuration failure!")
  endfunction
  
        //start simu
  virtual function void start_of_simulation_phase(uvm_phase phase);
      `uvm_info(get_full_name(),{"Start of simulation phase for ",get_type_name()}, UVM_LOW)
  endfunction
  
//run phase
  virtual task run_phase(uvm_phase phase);
      super.run_phase(phase);
      `uvm_info(get_full_name(),{"Starting Run phase for ",get_type_name()}, UVM_LOW)
      forever begin
          base_seq_item base_seq = base_seq_item::type_id::create("base_seq");
         
        @(posedge base_vif.clk)
        if(base_vif.rst_n && base_vif.rd) begin
                  base_seq.rd   = base_vif.rd;
                  base_seq.data_out = base_vif.data_out;
              base_seq.fifo_underflow = base_vif.fifo_underflow;
                  base_seq.fifo_empty = base_vif.fifo_empty;
              
                 `uvm_info(get_type_name(),$sformatf("BASE_MONITOR_1 read item: %s",base_seq.sprint()),UVM_LOW)
                  mon_rd_ap.write(base_seq);
                  read_cnt++;
                 `uvm_info(get_type_name(),$sformatf("BASE_MONITOR_1 read items collected : %0d",read_cnt),UVM_LOW);
            data_cover.sample();
          read_cover.sample();
          status_cover.sample();
//         		cross_cover.sample();
        end
    end
endtask

  function void report_phase(uvm_phase phase);
      `uvm_info(get_type_name(),$sformatf("BASE_MONITOR_1 read items collected : %0d ",read_cnt),UVM_LOW);
    
    $display("STDOUT: %3.2f%% coverage achieved.", data_cover.get_inst_coverage());
      $display("STDOUT: %3.2f%% coverage achieved.", read_cover.get_inst_coverage());  
    $display("STDOUT: %3.2f%% coverage achieved.", status_cover.get_inst_coverage());  
//         $display("STDOUT: %3.2f%% coverage achieved.", cross_cover.get_inst_coverage());
    
  endfunction
  
  
endclass : base_monitor1