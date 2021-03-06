/*
 * Copyright 2018 Google LLC
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// Base class for all load/store instruction stream

class riscv_load_store_base_instr_stream extends riscv_mem_access_stream;

  typedef enum bit [1:0] {
    NARROW,
    HIGH,
    MEDIUM,
    SPARSE
  } locality_e;

  rand int unsigned  num_load_store;
  rand int unsigned  num_mixed_instr;
  rand int           base;
  int                offset[];
  int                addr[];
  riscv_instr_base   load_store_instr[$];
  rand int unsigned  data_page_id;
  rand riscv_reg_t   rs1_reg;
  rand locality_e    locality;
  rand int           max_load_store_offset;

  `uvm_object_utils(riscv_load_store_base_instr_stream)

  constraint rs1_c {
    !(rs1_reg inside {cfg.reserved_regs, reserved_rd, ZERO});
  }

  constraint addr_c {
    solve data_page_id before max_load_store_offset;
    solve max_load_store_offset before base;
    data_page_id < max_data_page_id;
    foreach (data_page[i]) {
      if (i == data_page_id) {
        max_load_store_offset == data_page[i].size_in_bytes;
      }
    }
    base inside {[0 : max_load_store_offset-1]};
  }

  function new(string name = "");
    super.new(name);
  endfunction

  virtual function void randomize_offset();
    int offset_, addr_;
    offset = new[num_load_store];
    addr = new[num_load_store];
    for (int i=0; i<num_load_store; i++) begin
      if (!std::randomize(offset_, addr_) with {
        // Locality
        if (locality == NARROW) {
          soft offset_ inside {[-16:16]};
        } else if (locality == HIGH) {
          soft offset_ inside {[-64:64]};
        } else if (locality == MEDIUM) {
          soft offset_ inside {[-256:256]};
        } else if (locality == SPARSE) {
          soft offset_ inside {[-2048:2047]};
        }
        addr_ == base + offset_;
        addr_ inside {[0 : max_load_store_offset - 1]};
      }) begin
        `uvm_fatal(`gfn, "Cannot randomize load/store offset")
      end
      offset[i] = offset_;
      addr[i] = addr_;
    end
  endfunction

  function void post_randomize();
    randomize_offset();
    gen_load_store_instr();
    add_mixed_instr(num_mixed_instr);
    add_rs1_init_la_instr(rs1_reg, data_page_id, base);
    super.post_randomize();
  endfunction

  bit enable_compressed_load_store;

  // Generate each load/store instruction
  virtual function void gen_load_store_instr();
    randomize_avail_regs();
    set_en_compressed_load_store();
    protect_address_reg();
    foreach (addr[i]) gen_load_store_for_addr(i);
  endfunction

  virtual function void set_en_compressed_load_store();
    if ((rs1_reg inside {[S0 : A5]}) && !cfg.disable_compressed_instr) begin
      enable_compressed_load_store = 1;
    end
  endfunction

  virtual function void protect_address_reg();
    // rs1 cannot be modified by other instructions
    if(!(rs1_reg inside {reserved_rd})) reserved_rd = {reserved_rd, rs1_reg};
  endfunction

  int idx;

  virtual function void gen_load_store_for_addr(int idx);
    this.idx = idx;
    build_allowed_instr();
    create_rand_instr();
  endfunction

  virtual function void create_rand_instr();
    riscv_instr_base instr = riscv_instr_base::type_id::create("instr");
    randomize_instr(instr, .skip_rs1(1'b1), .skip_imm(1'b1), .disable_dist(1'b1));
    instr.rs1 = rs1_reg;
    instr.set_imm(offset[idx]);
    instr.process_load_store = 0;
    instr_list.push_back(instr);
  endfunction

  virtual function void build_allowed_instr();
    // Assign the allowed load/store instructions based on address alignment
    // This is done separately rather than a constraint to improve the randomization performance
    allowed_instr = {};
    add_byte_aligned_load_stores();
    if (is_h_aligned(addr[idx]) || cfg.enable_unaligned_load_store) add_h_aligned_load_stores();
    if (is_w_aligned(addr[idx]) || cfg.enable_unaligned_load_store) add_w_aligned_load_stores();
    if (XLEN >= 64 && (is_d_aligned(addr[idx]) || cfg.enable_unaligned_load_store)) add_d_aligned_load_stores();
  endfunction

  virtual function void add_byte_aligned_load_stores();
    allowed_instr = {LB, LBU, SB, allowed_instr};
  endfunction

  virtual function void add_h_aligned_load_stores();
    allowed_instr = {LH, LHU, SH, allowed_instr};
  endfunction

  virtual function void add_w_aligned_load_stores();
    allowed_instr = {LW, SW, allowed_instr};
    if (cfg.enable_floating_point && (RV32F inside {supported_isa})) allowed_instr = {FLW, FSW, allowed_instr};
    if (can_be_compressed(32)) add_compressed_w_aligned_load_stores();
  endfunction

  virtual function void add_d_aligned_load_stores();
    allowed_instr = {LWU, LD, SD, allowed_instr};
    if (cfg.enable_floating_point && (RV32D inside {supported_isa})) allowed_instr = {FLD, FSD, allowed_instr};
    if (can_be_compressed(64)) add_compressed_d_aligned_load_stores();
  endfunction

  virtual function bit can_be_compressed(int bits);
    int max = (bits == 64) ? 256 : 128;
    int mod = (bits == 64) ? 8 : 4;
    riscv_instr_group_t ig = (bits == 64) ? RV64C : RV32C;
    return (offset[idx] < max) && (offset[idx] % mod == 0) &&
           (ig inside {riscv_instr_pkg::supported_isa}) &&
           enable_compressed_load_store;
  endfunction

  virtual function void add_compressed_w_aligned_load_stores();
    allowed_instr = {C_LW, C_SW, allowed_instr};
    if (cfg.enable_floating_point && (RV32FC inside {supported_isa})) allowed_instr = {C_FLW, C_FSW, allowed_instr};
  endfunction

  virtual function void add_compressed_d_aligned_load_stores();
    allowed_instr = {C_LD, C_SD, allowed_instr};
    if (cfg.enable_floating_point && (RV32DC inside {supported_isa})) allowed_instr = {C_FLD, C_FSD, allowed_instr};
  endfunction

endclass


class riscv_vec_unit_stride_load_store_instr_stream extends riscv_mem_access_stream;

  typedef enum {B_ALIGNMENT, H_ALIGNMENT, W_ALIGNMENT, E_ALIGNMENT} alignment_e;

  rand alignment_e alignment;
  rand int unsigned data_page_id;
  rand int unsigned num_mixed_instr;
  rand riscv_reg_t rs1_reg;

  constraint vec_mixed_instr_c {num_mixed_instr inside {[0:10]};}
  constraint vec_rs1_c {!(rs1_reg inside {cfg.reserved_regs, reserved_rd, ZERO});}
  constraint vec_data_page_id_c {data_page_id < max_data_page_id;}
  constraint alignment_sew_c {
    if (SEW <= 16) {alignment != W_ALIGNMENT;}
    if (SEW <=  8) {alignment != H_ALIGNMENT;}
  }

  // int unsigned num_load_store;
  // int addr[];
  int base;
  int max_load_store_addr;
  riscv_instr_base load_store_instr;

  `uvm_object_utils(riscv_vec_unit_stride_load_store_instr_stream)

  function new(string name = "riscv_vec_unit_stride_load_store_instr_stream");
    super.new(name);
  endfunction

  function void post_randomize();
    randomize_base();
    // rs1 cannot be modified by other instructions
    if(!(rs1_reg inside {reserved_rd})) reserved_rd = {reserved_rd, rs1_reg};
    randomize_avail_regs();
    gen_load_store_instr();
    add_mixed_instr(num_mixed_instr);
    add_rs1_init_la_instr(rs1_reg, data_page_id, base);
    super.post_randomize();
  endfunction

  virtual function void randomize_base();
    int ss = stride_span();
    max_load_store_addr = data_page[data_page_id].size_in_bytes - ss;

    assert (max_load_store_addr >= 0) else begin
      `uvm_fatal(`gfn, $sformatf({"Expected positive value for max_load_store_addr.",
        "  Perhaps more memory needs to be allocated in the data pages for vector loads and stores.",
        "\ndata_page_id:%0d\ndata_page[data_page_id].size_in_bytes:%0d\nstride_span:%0d",
        "\nalignment:%s\nstride_bytes:%0d\nVLEN:%0d\nLMUL:%0d\nSEW:%0d\n\n"},
        data_page_id, data_page[data_page_id].size_in_bytes, ss,
        alignment.name(), stride_bytes(), VLEN, LMUL, SEW))
    end

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(base, base >= 0; base <= max_load_store_addr;)
    if (!cfg.enable_unaligned_load_store) base &= ~get_addr_alignment_mask(stride_bytes());
  endfunction

  virtual function int stride_span();
    int num_elements = VLEN * LMUL / SEW;
    stride_span = num_elements * stride_bytes();
  endfunction

  virtual function int stride_bytes();
    stride_bytes = 0;
    if (alignment == B_ALIGNMENT) stride_bytes = 1;
    else if (alignment == H_ALIGNMENT) stride_bytes = 2;
    else if (alignment == W_ALIGNMENT) stride_bytes = 4;
    else if (alignment == E_ALIGNMENT) stride_bytes = SEW;
  endfunction

  // Generate each load/store instruction
  virtual function void gen_load_store_instr();
    build_allowed_instr();
    load_store_instr = riscv_instr_base::type_id::create("load_store_instr");
    randomize_vec_load_store_instr();
    configure_vec_load_store_instr();
    instr_list.push_back(load_store_instr);
  endfunction

  virtual function void build_allowed_instr();
    if (alignment == B_ALIGNMENT) add_byte_aligned_vec_load_stores();
    else if (alignment == H_ALIGNMENT) add_h_aligned_vec_load_stores();
    else if (alignment == W_ALIGNMENT) add_w_aligned_vec_load_stores();
    else if (alignment == E_ALIGNMENT) add_element_vec_load_stores();
  endfunction

  virtual function void add_element_vec_load_stores();
    allowed_instr = {VLE_V, VSE_V, allowed_instr};
  endfunction

  virtual function void add_byte_aligned_vec_load_stores();
    allowed_instr = {VLB_V, VSB_V, VLBU_V, allowed_instr};
  endfunction

  virtual function void add_h_aligned_vec_load_stores();
    allowed_instr = {VLH_V, VSH_V, VLHU_V, allowed_instr};
  endfunction

  virtual function void add_w_aligned_vec_load_stores();
    allowed_instr = {VLW_V, VSW_V, VLWU_V, allowed_instr};
  endfunction

  virtual function void randomize_vec_load_store_instr();
    randomize_instr(load_store_instr, .skip_rs1(1'b1), .skip_imm(1'b1), .disable_dist(1'b1));
  endfunction

  virtual function void configure_vec_load_store_instr();
    load_store_instr.gen_rand_fields(cfg);
    load_store_instr.rs1 = rs1_reg;
    load_store_instr.process_load_store = 0;
  endfunction

endclass

// A single load/store instruction
class riscv_single_load_store_instr_stream extends riscv_load_store_base_instr_stream;

  constraint legal_c {
    num_load_store == 1;
    num_mixed_instr < 5;
  }

  `uvm_object_utils(riscv_single_load_store_instr_stream)
  `uvm_object_new

endclass

// Back to back load/store instructions
class riscv_load_store_stress_instr_stream extends riscv_load_store_base_instr_stream;

  int unsigned max_instr_cnt = 30;
  int unsigned min_instr_cnt = 10;

  constraint legal_c {
    num_load_store inside {[min_instr_cnt:max_instr_cnt]};
    num_mixed_instr == 0;
  }

  `uvm_object_utils(riscv_load_store_stress_instr_stream)
  `uvm_object_new

endclass

// Random load/store sequence
// A random mix of load/store instructions and other instructions
class riscv_load_store_rand_instr_stream extends riscv_load_store_base_instr_stream;

  constraint legal_c {
    num_load_store inside {[10:30]};
    num_mixed_instr inside {[10:30]};
  }

  `uvm_object_utils(riscv_load_store_rand_instr_stream)
  `uvm_object_new

endclass

// Use a small set of GPR to create various WAW, RAW, WAR hazard scenario
class riscv_hazard_instr_stream extends riscv_load_store_base_instr_stream;

  int unsigned num_of_avail_regs = 6;

  constraint legal_c {
    num_load_store inside {[10:30]};
    num_mixed_instr inside {[10:30]};
  }

  `uvm_object_utils(riscv_hazard_instr_stream)
  `uvm_object_new

  function void pre_randomize();
    avail_regs = new[num_of_avail_regs];
    super.pre_randomize();
  endfunction

endclass

// Use a small set of address to create various load/store hazard sequence
// This instruction stream focus more on hazard handling of load store unit.
class riscv_load_store_hazard_instr_stream extends riscv_load_store_base_instr_stream;

  rand int avail_addr[];

  constraint legal_c {
    num_load_store inside {[10:30]};
    num_mixed_instr inside {[10:30]};
  }

  constraint avail_addr_c {
    avail_addr.size() inside {[1:3]};
    foreach(avail_addr[i]) {
      avail_addr[i] inside {[0 : max_load_store_offset - 1]};
    }
  }

  `uvm_object_utils(riscv_load_store_hazard_instr_stream)
  `uvm_object_new

  // Randomize each address in the post_randomize to reduce the complexity of solving everything
  // in one shot.
  function void post_randomize();
    int temp_addr;
    foreach(addr[i]) begin
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(temp_addr,
                                         temp_addr inside {avail_addr};,
                                         "Cannot randomize address")
      addr[i] = temp_addr;
    end
  endfunction
endclass

// Back to back access to multiple data pages
// This is useful to test data TLB switch and replacement
class riscv_multi_page_load_store_instr_stream extends riscv_mem_access_stream;

  riscv_load_store_stress_instr_stream load_store_instr_stream[];
  rand int unsigned num_of_instr_stream;
  rand int unsigned data_page_id[];
  rand riscv_reg_t  rs1_reg[];

  constraint default_c {
    foreach(data_page_id[i]) {
      data_page_id[i] < max_data_page_id;
    }
    data_page_id.size() == num_of_instr_stream;
    rs1_reg.size() == num_of_instr_stream;
    unique {rs1_reg};
    foreach(rs1_reg[i]) {
      !(rs1_reg[i] inside {cfg.reserved_regs, ZERO});
    }
  }

  constraint page_c {
    solve num_of_instr_stream before data_page_id;
    num_of_instr_stream inside {[1 : max_data_page_id]};
    unique {data_page_id};
  }

  // Avoid accessing a large number of pages because we may run out of registers for rs1
  // Each page access needs a reserved register as the base address of load/store instruction
  constraint reasonable_c {
    num_of_instr_stream inside {[2:8]};
  }

  `uvm_object_utils(riscv_multi_page_load_store_instr_stream)
  `uvm_object_new

  // Generate each load/store seq, and mix them together
  function void post_randomize();
    load_store_instr_stream = new[num_of_instr_stream];
    foreach(load_store_instr_stream[i]) begin
      load_store_instr_stream[i] = riscv_load_store_stress_instr_stream::type_id::
                                   create($sformatf("load_store_instr_stream_%0d", i));
      load_store_instr_stream[i].min_instr_cnt = 5;
      load_store_instr_stream[i].max_instr_cnt = 10;
      load_store_instr_stream[i].cfg = cfg;
      // Make sure each load/store sequence doesn't override the rs1 of other sequences.
      foreach(rs1_reg[j]) begin
        if(i != j) begin
          load_store_instr_stream[i].reserved_rd =
            {load_store_instr_stream[i].reserved_rd, rs1_reg[j]};
        end
      end
      `DV_CHECK_RANDOMIZE_WITH_FATAL(load_store_instr_stream[i],
                                     rs1_reg == local::rs1_reg[i];
                                     data_page_id == local::data_page_id[i];,
                                     "Cannot randomize load/store instruction")
      // Mix the instruction stream of different page access, this could trigger the scenario of
      // frequent data TLB switch
      if(i == 0) begin
        instr_list = load_store_instr_stream[i].instr_list;
      end else begin
        mix_instr_stream(load_store_instr_stream[i].instr_list);
      end
    end
  endfunction

endclass

// Access the different locations of the same memory regions
class riscv_mem_region_stress_test extends riscv_multi_page_load_store_instr_stream;

  `uvm_object_utils(riscv_mem_region_stress_test)
  `uvm_object_new

  constraint page_c {
    num_of_instr_stream inside {[2:5]};
    foreach (data_page_id[i]) {
      if (i > 0) {
        data_page_id[i] == data_page_id[i-1];
      }
    }
  }

endclass

// Random load/store sequence to full address range
// The address range is not preloaded with data pages, use store instruction to initialize first
class riscv_load_store_rand_addr_instr_stream extends riscv_load_store_base_instr_stream;

  rand bit [XLEN-1:0] addr_offset;

  // Find an unused 4K page from address 1M onward
  constraint addr_offset_c {
    |addr_offset[XLEN-1:20] == 1'b1;
    // TODO(taliu) Support larger address range
    addr_offset[XLEN-1:31] == 0;
    addr_offset[11:0] == 0;
  }

  constraint legal_c {
    num_load_store inside {[5:10]};
    num_mixed_instr inside {[5:10]};
  }

  `uvm_object_utils(riscv_load_store_rand_addr_instr_stream)

   virtual function void randomize_offset();
    int offset_, addr_;
    offset = new[num_load_store];
    addr = new[num_load_store];
    for (int i=0; i<num_load_store; i++) begin
      if (!std::randomize(offset_) with {
          offset_ inside {[-2048:2047]};
        }
      ) begin
        `uvm_fatal(`gfn, "Cannot randomize load/store offset")
      end
      offset[i] = offset_;
      addr[i] = addr_offset + offset_;
    end
  endfunction `uvm_object_new

  virtual function void add_rs1_init_la_instr(riscv_reg_t gpr, int id, int base = 0);
    riscv_instr_base instr[$];
    riscv_pseudo_instr li_instr;
    riscv_instr_base store_instr;
    riscv_instr_base add_instr;
    int min_offset[$];
    int max_offset[$];
    min_offset = offset.min();
    max_offset = offset.max();
    // Use LI to initialize the address offset
    li_instr = riscv_pseudo_instr::type_id::create("li_instr");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(li_instr,
       pseudo_instr_name == LI;
       rd inside {cfg.gpr};
       rd != gpr;
    )
    li_instr.imm_str = $sformatf("0x%0x", addr_offset);
    // Add offset to the base address
    add_instr = riscv_instr_base::type_id::create("add_instr");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(add_instr,
       instr_name == ADD;
       rs1 == gpr;
       rs2 == li_instr.rd;
       rd  == gpr;
    )
    instr.push_back(li_instr);
    instr.push_back(add_instr);
    // Create SW instruction template
    store_instr = riscv_instr_base::type_id::create("store_instr");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(store_instr,
       instr_name == SB;
       rs1 == gpr;
    )
    // Initialize the location which used by load instruction later
    foreach (load_store_instr[i]) begin
      if (load_store_instr[i].category == LOAD) begin
        riscv_instr_base store;
        store = riscv_instr_base::type_id::create("store");
        store.copy_base_instr(store_instr);
        store.rs2 = riscv_reg_t'(i % 32);
        store.imm_str = load_store_instr[i].imm_str;
        case (load_store_instr[i].instr_name) inside
          LB, LBU : store.instr_name = SB;
          LH, LHU : store.instr_name = SH;
          LW, C_LW, FLW, C_FLW : store.instr_name = SW;
          LD, C_LD, FLD, C_FLD, LWU : store.instr_name = SD;
          default : `uvm_fatal(`gfn, $sformatf("Unexpected op: %0s",
                                               load_store_instr[i].convert2asm()))
        endcase
        instr.push_back(store);
      end
    end
    instr_list = {instr, instr_list};
    super.add_rs1_init_la_instr(gpr, id, 0);
  endfunction

endclass
