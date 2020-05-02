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

typedef class riscv_instr_gen_config;

class riscv_instr_base extends uvm_object;

  rand riscv_instr_group_t      group;
  rand riscv_instr_format_t     format;
  rand riscv_instr_category_t   category;
  rand riscv_instr_name_t       instr_name;
  rand bit [11:0]               csr;

  rand riscv_reg_t              rs2;
  rand riscv_reg_t              rs1;
  rand riscv_reg_t              rd;
  rand riscv_fpr_t              fs1;
  rand riscv_fpr_t              fs2;
  rand riscv_fpr_t              fs3;
  rand riscv_fpr_t              fd;
  rand riscv_vec_reg_t          vd;
  rand riscv_vec_reg_t          vs1;
  rand riscv_vec_reg_t          vs2;
  rand riscv_vec_reg_t          vs3;
  rand bit                      vm;
  rand bit                      wd;
  rand bit [31:0]               imm;
  rand imm_t                    imm_type;
  rand bit [4:0]                imm_len;
  rand bit                      is_pseudo_instr;
  rand bit                      aq;
  rand bit                      rl;
  bit                           is_branch_target;
  bit                           has_label = 1'b1;
  bit                           atomic = 0;
  bit                           branch_assigned;
  bit                           process_load_store = 1'b1;
  bit                           is_compressed;
  bit                           is_illegal_instr;
  bit                           is_hint_instr;
  bit                           has_imm;
  bit                           has_rs1;
  bit                           has_rs2;
  bit                           has_rd;
  bit                           has_fs1;
  bit                           has_fs2;
  bit                           has_fs3;
  bit                           has_fd;
  bit                           is_floating_point;
  bit [31:0]                    imm_mask = '1;
  string                        imm_str;
  string                        comment;
  string                        label;
  bit                           is_local_numeric_label;
  int                           idx = -1;

  // Some additional reserved registers
  riscv_reg_t reserved_rd[];

  `uvm_object_utils(riscv_instr_base)

  constraint default_c {
    soft is_pseudo_instr == 0;
    instr_name != INVALID_INSTR;
  }

  // Immediate bit length for different instruction format
  constraint imm_len_c {
    solve imm_type before imm_len;
    if(format inside {U_FORMAT, J_FORMAT}) {
      imm_len == 20;
    }
    if(format inside {I_FORMAT, S_FORMAT, B_FORMAT}) {
      if(imm_type == UIMM) {
        imm_len == 5;
      } else {
        imm_len == 11;
      }
    }
    if(format inside {CI_FORMAT, CSS_FORMAT}) {
      // TODO: gcc compiler seems to not support 6 bits unsigned imm for c.lui,
      // hardcoded to 5 bits for now
      if(instr_name == C_LUI) {
        imm_len == 5;
      } else {
        imm_len == 6;
      }
    }
    if(format inside {CL_FORMAT, CS_FORMAT}) {
      imm_len == 5;
    }
    if(format inside {CJ_FORMAT}) {
      imm_len == 11;
    }
    if(format inside {CB_FORMAT, CIW_FORMAT}) {
      if(instr_name == C_ANDI) {
        imm_len == 6;
      } else {
        imm_len == 8;
      }
    }
    imm_len <= 20;
    if (group == RVV) {imm_len == 5;}
  }

  constraint legal_operand_c {
    (instr_name == C_LUI) -> (rd != SP);
  }

  constraint imm_val_c {
    if(imm_type inside {NZIMM, NZUIMM}) {
      imm != 0;
    }
  }

  constraint aq_rl_c {
    aq && rl == 0;
  }

  // Avoid generating HINT or illegal instruction by default as it's not supported by the compiler
  constraint no_hint_illegal_instr_c {
    if (instr_name inside {C_ADDI, C_ADDIW, C_LI, C_LUI, C_SLLI, C_SLLI64,
                           C_LQSP, C_LDSP, C_MV, C_ADD}) {
      rd != ZERO;
    }
    if (instr_name == C_JR) {
      rs1 != ZERO;
    }
    if (instr_name inside {C_ADD, C_MV}) {
      rs2 != ZERO;
    }
  }

  // Cannot shift more than the width of the bus
  constraint shift_imm_val_c {
    solve category before imm;
    if(category == SHIFT) {
      if(group == RV64I) {
        // The new instruction in RV64I only handles 32 bits value
        imm < 32;
      } else {
        imm < XLEN;
      }
    }
  }

  constraint load_store_c {
    if(category inside {LOAD, STORE}) {
      rs1 != ZERO; // x0 cannot be used to save the base address
    }
  }

  constraint nop_c {
    if(instr_name inside {NOP, C_NOP}) {
      rs1 == ZERO;
      rs2 == ZERO;
      rd  == ZERO;
    }
  }

  constraint jal_c {
    if (XLEN != 32) {
      soft instr_name != C_JAL;
    }
  }

  constraint system_instr_c {
    if (category inside {SYSTEM, SYNCH}) {
      rd  == ZERO;
      rs1 == ZERO;
    }
  }

  constraint rvc_csr_c {
    //  Registers specified by the three-bit rs1’, rs2’, and rd’
    if(format inside {CIW_FORMAT, CL_FORMAT, CS_FORMAT, CB_FORMAT, CA_FORMAT}) {
      rs1 inside {[S0:A5]};
      rs2 inside {[S0:A5]};
      rd  inside {[S0:A5]};
    }
    // C_ADDI16SP is only valid when rd == SP
    if(instr_name == C_ADDI16SP) {
      rd  == SP;
      rs1 == SP;
    }

    if(instr_name inside {C_JR, C_JALR}) {
      rs2 == ZERO;
      rs1 != ZERO;
    }
  }

  ////////////  RV32I instructions  //////////////
  // LOAD instructions
  `add_instr(LB,     I_FORMAT, LOAD, RV32I)
  `add_instr(LH,     I_FORMAT, LOAD, RV32I)
  `add_instr(LW,     I_FORMAT, LOAD, RV32I)
  `add_instr(LBU,    I_FORMAT, LOAD, RV32I)
  `add_instr(LHU,    I_FORMAT, LOAD, RV32I)
  // STORE instructions
  `add_instr(SB,     S_FORMAT, STORE, RV32I)
  `add_instr(SH,     S_FORMAT, STORE, RV32I)
  `add_instr(SW,     S_FORMAT, STORE, RV32I)
  // SHIFT intructions
  `add_instr(SLL,    R_FORMAT, SHIFT, RV32I)
  `add_instr(SLLI,   I_FORMAT, SHIFT, RV32I)
  `add_instr(SRL,    R_FORMAT, SHIFT, RV32I)
  `add_instr(SRLI,   I_FORMAT, SHIFT, RV32I)
  `add_instr(SRA,    R_FORMAT, SHIFT, RV32I)
  `add_instr(SRAI,   I_FORMAT, SHIFT, RV32I)
  // ARITHMETIC intructions
  `add_instr(ADD,    R_FORMAT, ARITHMETIC, RV32I)
  `add_instr(ADDI,   I_FORMAT, ARITHMETIC, RV32I)
  `add_instr(NOP,    I_FORMAT, ARITHMETIC, RV32I)
  `add_instr(SUB,    R_FORMAT, ARITHMETIC, RV32I)
  `add_instr(LUI,    U_FORMAT, ARITHMETIC, RV32I, UIMM)
  `add_instr(AUIPC,  U_FORMAT, ARITHMETIC, RV32I, UIMM)
  // LOGICAL instructions
  `add_instr(XOR,    R_FORMAT, LOGICAL, RV32I)
  `add_instr(XORI,   I_FORMAT, LOGICAL, RV32I)
  `add_instr(OR,     R_FORMAT, LOGICAL, RV32I)
  `add_instr(ORI,    I_FORMAT, LOGICAL, RV32I)
  `add_instr(AND,    R_FORMAT, LOGICAL, RV32I)
  `add_instr(ANDI,   I_FORMAT, LOGICAL, RV32I)
  // COMPARE instructions
  `add_instr(SLT,    R_FORMAT, COMPARE, RV32I)
  `add_instr(SLTI,   I_FORMAT, COMPARE, RV32I)
  `add_instr(SLTU,   R_FORMAT, COMPARE, RV32I)
  `add_instr(SLTIU,  I_FORMAT, COMPARE, RV32I)
  // BRANCH instructions
  `add_instr(BEQ,    B_FORMAT, BRANCH, RV32I)
  `add_instr(BNE,    B_FORMAT, BRANCH, RV32I)
  `add_instr(BLT,    B_FORMAT, BRANCH, RV32I)
  `add_instr(BGE,    B_FORMAT, BRANCH, RV32I)
  `add_instr(BLTU,   B_FORMAT, BRANCH, RV32I)
  `add_instr(BGEU,   B_FORMAT, BRANCH, RV32I)
  // JUMP instructions
  `add_instr(JAL,    J_FORMAT, JUMP, RV32I)
  `add_instr(JALR,   I_FORMAT, JUMP, RV32I)
  // SYNCH instructions
  `add_instr(FENCE,   I_FORMAT, SYNCH, RV32I)
  `add_instr(FENCE_I,  I_FORMAT, SYNCH, RV32I)
  // SYSTEM instructions
  `add_instr(ECALL,   I_FORMAT, SYSTEM, RV32I)
  `add_instr(EBREAK,  I_FORMAT, SYSTEM, RV32I)
  `add_instr(URET,    I_FORMAT, SYSTEM, RV32I)
  `add_instr(SRET,    I_FORMAT, SYSTEM, RV32I)
  `add_instr(MRET,    I_FORMAT, SYSTEM, RV32I)
  `add_instr(DRET,    I_FORMAT, SYSTEM, RV32I)
  `add_instr(WFI,     I_FORMAT, INTERRUPT, RV32I)
  // CSR instructions
  `add_instr(CSRRW,  R_FORMAT, CSR, RV32I, UIMM)
  `add_instr(CSRRS,  R_FORMAT, CSR, RV32I, UIMM)
  `add_instr(CSRRC,  R_FORMAT, CSR, RV32I, UIMM)
  `add_instr(CSRRWI, I_FORMAT, CSR, RV32I, UIMM)
  `add_instr(CSRRSI, I_FORMAT, CSR, RV32I, UIMM)
  `add_instr(CSRRCI, I_FORMAT, CSR, RV32I, UIMM)

  ////////////  RV32M instructions  //////////////
  `add_instr(MUL,    R_FORMAT, ARITHMETIC, RV32M)
  `add_instr(MULH,   R_FORMAT, ARITHMETIC, RV32M)
  `add_instr(MULHSU, R_FORMAT, ARITHMETIC, RV32M)
  `add_instr(MULHU,  R_FORMAT, ARITHMETIC, RV32M)
  `add_instr(DIV,    R_FORMAT, ARITHMETIC, RV32M)
  `add_instr(DIVU,   R_FORMAT, ARITHMETIC, RV32M)
  `add_instr(REM,    R_FORMAT, ARITHMETIC, RV32M)
  `add_instr(REMU,   R_FORMAT, ARITHMETIC, RV32M)

  ////////////  RV64M instructions  //////////////
  `add_instr(MULW,   R_FORMAT, ARITHMETIC, RV64M)
  `add_instr(DIVW,   R_FORMAT, ARITHMETIC, RV64M)
  `add_instr(DIVUW,  R_FORMAT, ARITHMETIC, RV64M)
  `add_instr(REMW,   R_FORMAT, ARITHMETIC, RV64M)
  `add_instr(REMUW,  R_FORMAT, ARITHMETIC, RV64M)

  ////////////  RV32F instructions  //////////////
  `add_instr(FLW,       I_FORMAT, LOAD, RV32F)
  `add_instr(FSW,       S_FORMAT, STORE, RV32F)
  `add_instr(FMADD_S,   R4_FORMAT, ARITHMETIC, RV32F)
  `add_instr(FMSUB_S,   R4_FORMAT, ARITHMETIC, RV32F)
  `add_instr(FNMSUB_S,  R4_FORMAT, ARITHMETIC, RV32F)
  `add_instr(FNMADD_S,  R4_FORMAT, ARITHMETIC, RV32F)
  `add_instr(FADD_S,    R_FORMAT, ARITHMETIC, RV32F)
  `add_instr(FSUB_S,    R_FORMAT, ARITHMETIC, RV32F)
  `add_instr(FMUL_S,    R_FORMAT, ARITHMETIC, RV32F)
  `add_instr(FDIV_S,    R_FORMAT, ARITHMETIC, RV32F)
  `add_instr(FSQRT_S,   I_FORMAT, ARITHMETIC, RV32F)
  `add_instr(FSGNJ_S,   R_FORMAT, ARITHMETIC, RV32F)
  `add_instr(FSGNJN_S,  R_FORMAT, ARITHMETIC, RV32F)
  `add_instr(FSGNJX_S,  R_FORMAT, ARITHMETIC, RV32F)
  `add_instr(FMIN_S,    R_FORMAT, ARITHMETIC, RV32F)
  `add_instr(FMAX_S,    R_FORMAT, ARITHMETIC, RV32F)
  `add_instr(FCVT_W_S,  I_FORMAT, ARITHMETIC, RV32F)
  `add_instr(FCVT_WU_S, I_FORMAT, ARITHMETIC, RV32F)
  `add_instr(FMV_X_W,   I_FORMAT, ARITHMETIC, RV32F)
  `add_instr(FEQ_S,     R_FORMAT, COMPARE, RV32F)
  `add_instr(FLT_S,     R_FORMAT, COMPARE, RV32F)
  `add_instr(FLE_S,     R_FORMAT, COMPARE, RV32F)
  `add_instr(FCLASS_S,  R_FORMAT, ARITHMETIC, RV32F)
  `add_instr(FCVT_S_W,  I_FORMAT, ARITHMETIC, RV32F)
  `add_instr(FCVT_S_WU, I_FORMAT, ARITHMETIC, RV32F)
  `add_instr(FMV_W_X,   I_FORMAT, ARITHMETIC, RV32F)

  /////////////  RV64F instruction /////////////////
  `add_instr(FCVT_L_S,  I_FORMAT, ARITHMETIC, RV64F)
  `add_instr(FCVT_LU_S, I_FORMAT, ARITHMETIC, RV64F)
  `add_instr(FCVT_S_L,  I_FORMAT, ARITHMETIC, RV64F)
  `add_instr(FCVT_S_LU, I_FORMAT, ARITHMETIC, RV64F)

  ////////////  RV32D instructions  ////////////////
  `add_instr(FLD,       I_FORMAT, LOAD, RV32D)
  `add_instr(FSD,       S_FORMAT, STORE, RV32D)
  `add_instr(FMADD_D,   R4_FORMAT, ARITHMETIC, RV32D)
  `add_instr(FMSUB_D,   R4_FORMAT, ARITHMETIC, RV32D)
  `add_instr(FNMSUB_D,  R4_FORMAT, ARITHMETIC, RV32D)
  `add_instr(FNMADD_D,  R4_FORMAT, ARITHMETIC, RV32D)
  `add_instr(FADD_D,    R_FORMAT, ARITHMETIC, RV32D)
  `add_instr(FSUB_D,    R_FORMAT, ARITHMETIC, RV32D)
  `add_instr(FMUL_D,    R_FORMAT, ARITHMETIC, RV32D)
  `add_instr(FDIV_D,    R_FORMAT, ARITHMETIC, RV32D)
  `add_instr(FSQRT_D,   I_FORMAT, ARITHMETIC, RV32D)
  `add_instr(FSGNJ_D,   R_FORMAT, ARITHMETIC, RV32D)
  `add_instr(FSGNJN_D,  R_FORMAT, ARITHMETIC, RV32D)
  `add_instr(FSGNJX_D,  R_FORMAT, ARITHMETIC, RV32D)
  `add_instr(FMIN_D,    R_FORMAT, ARITHMETIC, RV32D)
  `add_instr(FMAX_D,    R_FORMAT, ARITHMETIC, RV32D)
  `add_instr(FCVT_S_D,  I_FORMAT, ARITHMETIC, RV32D)
  `add_instr(FCVT_D_S,  I_FORMAT, ARITHMETIC, RV32D)
  `add_instr(FEQ_D,     R_FORMAT, COMPARE, RV32D)
  `add_instr(FLT_D,     R_FORMAT, COMPARE, RV32D)
  `add_instr(FLE_D,     R_FORMAT, COMPARE, RV32D)
  `add_instr(FCLASS_D,  R_FORMAT, ARITHMETIC, RV32D)
  `add_instr(FCVT_W_D,  I_FORMAT, ARITHMETIC, RV32D)
  `add_instr(FCVT_WU_D, I_FORMAT, ARITHMETIC, RV32D)
  `add_instr(FCVT_D_W,  I_FORMAT, ARITHMETIC, RV32D)
  `add_instr(FCVT_D_WU, I_FORMAT, ARITHMETIC, RV32D)

  //////////////  RV64D instruction  ///////////////
  `add_instr(FMV_X_D,   I_FORMAT, ARITHMETIC, RV64D)
  `add_instr(FMV_D_X,   I_FORMAT, ARITHMETIC, RV64D)
  `add_instr(FCVT_L_D,  I_FORMAT, ARITHMETIC, RV64D)
  `add_instr(FCVT_LU_D, I_FORMAT, ARITHMETIC, RV64D)
  `add_instr(FCVT_D_L,  I_FORMAT, ARITHMETIC, RV64D)
  `add_instr(FCVT_D_LU, I_FORMAT, ARITHMETIC, RV64D)

  // RV64I instructions
  // LOAD/STORE instructions
  `add_instr(LWU,     I_FORMAT, LOAD, RV64I)
  `add_instr(LD,      I_FORMAT, LOAD, RV64I)
  `add_instr(SD,      S_FORMAT, STORE, RV64I)
  // SHIFT intructions
  `add_instr(SLLW,    R_FORMAT, SHIFT, RV64I)
  `add_instr(SLLIW,   I_FORMAT, SHIFT, RV64I)
  `add_instr(SRLW,    R_FORMAT, SHIFT, RV64I)
  `add_instr(SRLIW,   I_FORMAT, SHIFT, RV64I)
  `add_instr(SRAW,    R_FORMAT, SHIFT, RV64I)
  `add_instr(SRAIW,   I_FORMAT, SHIFT, RV64I)
  // ARITHMETIC intructions
  `add_instr(ADDW,    R_FORMAT, ARITHMETIC, RV64I)
  `add_instr(ADDIW,   I_FORMAT, ARITHMETIC, RV64I)
  `add_instr(SUBW,    R_FORMAT, ARITHMETIC, RV64I)

  // RV32IC
  `add_instr(C_LW,       CL_FORMAT, LOAD, RV32C, UIMM)
  `add_instr(C_SW,       CS_FORMAT, STORE, RV32C, UIMM)
  `add_instr(C_LWSP,     CI_FORMAT, LOAD, RV32C, UIMM)
  `add_instr(C_SWSP,     CSS_FORMAT, STORE, RV32C, UIMM)
  `add_instr(C_ADDI4SPN, CIW_FORMAT, ARITHMETIC, RV32C, NZUIMM)
  `add_instr(C_ADDI,     CI_FORMAT, ARITHMETIC, RV32C, NZIMM)
  `add_instr(C_ADDI16SP, CI_FORMAT, ARITHMETIC, RV32C, NZIMM)
  `add_instr(C_LI,       CI_FORMAT, ARITHMETIC, RV32C)
  `add_instr(C_LUI,      CI_FORMAT, ARITHMETIC, RV32C, NZUIMM)
  `add_instr(C_SUB,      CA_FORMAT, ARITHMETIC, RV32C)
  `add_instr(C_ADD,      CR_FORMAT, ARITHMETIC, RV32C)
  `add_instr(C_NOP,      CI_FORMAT, ARITHMETIC, RV32C)
  `add_instr(C_MV,       CR_FORMAT, ARITHMETIC, RV32C)
  `add_instr(C_ANDI,     CB_FORMAT, LOGICAL, RV32C)
  `add_instr(C_XOR,      CA_FORMAT, LOGICAL, RV32C)
  `add_instr(C_OR,       CA_FORMAT, LOGICAL, RV32C)
  `add_instr(C_AND,      CA_FORMAT, LOGICAL, RV32C)
  `add_instr(C_BEQZ,     CB_FORMAT, BRANCH, RV32C)
  `add_instr(C_BNEZ,     CB_FORMAT, BRANCH, RV32C)
  `add_instr(C_SRLI,     CB_FORMAT, SHIFT, RV32C, NZUIMM)
  `add_instr(C_SRAI,     CB_FORMAT, SHIFT, RV32C, NZUIMM)
  `add_instr(C_SLLI,     CI_FORMAT, SHIFT, RV32C, NZUIMM)
  `add_instr(C_J,        CJ_FORMAT, JUMP, RV32C)
  `add_instr(C_JAL,      CJ_FORMAT, JUMP, RV32C)
  `add_instr(C_JR,       CR_FORMAT, JUMP, RV32C)
  `add_instr(C_JALR,     CR_FORMAT, JUMP, RV32C)
  `add_instr(C_EBREAK,   CI_FORMAT, SYSTEM, RV32C)

  // RV64C
  `add_instr(C_ADDIW,  CI_FORMAT, ARITHMETIC, RV64C)
  `add_instr(C_SUBW,   CA_FORMAT, ARITHMETIC, RV64C)
  `add_instr(C_ADDW,   CA_FORMAT, ARITHMETIC, RV64C)
  `add_instr(C_LD,     CL_FORMAT, LOAD, RV64C, UIMM)
  `add_instr(C_SD,     CS_FORMAT, STORE, RV64C, UIMM)
  `add_instr(C_LDSP,   CI_FORMAT, LOAD, RV64C, UIMM)
  `add_instr(C_SDSP,   CSS_FORMAT, STORE, RV64C, UIMM)

  // RV128C
  `add_instr(C_SRLI64, CB_FORMAT, SHIFT, RV128C, NZUIMM)
  `add_instr(C_SRAI64, CB_FORMAT, SHIFT, RV128C, NZUIMM)
  `add_instr(C_SLLI64, CI_FORMAT, SHIFT, RV128C, NZUIMM)
  `add_instr(C_LQ,     CL_FORMAT, LOAD, RV32DC, UIMM)
  `add_instr(C_SQ,     CS_FORMAT, STORE, RV32DC, UIMM)
  `add_instr(C_LQSP,   CI_FORMAT, LOAD, RV32DC, UIMM)
  `add_instr(C_SQSP,   CSS_FORMAT, STORE, RV32DC, UIMM)

  // RV32FC
  `add_instr(C_FLW,   CL_FORMAT, LOAD, RV32FC, UIMM)
  `add_instr(C_FSW,   CS_FORMAT, STORE, RV32FC, UIMM)
  `add_instr(C_FLWSP, CI_FORMAT, LOAD, RV32FC, UIMM)
  `add_instr(C_FSWSP, CSS_FORMAT, STORE, RV32FC, UIMM)

  // RV32DC
  `add_instr(C_FLD,   CL_FORMAT, LOAD, RV32DC, UIMM)
  `add_instr(C_FSD,   CS_FORMAT, STORE, RV32DC, UIMM)
  `add_instr(C_FLDSP, CI_FORMAT, LOAD, RV32DC, UIMM)
  `add_instr(C_FSDSP, CSS_FORMAT, STORE, RV32DC, UIMM)

  // RV32A
  `add_instr(LR_W,      R_FORMAT, LOAD, RV32A)
  `add_instr(SC_W,      R_FORMAT, STORE, RV32A)
  `add_instr(AMOSWAP_W, R_FORMAT, AMO, RV32A)
  `add_instr(AMOADD_W,  R_FORMAT, AMO, RV32A)
  `add_instr(AMOAND_W,  R_FORMAT, AMO, RV32A)
  `add_instr(AMOOR_W,   R_FORMAT, AMO, RV32A)
  `add_instr(AMOXOR_W,  R_FORMAT, AMO, RV32A)
  `add_instr(AMOMIN_W,  R_FORMAT, AMO, RV32A)
  `add_instr(AMOMAX_W,  R_FORMAT, AMO, RV32A)
  `add_instr(AMOMINU_W, R_FORMAT, AMO, RV32A)
  `add_instr(AMOMAXU_W, R_FORMAT, AMO, RV32A)

  // RV64A
  `add_instr(LR_D,      R_FORMAT, LOAD, RV64A)
  `add_instr(SC_D,      R_FORMAT, STORE, RV64A)
  `add_instr(AMOSWAP_D, R_FORMAT, AMO, RV64A)
  `add_instr(AMOADD_D,  R_FORMAT, AMO, RV64A)
  `add_instr(AMOAND_D,  R_FORMAT, AMO, RV64A)
  `add_instr(AMOOR_D,   R_FORMAT, AMO, RV64A)
  `add_instr(AMOXOR_D,  R_FORMAT, AMO, RV64A)
  `add_instr(AMOMIN_D,  R_FORMAT, AMO, RV64A)
  `add_instr(AMOMAX_D,  R_FORMAT, AMO, RV64A)
  `add_instr(AMOMINU_D, R_FORMAT, AMO, RV64A)
  `add_instr(AMOMAXU_D, R_FORMAT, AMO, RV64A)

  // Supervisor Instructions
  `add_instr(SFENCE_VMA, R_FORMAT,SYNCH,RV32I)


  // -------------------------------------------------------------------------
  //  Section 7. Vector Loads and Stores
  // -------------------------------------------------------------------------
  // Section 7.4 - Vector Unit-Stride Instructions
  `add_instr(VLE_V, VL_FORMAT, LOAD, RVV)
  `add_instr(VSE_V, VS_FORMAT, STORE, RVV)
  `add_instr(VLB_V, VL_FORMAT, LOAD, RVV)
  `add_instr(VSB_V, VS_FORMAT, STORE, RVV)
  `add_instr(VLH_V, VL_FORMAT, LOAD, RVV)
  `add_instr(VSH_V, VS_FORMAT, STORE, RVV)
  `add_instr(VLW_V, VL_FORMAT, LOAD, RVV)
  `add_instr(VSW_V, VS_FORMAT, STORE, RVV)
  `add_instr(VLBU_V, VL_FORMAT, LOAD, RVV)
  `add_instr(VLHU_V, VS_FORMAT, LOAD, RVV)
  `add_instr(VLWU_V, VL_FORMAT, LOAD, RVV)
  // Section 7.5 - Vector Strided Instructions
  `add_instr(VLSB_V, VLS_FORMAT, LOAD, RVV)
  `add_instr(VLSH_V, VLS_FORMAT, LOAD, RVV)
  `add_instr(VLSW_V, VLS_FORMAT, LOAD, RVV)
  `add_instr(VLSBU_V, VLS_FORMAT, LOAD, RVV)
  `add_instr(VLSHU_V, VLS_FORMAT, LOAD, RVV)
  `add_instr(VLSWU_V, VLS_FORMAT, LOAD, RVV)
  `add_instr(VLSE_V, VLS_FORMAT, LOAD, RVV)
  `add_instr(VSSB_V, VSS_FORMAT, STORE, RVV)
  `add_instr(VSSH_V, VSS_FORMAT, STORE, RVV)
  `add_instr(VSSW_V, VSS_FORMAT, STORE, RVV)
  `add_instr(VSSE_V, VSS_FORMAT, STORE, RVV)
  // Section 7.6 - Vector Indexed Instructions
  `add_instr(VLXB_V, VLV_FORMAT, LOAD, RVV)
  `add_instr(VLXH_V, VLV_FORMAT, LOAD, RVV)
  `add_instr(VLXW_V, VLV_FORMAT, LOAD, RVV)
  `add_instr(VLXBU_V, VLV_FORMAT, LOAD, RVV)
  `add_instr(VLXHU_V, VLV_FORMAT, LOAD, RVV)
  `add_instr(VLXWU_V, VLV_FORMAT, LOAD, RVV)
  `add_instr(VLXE_V, VLV_FORMAT, LOAD, RVV)
  `add_instr(VSXB_V, VSV_FORMAT, STORE, RVV)
  `add_instr(VSXH_V, VSV_FORMAT, STORE, RVV)
  `add_instr(VSXW_V, VSV_FORMAT, STORE, RVV)
  `add_instr(VSXE_V, VSV_FORMAT, STORE, RVV)
  `add_instr(VSUXB_V, VSV_FORMAT, STORE, RVV)
  `add_instr(VSUXH_V, VSV_FORMAT, STORE, RVV)
  `add_instr(VSUXW_V, VSV_FORMAT, STORE, RVV)
  `add_instr(VSUXE_V, VSV_FORMAT, STORE, RVV)
  // Section 7.7 - Vector Unit-Stride Fault-Only-First Loads
  `add_instr(VLBFF_V, VL_FORMAT, LOAD, RVV)
  `add_instr(VLHFF_V, VL_FORMAT, LOAD, RVV)
  `add_instr(VLWFF_V, VL_FORMAT, LOAD, RVV)
  `add_instr(VLBUFF_V, VL_FORMAT, LOAD, RVV)
  `add_instr(VLHUFF_V, VL_FORMAT, LOAD, RVV)
  `add_instr(VLWUFF_V, VL_FORMAT, LOAD, RVV)
  `add_instr(VLEFF_V, VL_FORMAT, LOAD, RVV)

  // -------------------------------------------------------------------------
  //  Section 8. Vector AMO Operations (Zvamo)
  // -------------------------------------------------------------------------
  // 32-bit vector AMOs
  `add_instr(VAMOSWAPW_V, VAMO_FORMAT, AMO, RVV)
  `add_instr(VAMOADDW_V, VAMO_FORMAT, AMO, RVV)
  `add_instr(VAMOXORW_V, VAMO_FORMAT, AMO, RVV)
  `add_instr(VAMOANDW_V, VAMO_FORMAT, AMO, RVV)
  `add_instr(VAMOORW_V, VAMO_FORMAT, AMO, RVV)
  `add_instr(VAMOMINW_V, VAMO_FORMAT, AMO, RVV)
  `add_instr(VAMOMAXW_V, VAMO_FORMAT, AMO, RVV)
  `add_instr(VAMOMINUW_V, VAMO_FORMAT, AMO, RVV)
  `add_instr(VAMOMAXUW_V, VAMO_FORMAT, AMO, RVV)
  // SEW-bit Vector AMO
  `add_instr(VAMOSWAPE_V, VAMO_FORMAT, AMO, RVV)
  `add_instr(VAMOADDE_V, VAMO_FORMAT, AMO, RVV)
  `add_instr(VAMOXORE_V, VAMO_FORMAT, AMO, RVV)
  `add_instr(VAMOANDE_V, VAMO_FORMAT, AMO, RVV)
  `add_instr(VAMOORE_V, VAMO_FORMAT, AMO, RVV)
  `add_instr(VAMOMINE_V, VAMO_FORMAT, AMO, RVV)
  `add_instr(VAMOMAXE_V, VAMO_FORMAT, AMO, RVV)
  `add_instr(VAMOMINUE_V, VAMO_FORMAT, AMO, RVV)
  `add_instr(VAMOMAXUE_V, VAMO_FORMAT, AMO, RVV)

  // -------------------------------------------------------------------------
  //  Section 12. Vector Integer Arithmetic Instructions
  // -------------------------------------------------------------------------
  // Section 12.1 - Vector Single-Width Integer Add and Subtract
  `add_instr(VADD_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VADD_VX, VX_FORMAT, ARITHMETIC, RVV)
  `add_instr(VADD_VI, VI_FORMAT, ARITHMETIC, RVV, IMM)
  `add_instr(VSUB_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VSUB_VX, VX_FORMAT, ARITHMETIC, RVV)
  `add_instr(VRSUB_VX, VX_FORMAT, ARITHMETIC, RVV)
  `add_instr(VRSUB_VI, VI_FORMAT, ARITHMETIC, RVV, IMM)
  // Section 12.2 - Vector Widening Integer Add/Subtract
  `add_instr(VWADDU_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VWADDU_VX, VX_FORMAT, ARITHMETIC, RVV)
  `add_instr(VWSUBU_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VWSUBU_VX, VX_FORMAT, ARITHMETIC, RVV)
  `add_instr(VWADD_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VWADD_VX, VX_FORMAT, ARITHMETIC, RVV)
  `add_instr(VWSUB_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VWSUB_VX, VX_FORMAT, ARITHMETIC, RVV)
  `add_instr(VWADDU_WV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VWADDU_WX, VX_FORMAT, ARITHMETIC, RVV)
  `add_instr(VWSUBU_WV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VWSUBU_WX, VX_FORMAT, ARITHMETIC, RVV)
  `add_instr(VWADD_WV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VWADD_WX, VX_FORMAT, ARITHMETIC, RVV)
  `add_instr(VWSUB_WV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VWSUB_WX, VX_FORMAT, ARITHMETIC, RVV)
  // Section 12.3 - Vector Integer Add-with-Carry / Subtract-with-Borrow Instructions
  `add_instr(VADC_VVM, VV1_FORMAT, ARITHMETIC, RVV)
  `add_instr(VADC_VXM, VX1_FORMAT, ARITHMETIC, RVV)
  `add_instr(VADC_VIM, VI1_FORMAT, ARITHMETIC, RVV, IMM)
  `add_instr(VMADC_VVM, VV1_FORMAT, ARITHMETIC, RVV)
  `add_instr(VMADC_VXM, VX1_FORMAT, ARITHMETIC, RVV)
  `add_instr(VMADC_VIM, VI1_FORMAT, ARITHMETIC, RVV, IMM)
  `add_instr(VMADC_VV, VV5_FORMAT, ARITHMETIC, RVV)
  `add_instr(VMADC_VX, VX5_FORMAT, ARITHMETIC, RVV)
  `add_instr(VMADC_VI, VI5_FORMAT, ARITHMETIC, RVV, IMM)
  `add_instr(VSBC_VVM, VV1_FORMAT, ARITHMETIC, RVV)
  `add_instr(VSBC_VXM, VX1_FORMAT, ARITHMETIC, RVV)
  `add_instr(VMSBC_VVM, VV1_FORMAT, ARITHMETIC, RVV)
  `add_instr(VMSBC_VXM, VX1_FORMAT, ARITHMETIC, RVV)
  `add_instr(VMSBC_VV, VV5_FORMAT, ARITHMETIC, RVV)
  `add_instr(VMSBC_VX, VX5_FORMAT, ARITHMETIC, RVV)
  // Section 12.4 - Vector Bitwise Logical Instructions
  `add_instr(VAND_VV, VV_FORMAT, LOGICAL, RVV)
  `add_instr(VAND_VX, VX_FORMAT, LOGICAL, RVV)
  `add_instr(VAND_VI, VI_FORMAT, LOGICAL, RVV, IMM)
  `add_instr(VOR_VV, VV_FORMAT, LOGICAL, RVV)
  `add_instr(VOR_VX, VX_FORMAT, LOGICAL, RVV)
  `add_instr(VOR_VI, VI_FORMAT, LOGICAL, RVV, IMM)
  `add_instr(VXOR_VV, VV_FORMAT, LOGICAL, RVV)
  `add_instr(VXOR_VX, VX_FORMAT, LOGICAL, RVV)
  `add_instr(VXOR_VI, VI_FORMAT, LOGICAL, RVV, IMM)
  // Section 12.5 - Vector Single-Width Bit Shift Instructions
  `add_instr(VSLL_VV, VV_FORMAT, SHIFT, RVV)
  `add_instr(VSLL_VX, VX_FORMAT, SHIFT, RVV)
  `add_instr(VSLL_VI, VI_FORMAT, SHIFT, RVV, UIMM)
  `add_instr(VSRL_VV, VV_FORMAT, SHIFT, RVV)
  `add_instr(VSRL_VX, VX_FORMAT, SHIFT, RVV)
  `add_instr(VSRL_VI, VI_FORMAT, SHIFT, RVV, UIMM)
  `add_instr(VSRA_VV, VV_FORMAT, SHIFT, RVV)
  `add_instr(VSRA_VX, VX_FORMAT, SHIFT, RVV)
  `add_instr(VSRA_VI, VI_FORMAT, SHIFT, RVV, UIMM)
  // Section 12.6 - Vector Narrowing Integer Right Shift Instructions
  `add_instr(VNSRL_WV, VV_FORMAT, SHIFT, RVV)
  `add_instr(VNSRL_WX, VX_FORMAT, SHIFT, RVV)
  `add_instr(VNSRL_WI, VI_FORMAT, SHIFT, RVV, UIMM)
  `add_instr(VNSRA_WV, VV_FORMAT, SHIFT, RVV)
  `add_instr(VNSRA_WX, VX_FORMAT, SHIFT, RVV)
  `add_instr(VNSRA_WI, VI_FORMAT, SHIFT, RVV, UIMM)
  // Section 12.7 - Vector Integer Comparison Instructions
  `add_instr(VMSEQ_VV, VV_FORMAT, COMPARE, RVV)
  `add_instr(VMSEQ_VX, VX_FORMAT, COMPARE, RVV)
  `add_instr(VMSEQ_VI, VI_FORMAT, COMPARE, RVV, IMM)
  `add_instr(VMSNE_VV, VV_FORMAT, COMPARE, RVV)
  `add_instr(VMSNE_VX, VX_FORMAT, COMPARE, RVV)
  `add_instr(VMSNE_VI, VI_FORMAT, COMPARE, RVV, IMM)
  `add_instr(VMSLTU_VV, VV_FORMAT, COMPARE, RVV)
  `add_instr(VMSLTU_VX, VX_FORMAT, COMPARE, RVV)
  `add_instr(VMSLT_VV, VV_FORMAT, COMPARE, RVV)
  `add_instr(VMSLT_VX, VX_FORMAT, COMPARE, RVV)
  `add_instr(VMSLEU_VV, VV_FORMAT, COMPARE, RVV)
  `add_instr(VMSLEU_VX, VX_FORMAT, COMPARE, RVV)
  `add_instr(VMSLEU_VI, VI_FORMAT, COMPARE, RVV, IMM)
  `add_instr(VMSLE_VV, VV_FORMAT, COMPARE, RVV)
  `add_instr(VMSLE_VX, VX_FORMAT, COMPARE, RVV)
  `add_instr(VMSLE_VI, VI_FORMAT, COMPARE, RVV, IMM)
  `add_instr(VMSGTU_VX, VX_FORMAT, COMPARE, RVV)
  `add_instr(VMSGTU_VI, VI_FORMAT, COMPARE, RVV, IMM)
  `add_instr(VMSGT_VX, VX_FORMAT, COMPARE, RVV)
  `add_instr(VMSGT_VI, VI_FORMAT, COMPARE, RVV, IMM)
  // Section 12.8 - Vector Integer Min/Max Instructions
  `add_instr(VMINU_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VMINU_VX, VX_FORMAT, ARITHMETIC, RVV)
  `add_instr(VMIN_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VMIN_VX, VX_FORMAT, ARITHMETIC, RVV)
  `add_instr(VMAXU_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VMAXU_VX, VX_FORMAT, ARITHMETIC, RVV)
  `add_instr(VMAX_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VMAX_VX, VX_FORMAT, ARITHMETIC, RVV)
  // Section 12.9 - Vector Single-Width Integer Multiply Instructions
  `add_instr(VMUL_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VMUL_VX, VX_FORMAT, ARITHMETIC, RVV)
  `add_instr(VMULH_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VMULH_VX, VX_FORMAT, ARITHMETIC, RVV)
  `add_instr(VMULHU_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VMULHU_VX, VX_FORMAT, ARITHMETIC, RVV)
  `add_instr(VMULHSU_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VMULHSU_VX, VX_FORMAT, ARITHMETIC, RVV)
  // Section 12.10 - Vector Integer Divide Instructions
  `add_instr(VDIVU_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VDIVU_VX, VX_FORMAT, ARITHMETIC, RVV)
  `add_instr(VDIV_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VDIV_VX, VX_FORMAT, ARITHMETIC, RVV)
  `add_instr(VREMU_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VREMU_VX, VX_FORMAT, ARITHMETIC, RVV)
  `add_instr(VREM_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VREM_VX, VX_FORMAT, ARITHMETIC, RVV)
  // Section 12.11 - Vector Widening Integer Multiply Instructions
  `add_instr(VWMUL_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VWMUL_VX, VX_FORMAT, ARITHMETIC, RVV)
  `add_instr(VWMULU_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VWMULU_VX, VX_FORMAT, ARITHMETIC, RVV)
  `add_instr(VWMULSU_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VWMULSU_VX, VX_FORMAT, ARITHMETIC, RVV)
  // Section 12.12 - Vector Single-Width Integer Multiply-Add Instructions
  `add_instr(VMACC_VV, VV2_FORMAT, ARITHMETIC, RVV)
  `add_instr(VMACC_VX, VX2_FORMAT, ARITHMETIC, RVV)
  `add_instr(VNMSAC_VV, VV2_FORMAT, ARITHMETIC, RVV)
  `add_instr(VNMSAC_VX, VX2_FORMAT, ARITHMETIC, RVV)
  `add_instr(VMADD_VV, VV2_FORMAT, ARITHMETIC, RVV)
  `add_instr(VMADD_VX, VX2_FORMAT, ARITHMETIC, RVV)
  `add_instr(VNMSUB_VV, VV2_FORMAT, ARITHMETIC, RVV)
  `add_instr(VNMSUB_VX, VX2_FORMAT, ARITHMETIC, RVV)
  // Section 12.13 - Vector Widening Integer Multiply-Add Instructions
  `add_instr(VWMACCU_VV, VV2_FORMAT, ARITHMETIC, RVV)
  `add_instr(VWMACCU_VX, VX2_FORMAT, ARITHMETIC, RVV)
  `add_instr(VWMACC_VV, VV2_FORMAT, ARITHMETIC, RVV)
  `add_instr(VWMACC_VX, VX2_FORMAT, ARITHMETIC, RVV)
  `add_instr(VWMACCSU_VV, VV2_FORMAT, ARITHMETIC, RVV)
  `add_instr(VWMACCSU_VX, VX2_FORMAT, ARITHMETIC, RVV)
  `add_instr(VWMACCUS_VX, VX2_FORMAT, ARITHMETIC, RVV)
  // Section 12.14 - Vector Quad-Widening Integer Multiply-Add Instructions
  `add_instr(VQMACCU_VV, VV2_FORMAT, ARITHMETIC, RVV)
  `add_instr(VQMACCU_VX, VX2_FORMAT, ARITHMETIC, RVV)
  `add_instr(VQMACC_VV, VV2_FORMAT, ARITHMETIC, RVV)
  `add_instr(VQMACC_VX, VX2_FORMAT, ARITHMETIC, RVV)
  `add_instr(VQMACCSU_VV, VV2_FORMAT, ARITHMETIC, RVV)
  `add_instr(VQMACCSU_VX, VX2_FORMAT, ARITHMETIC, RVV)
  `add_instr(VQMACCUS_VX, VX2_FORMAT, ARITHMETIC, RVV)
  // Section 12.15 - Vector Integer Merge Instructions
  `add_instr(VMERGE_VVM, VV1_FORMAT, ARITHMETIC, RVV)
  `add_instr(VMERGE_VXM, VX1_FORMAT, ARITHMETIC, RVV)
  `add_instr(VMERGE_VIM, VI1_FORMAT, ARITHMETIC, RVV, IMM)
  // Section 12.16 - Vector Integer Move Instructions
  `add_instr(VMV_V_V, VV3_FORMAT, ARITHMETIC, RVV)
  `add_instr(VMV_V_X, VX3_FORMAT, ARITHMETIC, RVV)
  `add_instr(VMV_V_I, VI3_FORMAT, ARITHMETIC, RVV, IMM)
  // -------------------------------------------------------------------------
  //  Section 13. Vector Fixed-Point Arithmetic Instructions
  // -------------------------------------------------------------------------
  // Section 13.1 - Vector Single-Width Saturating Add and Subtract
  `add_instr(VSADDU_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VSADDU_VX, VX_FORMAT, ARITHMETIC, RVV)
  `add_instr(VSADDU_VI, VI_FORMAT, ARITHMETIC, RVV, IMM)
  `add_instr(VSADD_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VSADD_VX, VX_FORMAT, ARITHMETIC, RVV)
  `add_instr(VSADD_VI, VI_FORMAT, ARITHMETIC, RVV, IMM)
  `add_instr(VSSUBU_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VSSUBU_VX, VX_FORMAT, ARITHMETIC, RVV)
  `add_instr(VSSUB_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VSSUB_VX, VX_FORMAT, ARITHMETIC, RVV)
  // Section 13.2 - Vector Single-Width Averaging Add and Subtract
  `add_instr(VAADDU_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VAADDU_VX, VX_FORMAT, ARITHMETIC, RVV)
  `add_instr(VAADD_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VAADD_VX, VX_FORMAT, ARITHMETIC, RVV)
  `add_instr(VASUBU_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VASUBU_VX, VX_FORMAT, ARITHMETIC, RVV)
  `add_instr(VASUB_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VASUB_VX, VX_FORMAT, ARITHMETIC, RVV)
  // Section 13.3 - Vector Single-Width Fractional Multiply with Rounding and Saturation
  `add_instr(VSMUL_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VSMUL_VX, VX_FORMAT, ARITHMETIC, RVV)
  // Section 13.4 - Vector Single-Width Scaling Shift Instructions
  `add_instr(VSSRL_VV, VV_FORMAT, SHIFT, RVV)
  `add_instr(VSSRL_VX, VX_FORMAT, SHIFT, RVV)
  `add_instr(VSSRL_VI, VI_FORMAT, SHIFT, RVV, UIMM)
  `add_instr(VSSRA_VV, VV_FORMAT, SHIFT, RVV)
  `add_instr(VSSRA_VX, VX_FORMAT, SHIFT, RVV)
  `add_instr(VSSRA_VI, VI_FORMAT, SHIFT, RVV, UIMM)
  // Section 13.5 - Vector Narrowing Fixed-Point Clip Instructions
  `add_instr(VNCLIPU_WV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VNCLIPU_WX, VX_FORMAT, ARITHMETIC, RVV)
  `add_instr(VNCLIPU_WI, VI_FORMAT, ARITHMETIC, RVV, UIMM)
  `add_instr(VNCLIP_WV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VNCLIP_WX, VX_FORMAT, ARITHMETIC, RVV)
  `add_instr(VNCLIP_WI, VI_FORMAT, ARITHMETIC, RVV, UIMM)
  // -------------------------------------------------------------------------
  //  Section 14. Vector Floating-Point Instructions
  // -------------------------------------------------------------------------
  // Section 14.2 - Vector Single-Width Floating-Point Add/Subtract Instructions
  `add_instr(VFADD_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFADD_VF, VF_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFSUB_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFSUB_VF, VF_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFRSUB_VF, VF_FORMAT, ARITHMETIC, RVV)
  // Section 14.3 - Vector Widening Floating-Point Add/Subtract Instructions
  `add_instr(VFWADD_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFWADD_VF, VF_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFWSUB_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFWSUB_VF, VF_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFWADD_WV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFWADD_WF, VF_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFWSUB_WV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFWSUB_WF, VF_FORMAT, ARITHMETIC, RVV)
  // Section 14.4 - Vector Single-Width Floating-Point Multiply/Divide Instructions
  `add_instr(VFMUL_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFMUL_VF, VF_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFDIV_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFDIV_VF, VF_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFRDIV_VF, VF_FORMAT, ARITHMETIC, RVV)
  // Section 14.5 - Vector Widening Floating-Point Multiply
  `add_instr(VFWMUL_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFWMUL_VF, VF_FORMAT, ARITHMETIC, RVV)
  // Section 14.6 - Vector Single-Width Floating-Point Fused Multiply-Add Instructions
  `add_instr(VFMACC_VV, VV2_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFMACC_VF, VF2_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFNMACC_VV, VV2_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFNMACC_VF, VF2_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFMSAC_VV, VV2_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFMSAC_VF, VF2_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFNMSAC_VV, VV2_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFNMSAC_VF, VF2_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFMADD_VV, VV2_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFMADD_VF, VF2_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFNMADD_VV, VV2_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFNMADD_VF, VF2_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFMSUB_VV, VV2_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFMSUB_VF, VF2_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFNMSUB_VV, VV2_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFNMSUB_VF, VF2_FORMAT, ARITHMETIC, RVV)
  // Section 14.7 - Vector Widening Floating-Point Fused Multiply-Add Instructions
  `add_instr(VFWMACC_VV, VV2_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFWMACC_VF, VF2_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFWNMACC_VV, VV2_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFWNMACC_VF, VF2_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFWMSAC_VV, VV2_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFWMSAC_VF, VF2_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFWNMSAC_VV, VV2_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFWNMSAC_VF, VF2_FORMAT, ARITHMETIC, RVV)
  // Section 14.8 - Vector Floating-Point Square-Root Instructions
  `add_instr(VFSQRT_V, VV4_FORMAT, ARITHMETIC, RVV)
  // Section 14.9 - Vector Floating-Point MIN/MAX Instructions
  `add_instr(VFMIN_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFMIN_VF, VF_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFMAX_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFMAX_VF, VF_FORMAT, ARITHMETIC, RVV)
  // Section 14.10 - Vector Floating-Point Sign-Injection Instructions
  `add_instr(VFSGNJ_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFSGNJ_VF, VF_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFSGNJN_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFSGNJN_VF, VF_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFSGNJX_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFSGNJX_VF, VF_FORMAT, ARITHMETIC, RVV)
  // Section 14.11 - Vector Floating-Point Compare Instructions
  `add_instr(VMFEQ_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VMFEQ_VF, VF_FORMAT, ARITHMETIC, RVV)
  `add_instr(VMFNE_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VMFNE_VF, VF_FORMAT, ARITHMETIC, RVV)
  `add_instr(VMFLT_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VMFLT_VF, VF_FORMAT, ARITHMETIC, RVV)
  `add_instr(VMFLE_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VMFLE_VF, VF_FORMAT, ARITHMETIC, RVV)
  `add_instr(VMFGT_VF, VF_FORMAT, ARITHMETIC, RVV)
  `add_instr(VMFGE_VF, VF_FORMAT, ARITHMETIC, RVV)
  // Section 14.12 - Vector Floating-Point Classify Instruction
  `add_instr(VFCLASS_V, VV4_FORMAT, ARITHMETIC, RVV)
  // Section 14.13 - Vector Floating-Point Merge Instruction
  `add_instr(VFMERGE_VFM, VF1_FORMAT, ARITHMETIC, RVV)
  // Section 14.14 - Vector Floating-Point Move Instruction
  `add_instr(VFMV_V_F, VF3_FORMAT, ARITHMETIC, RVV)
  // Section 14.15 - Single-Width Floating-Point/Integer Type-Convert Instructions
  `add_instr(VFCVT_XU_F_V, VV4_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFCVT_X_F_V, VV4_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFCVT_F_XU_V, VV4_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFCVT_F_X_V, VV4_FORMAT, ARITHMETIC, RVV)
  // Section 14.16 - Widening Floating-Point/Integer Type-Convert Instructions
  `add_instr(VFWCVT_XU_F_V, VV4_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFWCVT_X_F_V, VV4_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFWCVT_F_XU_V, VV4_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFWCVT_F_X_V, VV4_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFWCVT_F_F_V, VV4_FORMAT, ARITHMETIC, RVV)
  // Section 14.17 - Narrowing Floating-Point/Integer Type-Convert Instructions
  `add_instr(VFNCVT_XU_F_W, VV4_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFNCVT_X_F_W, VV4_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFNCVT_F_XU_W, VV4_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFNCVT_F_X_W, VV4_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFNCVT_F_F_W, VV4_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFNCVT_ROD_F_F_W, VV4_FORMAT, ARITHMETIC, RVV)
  // -------------------------------------------------------------------------
  //  Section 15. Vector Reduction Operations
  // -------------------------------------------------------------------------
  // Section 15.1 - Vector Single-Width Integer Reduction Instructions
  `add_instr(VREDSUM_VS, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VREDMAXU_VS, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VREDMAX_VS, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VREDMINU_VS, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VREDMIN_VS, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VREDAND_VS, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VREDOR_VS, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VREDXOR_VS, VV_FORMAT, ARITHMETIC, RVV)
  // Section 15.2 - Vector Widening Integer Reduction Instructions
  `add_instr(VWREDSUMU_VS, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VWREDSUM_VS, VV_FORMAT, ARITHMETIC, RVV)
  // Section 15.3 - Vector Single-Width Floating-Point Reduction Instructions
  `add_instr(VFREDOSUM_VS, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFREDSUM_VS, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFREDMAX_VS, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFREDMIN_VS, VV_FORMAT, ARITHMETIC, RVV)
  // Section 15.4 - Vector Widening Floating-Point Reduction Instructions
  `add_instr(VFWREDOSUM_VS, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFWREDSUM_VS, VV_FORMAT, ARITHMETIC, RVV)
  // -------------------------------------------------------------------------
  //  Section 16. Vector Mask Instructions
  // -------------------------------------------------------------------------
  // Section 16.1 - Vector Mask-Register Logical Instructions
  `add_instr(VMAND_MM, VV5_FORMAT, LOGICAL, RVV)
  `add_instr(VMNAND_MM, VV5_FORMAT, LOGICAL, RVV)
  `add_instr(VMANDNOT_MM, VV5_FORMAT, LOGICAL, RVV)
  `add_instr(VMXOR_MM, VV5_FORMAT, LOGICAL, RVV)
  `add_instr(VMOR_MM, VV5_FORMAT, LOGICAL, RVV)
  `add_instr(VMNOR_MM, VV5_FORMAT, LOGICAL, RVV)
  `add_instr(VMORNOT_MM, VV5_FORMAT, LOGICAL, RVV)
  `add_instr(VMXNOR_MM, VV5_FORMAT, LOGICAL, RVV)
  // Section 16.2 - Vector Mask Population Count vpopc
  `add_instr(VPOPC_M, VV6_FORMAT, ARITHMETIC, RVV)
  // Section 16.3 - vfirst find-first-set mask bit
  `add_instr(VFIRST_M, VV6_FORMAT, ARITHMETIC, RVV)
  // Section 16.4 - VMSBF.M Set-Before-First Mask Bit
  `add_instr(VMSBF_M, VV4_FORMAT, ARITHMETIC, RVV)
  // Section 16.5 - VMSIF.M Set-Including-First Mask Bit
  `add_instr(VMSIF_M, VV4_FORMAT, ARITHMETIC, RVV)
  // Section 16.6 - VMSOF.M Set-Only-First Mask Bit
  `add_instr(VMSOF_M, VV4_FORMAT, ARITHMETIC, RVV)
  // Section 16.8 - Vector Iota Instruction
  `add_instr(VIOTA_M, VV4_FORMAT, ARITHMETIC, RVV)
  // Section 16.9 - Vector Element Index Instruction
  `add_instr(VID_V, VV7_FORMAT, ARITHMETIC, RVV)
  // -------------------------------------------------------------------------
  //  Section 17. Vector Permutation Instructions
  // -------------------------------------------------------------------------
  // Section 17.1 - Integer Scalar Move Instruction
  `add_instr(VMV_X_S, VV8_FORMAT, ARITHMETIC, RVV)
  `add_instr(VMV_S_X, VX3_FORMAT, ARITHMETIC, RVV)
  // Section 17.2 - Floating-Point Scalar Move Instruction
  `add_instr(VFMV_F_S, VF4_FORMAT, ARITHMETIC, RVV)
  `add_instr(VFMV_S_F, VF3_FORMAT, ARITHMETIC, RVV)
  // Section 17.3.1 - Vector Slideup Instruction
  `add_instr(VSLIDEUP_VX, VX_FORMAT, ARITHMETIC, RVV)
  `add_instr(VSLIDEUP_VI, VI_FORMAT, ARITHMETIC, RVV, UIMM)
  // Section 17.3.2 - Vector Slidedown Instruction
  `add_instr(VSLIDEDOWN_VX, VX_FORMAT, ARITHMETIC, RVV)
  `add_instr(VSLIDEDOWN_VI, VI_FORMAT, ARITHMETIC, RVV, UIMM)
  // Section 17.3.3 - Vector Slide1up
  `add_instr(VSLIDE1UP_VX, VX_FORMAT, ARITHMETIC, RVV)
  // Section 17.3.4 - Vector Slide1down Instruction
  `add_instr(VSLIDE1DOWN_VX, VX_FORMAT, ARITHMETIC, RVV)
  // Section 17.4 - Vector Register Gather Instruction
  `add_instr(VRGATHER_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VRGATHER_VX, VX_FORMAT, ARITHMETIC, RVV)
  `add_instr(VRGATHER_VI, VI_FORMAT, ARITHMETIC, RVV, UIMM)
  // Section 17.5 - Vector Compress Instruction
  `add_instr(VCOMPRESS_VM, VV5_FORMAT, ARITHMETIC, RVV)
  // Section 17.6 - Whole Vector Register Move
  // -------------------------------------------------------------------------
  //  Section 19. Divided Element Extension ('Zvediv')
  // -------------------------------------------------------------------------
  // Section 19.3 - Vector Integer Dot-Product Instruction
  `add_instr(VDOTU_VV, VV_FORMAT, ARITHMETIC, RVV)
  `add_instr(VDOT_VV, VV_FORMAT, ARITHMETIC, RVV)
  // Section 19.4 - Vector Floating-Point Dot-Product Instruction
  `add_instr(VFDOT_VV, VV_FORMAT, ARITHMETIC, RVV)


  function void post_randomize();
    if (group inside {RV32C, RV64C, RV128C, RV32DC, RV32FC}) begin
      is_compressed = 1'b1;
    end
    if (!(format inside {R_FORMAT, CR_FORMAT})) begin
      imm_mask = '1;
      imm_mask = imm_mask << imm_len;
      has_imm = 1'b1;
      mask_imm();
      if (imm_str == "") begin
        update_imm_str();
      end
    end
    if (format inside {R_FORMAT, S_FORMAT, B_FORMAT, CSS_FORMAT,
                       CS_FORMAT, CR_FORMAT, CA_FORMAT}) begin
      has_rs2 = 1'b1;
    end
    if (!(format inside {J_FORMAT, U_FORMAT, CJ_FORMAT, CSS_FORMAT,
                         CA_FORMAT, CR_FORMAT, CI_FORMAT})) begin
      has_rs1 = 1'b1;
    end else if (instr_name inside {C_JR, C_JALR}) begin
      has_rs1 = 1'b1;
      has_rs2 = 1'b0;
    end
    if (!(format inside {CJ_FORMAT, CB_FORMAT, CS_FORMAT, CSS_FORMAT, B_FORMAT, S_FORMAT})) begin
      has_rd = 1'b1;
    end
    if (category == CSR) begin
      has_rs2 = 1'b0;
      if (instr_name inside {CSRRWI, CSRRSI, CSRRCI}) begin
        has_rs1 = 1'b0;
      end
    end
    // TODO(taliu) Add support for compressed floating point format
    if (group inside {RV32F, RV64F, RV32D, RV64D, RV32FC, RV32DC}) begin
      is_floating_point = 1'b1;
      has_rs1 = 1'b0;
      has_rs2 = 1'b0;
      has_rd  = 1'b0;
      has_fs1 = 1'b1;
      if (format == R4_FORMAT) begin
        has_fs3 = 1'b1;
      end
      if (format != S_FORMAT) begin
        if ((category == COMPARE) || (instr_name inside {FCLASS_S, FCLASS_D})) begin
          has_rd = 1'b1;
        end else begin
          has_fd = 1'b1;
        end
      end
      if (format != I_FORMAT) begin
        has_fs2 = 1'b1;
      end
      if (instr_name inside {FMV_X_W, FMV_X_D, FCVT_W_S, FCVT_WU_S,
                             FCVT_L_S, FCVT_LU_S, FCVT_L_D, FCVT_LU_D, FCVT_LU_S,
                             FCVT_W_D, FCVT_WU_D}) begin
        // Floating point to integer operation
        has_rd = 1'b1;
        has_fs1 = 1'b1;
        has_fd = 1'b0;
      end else if (instr_name inside {FMV_W_X, FMV_D_X, FCVT_S_W, FCVT_S_WU,
                                      FCVT_S_L, FCVT_D_L, FCVT_S_LU, FCVT_D_W,
                                      FCVT_D_LU, FCVT_D_WU, FLW, FLD, FSW, FSD,
                                      C_FLW, C_FLD, C_FSW, C_FSD}) begin
        // Integer to floating point operation
        has_fd = 1'b1;
        has_fs1 = 1'b0;
        has_rs1 = 1'b1;
      end
    end
  endfunction

  virtual function void mask_imm();
    // Process the immediate value and sign extension
    if (imm_type inside {UIMM, NZUIMM}) begin
      imm = imm & ~imm_mask;
    end else begin
      if (imm[imm_len-1]) begin
        imm = imm | imm_mask;
      end else begin
        imm = imm & ~imm_mask;
      end
    end
    // Give a random value if imm is zero after masking unexpectedly
    if((imm_type inside {NZIMM, NZUIMM}) && (imm == '0)) begin
      imm = $urandom_range(2 ** (imm_len-1) - 1, 1);
    end
  endfunction

  virtual function void gen_rand_fields(riscv_instr_gen_config cfg,
                                        riscv_reg_t avail_regs[]={}, riscv_reg_t cant_write_regs[]={},
                                        bit skip_rs1=0, bit skip_rs2=0, bit skip_rd=0, bit skip_imm=0, bit skip_csr=0);
    if (group == RVV) gen_rand_vec_args(cfg);
    if (has_imm && !skip_imm) gen_rand_imm();
    if (has_rs1 && !skip_rs1) gen_rand_rs1(cfg, avail_regs);
    if (has_rs2 && !skip_rs2) gen_rand_rs2(cfg, avail_regs);
    if (has_rd && !skip_rd) gen_rand_rd(cfg, avail_regs, cant_write_regs);
    if ((category == CSR) && !skip_csr) gen_rand_csr(cfg);
    if (has_fs1) gen_rand_fs1();
    if (has_fs2) gen_rand_fs2();
    if (has_fs3) gen_rand_fs3();
    if (has_fd) gen_rand_fd();
  endfunction

  virtual function void gen_rand_rs1(riscv_instr_gen_config cfg, riscv_reg_t avail_regs[]);
    rs1 = gen_rand_gpr(.included_reg(avail_regs),
                       .excluded_reg(is_compressed ? {reserved_rd, cfg.reserved_regs} : {}));
  endfunction

  virtual function void gen_rand_rs2(riscv_instr_gen_config cfg, riscv_reg_t avail_regs[]);
    rs2 = gen_rand_gpr(.included_reg(avail_regs));
  endfunction

  virtual function void gen_rand_rd(riscv_instr_gen_config cfg, riscv_reg_t avail_regs[], riscv_reg_t cant_write_regs[]);
    riscv_reg_t excld[] = {reserved_rd, cfg.reserved_regs, cant_write_regs};
    if (instr_name == C_LUI) excld = {excld, SP};
    rd = gen_rand_gpr(.included_reg(avail_regs), .excluded_reg(excld));
  endfunction

  virtual function void gen_rand_fs1(); fs1 = gen_rand_fpr(); endfunction
  virtual function void gen_rand_fs2(); fs2 = gen_rand_fpr(); endfunction
  virtual function void gen_rand_fs3(); fs3 = gen_rand_fpr(); endfunction
  virtual function void gen_rand_fd(); fd = gen_rand_fpr(); endfunction

  virtual function void gen_rand_imm();
    assert (randomize(imm)) else `uvm_fatal(`gfn, $sformatf("Cannot randomize imm for %s", instr_name.name()))
    mask_imm();
    update_imm_str();
  endfunction

  virtual function void update_imm_str();
    imm_str = $sformatf("%0d", $signed(imm));
  endfunction

  virtual function void set_imm(int imm);
    this.imm = imm;
    mask_imm();
    update_imm_str();
  endfunction

  virtual function riscv_reg_t gen_rand_gpr(riscv_reg_t included_reg[] = {}, riscv_reg_t excluded_reg[] = {});
    riscv_reg_t gpr;
    int unsigned i;
    riscv_reg_t legal_gpr[$];
    if (included_reg.size() > 0) begin
      legal_gpr = included_reg;
      if (is_compressed && !(format inside {CR_FORMAT, CI_FORMAT, CSS_FORMAT})) begin
        while (i < legal_gpr.size()) begin
          if (legal_gpr[i] < S0 || legal_gpr[i] > A5) begin
            legal_gpr.delete(i);
          end else begin
            i++;
          end
        end
      end
    end else if (is_compressed &&
                 !(format inside {CR_FORMAT, CI_FORMAT, CSS_FORMAT})) begin
      legal_gpr = riscv_instr_pkg::compressed_gpr;
    end else begin
      legal_gpr = riscv_instr_pkg::all_gpr;
    end
    if (format inside {CR_FORMAT, CI_FORMAT}) begin
      excluded_reg = {excluded_reg, ZERO};
    end
    if (excluded_reg.size() > 0) begin
      i = 0;
      while (i < legal_gpr.size()) begin
        if (legal_gpr[i] inside {excluded_reg}) begin
          legal_gpr.delete(i);
        end else begin
          i++;
        end
      end
    end
    `DV_CHECK_FATAL(legal_gpr.size() > 0)
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(i, i < legal_gpr.size();)
    gpr = legal_gpr[i];
    return gpr;
  endfunction

  virtual function riscv_fpr_t gen_rand_fpr(riscv_fpr_t excluded_reg[] = {});
    riscv_fpr_t fpr;
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(fpr,
                                       if (excluded_reg.size() > 0) {
                                         !(fpr inside {excluded_reg});
                                       }
                                       if (is_compressed) {
                                         fpr inside {[F8:F15]};
                                       });
    return fpr;
  endfunction

  virtual function void gen_rand_csr(riscv_instr_gen_config cfg);
    privileged_reg_t preg[$];
    if (cfg.enable_illegal_csr_instruction) begin
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(csr, !(csr inside {implemented_csr});)
    end else begin
      // Use scratch register to avoid the side effect of modifying other privileged mode CSR.
      if (cfg.init_privileged_mode == MACHINE_MODE)
        preg = {MSCRATCH};
      else if (cfg.init_privileged_mode == SUPERVISOR_MODE)
        preg = {SSCRATCH};
      else
        preg = {USCRATCH};
      if (cfg.enable_floating_point) begin
        preg = {preg, FFLAGS, FRM, FCSR};
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(csr, csr inside {preg};)
      end else begin
        csr = preg[0];
      end
    end
  endfunction

  virtual function void gen_rand_vec_args(riscv_instr_gen_config cfg);
    // TODO: set has_* fields to only generate needed regs
    calc_vec_reg_groups();
    gen_rand_vd(cfg);
    gen_rand_vs1(cfg);
    gen_rand_vs2(cfg);
    gen_rand_vs3(cfg);
    gen_rand_vm();
    gen_rand_wd();
    has_rd = 1;
    has_rs1 = 1;
    has_fd = 1;
    has_fs1 = 1;
  endfunction

  static riscv_vec_reg_t vec_reg_group_heads_lmul[int][$] = '{
      1:{riscv_all_vec_reg_q},
      2:{V0, V2, V4, V6, V8, V10, V12, V14, V16, V18, V20, V22, V24, V26, V28, V30},
      4:{V0, V4, V8, V12, V16, V20, V24, V28},
      8:{V0, V8, V16, V24},
      16:{V0, V16}
    };

  static riscv_vec_reg_t vec_regs_in_a_group[int][riscv_vec_reg_t][$] = '{
      1:'{V0:{V0}, V1:{V1}, V2:{V2}, V3:{V3}, V4:{V4}, V5:{V5}, V6:{V6}, V7:{V7}, V8:{V8}, V9:{V9}, V10:{V10},
          V11:{V11}, V12:{V12}, V13:{V13}, V14:{V14}, V15:{V15}, V16:{V16}, V17:{V17}, V18:{V18}, V19:{V19}, V20:{V20},
          V21:{V21}, V22:{V22}, V23:{V23}, V24:{V24}, V25:{V25}, V26:{V26}, V27:{V27}, V28:{V28}, V29:{V29}, V30:{V30},
          V31:{V31}},
      2:'{V0:{V0, V1}, V1:{V0, V1}, V2:{V2, V3}, V3:{V2, V3}, V4:{V4, V5}, V5:{V4, V5}, V6:{V6, V7}, V7:{V6, V7},
          V8:{V8, V9}, V9:{V8, V9}, V10:{V10, V11}, V11:{V10, V11}, V12:{V12, V13}, V13:{V12, V13},
          V14:{V14, V15}, V15:{V14, V15}, V16:{V16, V17}, V17:{V16, V17}, V18:{V18, V19}, V19:{V18, V19},
          V20:{V20, V21}, V21:{V20, V21}, V22:{V22, V23}, V23:{V22, V23}, V24:{V24, V25}, V25:{V24, V25},
          V26:{V26, V27}, V27:{V26, V27}, V28:{V28, V29}, V29:{V28, V29}, V30:{V30, V31}, V31:{V30, V31}},
      4:'{V0:{V0, V1, V2, V3}, V1:{V0, V1, V2, V3}, V2:{V0, V1, V2, V3}, V3:{V0, V1, V2, V3},
          V4:{V4, V5, V6, V7}, V5:{V4, V5, V6, V7}, V6:{V4, V5, V6, V7}, V7:{V4, V5, V6, V7},
          V8:{V8, V9, V10, V11}, V9:{V8, V9, V10, V11}, V10:{V8, V9, V10, V11}, V11:{V8, V9, V10, V11},
          V12:{V12, V13, V14, V15}, V13:{V12, V13, V14, V15}, V14:{V12, V13, V14, V15}, V15:{V12, V13, V14, V15},
          V16:{V16, V17, V18, V19}, V17:{V16, V17, V18, V19}, V18:{V16, V17, V18, V19}, V19:{V16, V17, V18, V19},
          V20:{V20, V21, V22, V23}, V21:{V20, V21, V22, V23}, V22:{V20, V21, V22, V23}, V23:{V20, V21, V22, V23},
          V24:{V24, V25, V26, V27}, V25:{V24, V25, V26, V27}, V26:{V24, V25, V26, V27}, V27:{V24, V25, V26, V27},
          V28:{V28, V29, V30, V31}, V29:{V28, V29, V30, V31}, V30:{V28, V29, V30, V31}, V31:{V28, V29, V30, V31}},
      8:'{V0:{V0, V1, V2, V3, V4, V5, V6, V7}, V1:{V0, V1, V2, V3, V4, V5, V6, V7}, V2:{V0, V1, V2, V3, V4, V5, V6, V7},
          V3:{V0, V1, V2, V3, V4, V5, V6, V7}, V4:{V0, V1, V2, V3, V4, V5, V6, V7}, V5:{V0, V1, V2, V3, V4, V5, V6, V7},
          V6:{V0, V1, V2, V3, V4, V5, V6, V7}, V7:{V0, V1, V2, V3, V4, V5, V6, V7},
          V8:{V8, V9, V10, V11, V12, V13, V14, V15}, V9:{V8, V9, V10, V11, V12, V13, V14, V15},
          V10:{V8, V9, V10, V11, V12, V13, V14, V15}, V11:{V8, V9, V10, V11, V12, V13, V14, V15},
          V12:{V8, V9, V10, V11, V12, V13, V14, V15}, V13:{V8, V9, V10, V11, V12, V13, V14, V15},
          V14:{V8, V9, V10, V11, V12, V13, V14, V15}, V15:{V8, V9, V10, V11, V12, V13, V14, V15},
          V16:{V16, V17, V18, V19, V20, V21, V22, V23}, V17:{V16, V17, V18, V19, V20, V21, V22, V23},
          V18:{V16, V17, V18, V19, V20, V21, V22, V23}, V19:{V16, V17, V18, V19, V20, V21, V22, V23},
          V20:{V16, V17, V18, V19, V20, V21, V22, V23}, V21:{V16, V17, V18, V19, V20, V21, V22, V23},
          V22:{V16, V17, V18, V19, V20, V21, V22, V23}, V23:{V16, V17, V18, V19, V20, V21, V22, V23},
          V24:{V24, V25, V26, V27, V28, V29, V30, V31}, V25:{V24, V25, V26, V27, V28, V29, V30, V31},
          V26:{V24, V25, V26, V27, V28, V29, V30, V31}, V27:{V24, V25, V26, V27, V28, V29, V30, V31},
          V28:{V24, V25, V26, V27, V28, V29, V30, V31}, V29:{V24, V25, V26, V27, V28, V29, V30, V31},
          V30:{V24, V25, V26, V27, V28, V29, V30, V31}, V31:{V24, V25, V26, V27, V28, V29, V30, V31}},
      16:'{V0:{V0, V1, V2, V3, V4, V5, V6, V7, V8, V9, V10, V11, V12, V13, V14, V15},
           V1:{V0, V1, V2, V3, V4, V5, V6, V7, V8, V9, V10, V11, V12, V13, V14, V15},
           V2:{V0, V1, V2, V3, V4, V5, V6, V7, V8, V9, V10, V11, V12, V13, V14, V15},
           V3:{V0, V1, V2, V3, V4, V5, V6, V7, V8, V9, V10, V11, V12, V13, V14, V15},
           V4:{V0, V1, V2, V3, V4, V5, V6, V7, V8, V9, V10, V11, V12, V13, V14, V15},
           V5:{V0, V1, V2, V3, V4, V5, V6, V7, V8, V9, V10, V11, V12, V13, V14, V15},
           V6:{V0, V1, V2, V3, V4, V5, V6, V7, V8, V9, V10, V11, V12, V13, V14, V15},
           V7:{V0, V1, V2, V3, V4, V5, V6, V7, V8, V9, V10, V11, V12, V13, V14, V15},
           V8:{V0, V1, V2, V3, V4, V5, V6, V7, V8, V9, V10, V11, V12, V13, V14, V15},
           V9:{V0, V1, V2, V3, V4, V5, V6, V7, V8, V9, V10, V11, V12, V13, V14, V15},
           V10:{V0, V1, V2, V3, V4, V5, V6, V7, V8, V9, V10, V11, V12, V13, V14, V15},
           V11:{V0, V1, V2, V3, V4, V5, V6, V7, V8, V9, V10, V11, V12, V13, V14, V15},
           V12:{V0, V1, V2, V3, V4, V5, V6, V7, V8, V9, V10, V11, V12, V13, V14, V15},
           V13:{V0, V1, V2, V3, V4, V5, V6, V7, V8, V9, V10, V11, V12, V13, V14, V15},
           V14:{V0, V1, V2, V3, V4, V5, V6, V7, V8, V9, V10, V11, V12, V13, V14, V15},
           V15:{V0, V1, V2, V3, V4, V5, V6, V7, V8, V9, V10, V11, V12, V13, V14, V15},
           V16:{V16, V17, V18, V19, V20, V21, V22, V23, V24, V25, V26, V27, V28, V29, V30, V31},
           V17:{V16, V17, V18, V19, V20, V21, V22, V23, V24, V25, V26, V27, V28, V29, V30, V31},
           V18:{V16, V17, V18, V19, V20, V21, V22, V23, V24, V25, V26, V27, V28, V29, V30, V31},
           V19:{V16, V17, V18, V19, V20, V21, V22, V23, V24, V25, V26, V27, V28, V29, V30, V31},
           V20:{V16, V17, V18, V19, V20, V21, V22, V23, V24, V25, V26, V27, V28, V29, V30, V31},
           V21:{V16, V17, V18, V19, V20, V21, V22, V23, V24, V25, V26, V27, V28, V29, V30, V31},
           V22:{V16, V17, V18, V19, V20, V21, V22, V23, V24, V25, V26, V27, V28, V29, V30, V31},
           V23:{V16, V17, V18, V19, V20, V21, V22, V23, V24, V25, V26, V27, V28, V29, V30, V31},
           V24:{V16, V17, V18, V19, V20, V21, V22, V23, V24, V25, V26, V27, V28, V29, V30, V31},
           V25:{V16, V17, V18, V19, V20, V21, V22, V23, V24, V25, V26, V27, V28, V29, V30, V31},
           V26:{V16, V17, V18, V19, V20, V21, V22, V23, V24, V25, V26, V27, V28, V29, V30, V31},
           V27:{V16, V17, V18, V19, V20, V21, V22, V23, V24, V25, V26, V27, V28, V29, V30, V31},
           V28:{V16, V17, V18, V19, V20, V21, V22, V23, V24, V25, V26, V27, V28, V29, V30, V31},
           V29:{V16, V17, V18, V19, V20, V21, V22, V23, V24, V25, V26, V27, V28, V29, V30, V31},
           V30:{V16, V17, V18, V19, V20, V21, V22, V23, V24, V25, V26, V27, V28, V29, V30, V31},
           V31:{V16, V17, V18, V19, V20, V21, V22, V23, V24, V25, V26, V27, V28, V29, V30, V31}}
    };

  riscv_vec_reg_t src_grp_heads[$];
  riscv_vec_reg_t dst_grp_heads[$];
  riscv_vec_reg_t vs2_widening_grp_heads[$];
  riscv_vec_reg_t vd_group[$];
  bit is_narrowing, is_vs2_widening, no_vec_src_dst_overlap, vd_cant_be_mask, no_mask_dst_overlap;
  int widening_shift;

  virtual function void calc_vec_reg_groups();
    widening_shift = instr_name inside {vec_widening_instr};
    widening_shift = instr_name inside {vec_quad_widening_instr} ? 2 : widening_shift;
    is_narrowing = instr_name inside {vec_narrowing_instr};
    is_vs2_widening = instr_name inside {vec_widening_vs2};
    vd_cant_be_mask = LMUL > 1 && instr_name inside {vec_forced_mask_instr};
    no_vec_src_dst_overlap = (instr_name inside {vec_illegal_src_dest_overlap_instr})
                             || (LMUL > 1 && instr_name inside {vec_no_src_dst_overlap_with_lmul});
    no_mask_dst_overlap = instr_name inside {vec_illegal_mask_dest_overlap_instr};
    dst_grp_heads = vec_reg_group_heads_lmul[LMUL << widening_shift];
    src_grp_heads = vec_reg_group_heads_lmul[LMUL << is_narrowing];
    vs2_widening_grp_heads = vec_reg_group_heads_lmul[LMUL << is_vs2_widening];
  endfunction

  virtual function void gen_rand_vd(riscv_instr_gen_config cfg);
    riscv_vec_reg_t hzd[$] = cfg.get_hazard_vec_reg_set();
    bit success = 0;
    int attempts = 0;
    while (!success && attempts < 2) begin
      success = std::randomize(vd) with {
          vd inside {hzd};
          vd inside {dst_grp_heads};
          if (vd_cant_be_mask) vd != V0;
        };
      attempts++;
      hzd = riscv_all_vec_reg_q;
    end
    assert (success) else begin
      `uvm_fatal(`gfn, $sformatf({"gen_rand_vd failed:\ninstr_name:%s",
        "\nLMUL:%0d\nwidening_shift:%0d\nis_narrowing:%0d\nvd_cant_be_mask:%0d\ndst_grp_heads:%p"},
        instr_name.name(), LMUL, widening_shift, is_narrowing, vd_cant_be_mask, dst_grp_heads))
    end
    vd_group = vec_regs_in_a_group[LMUL << max_shift()][vd];
    cfg.build_hazard_vec_reg_set(vd);
  endfunction

  virtual function int max_shift();
    if (widening_shift > is_narrowing) return widening_shift;
    return is_narrowing;
  endfunction

  virtual function void gen_rand_vs1(riscv_instr_gen_config cfg);
    vs1 = get_rand_src_reg(cfg);
  endfunction

  virtual function void gen_rand_vs2(riscv_instr_gen_config cfg);
    vs2 = get_rand_src_reg(cfg, 1);
  endfunction

  virtual function void gen_rand_vs3(riscv_instr_gen_config cfg);
    vs3 = get_rand_src_reg(cfg);
  endfunction

  virtual function riscv_vec_reg_t get_rand_src_reg(riscv_instr_gen_config cfg, bit is_vs2=0);
    riscv_vec_reg_t hzd[$] = cfg.get_hazard_vec_reg_set();
    bit success = 0;
    int attempts = 0;

    // If we can't successfully generate with the list of hazard registers,
    // try again without it.
    while (!success && attempts < 2) begin
      success = std::randomize(get_rand_src_reg) with {
          get_rand_src_reg inside {hzd};
          if (is_vs2 && is_vs2_widening) {
            get_rand_src_reg inside {vs2_widening_grp_heads};
          } else {
            get_rand_src_reg inside {src_grp_heads};
          }
          if (no_vec_src_dst_overlap) {!(get_rand_src_reg inside {vd_group});}
        };
      attempts++;
      hzd = riscv_all_vec_reg_q;
    end
    assert (success) else begin
      `uvm_fatal(`gfn, $sformatf({"get_rand_src_reg failed:\ninstr_name:%s\nis_vs2:%0d",
        "\nLMUL:%0d\widening_shift:%0d\nis_vs2_widening:%0d\nis_narrowing:%0d\nno_vec_src_dst_overlap:%0d",
        "\nsrc_grp_heads:%p\nvs2_widening_grp_heads:%p\nvd_group:%p\n\n"},
        instr_name.name(), is_vs2,
        LMUL,widening_shift, is_vs2_widening, is_narrowing, no_vec_src_dst_overlap,
        src_grp_heads, vs2_widening_grp_heads, vd_group))
    end
    cfg.build_hazard_vec_reg_set(get_rand_src_reg);
  endfunction

  virtual function void gen_rand_vm();
    bit success = std::randomize(vm) with {
        if (LMUL > 1 && vd == V0) {vm;} // RVV spec section 5.3
        if (widening_shift && vd == V0) {vm;} // RVV spec section 11.2
        if (no_mask_dst_overlap && vd == V0) {vm;}
      };
    assert (success) else begin
      `uvm_fatal(`gfn, $sformatf({"gen_rand_vm failed:",
        "\ninstr_name:%s\nLMUL:%0d\nvd:%s\widening_shift:%0d\nno_mask_dst_overlap:%0d\n\n"},
        instr_name.name(), LMUL, vd.name(),widening_shift, no_mask_dst_overlap))
    end
  endfunction

  virtual function void gen_rand_wd();
    bit success = std::randomize(wd);
    assert (success) else begin
      `uvm_fatal(`gfn, $sformatf({"gen_rand_wd failed:", "\ninstr_name:%s"}, instr_name.name()))
    end
  endfunction

  function new(string name = "");
    super.new(name);
  endfunction

  // Convert the instruction to one-liner print message
  virtual function string convert2string();
    return convert2asm();
  endfunction

  virtual function void do_print (uvm_printer printer);
    `uvm_info(get_type_name(), convert2string(), UVM_LOW)
  endfunction

  // Convert the instruction to assembly code
  virtual function string convert2asm(string prefix = "");
    string asm_str;
    asm_str = format_string(get_instr_name(), MAX_INSTR_STR_LEN);
    if (is_floating_point) begin
      case (format)
        I_FORMAT:
          if (category == LOAD) begin
            asm_str = $sformatf("%0s%0s, %0s(%0s)", asm_str, fd.name(), get_imm(), rs1.name());
          end else if (instr_name inside {FMV_X_W, FMV_X_D, FCVT_W_S, FCVT_WU_S,
                                          FCVT_L_S, FCVT_LU_S, FCVT_L_D, FCVT_LU_D, FCVT_LU_S,
                                          FCVT_W_D, FCVT_WU_D}) begin
            asm_str = $sformatf("%0s%0s, %0s", asm_str, rd.name(), fs1.name());
          end else if (instr_name inside {FMV_W_X, FMV_D_X, FCVT_S_W, FCVT_S_WU,
                                          FCVT_S_L, FCVT_D_L, FCVT_S_LU, FCVT_D_W,
                                          FCVT_D_LU, FCVT_D_WU}) begin
            asm_str = $sformatf("%0s%0s, %0s", asm_str, fd.name(), rs1.name());
          end else begin
            asm_str = $sformatf("%0s%0s, %0s", asm_str, fd.name(), fs1.name());
          end
        S_FORMAT:
          asm_str = $sformatf("%0s%0s, %0s(%0s)", asm_str, fs2.name(), get_imm(), rs1.name());
        R_FORMAT:
          if (category == COMPARE) begin
            asm_str = $sformatf("%0s%0s, %0s, %0s", asm_str, rd.name(), fs1.name(), fs2.name());
          end else if (instr_name inside {FCLASS_S, FCLASS_D}) begin
            asm_str = $sformatf("%0s%0s, %0s", asm_str, rd.name(), fs1.name());
          end else begin
            asm_str = $sformatf("%0s%0s, %0s, %0s", asm_str, fd.name(), fs1.name(), fs2.name());
          end
        R4_FORMAT:
          asm_str = $sformatf("%0s%0s, %0s, %0s, %0s", asm_str, fd.name(), fs1.name(),
                                                       fs2.name(), fs3.name());
        CL_FORMAT:
          asm_str = $sformatf("%0s%0s, %0s(%0s)", asm_str, fd.name(), get_imm(), rs1.name());
        CS_FORMAT:
          asm_str = $sformatf("%0s%0s, %0s(%0s)", asm_str, fs2.name(), get_imm(), rs1.name());
        default:
          `uvm_fatal(`gfn, $sformatf("Unsupported floating point format: %0s", format.name()))
      endcase
    end else if((category != SYSTEM) && !(group inside {RV32A, RV64A})) begin
      case(format)
        J_FORMAT, U_FORMAT : // instr rd,imm
          asm_str = $sformatf("%0s%0s, %0s", asm_str, rd.name(), get_imm());
        I_FORMAT: // instr rd,rs1,imm
          if(instr_name == NOP)
            asm_str = "nop";
          else if(instr_name == C_NOP)
            asm_str = "c.nop";
          else if(instr_name == WFI)
            asm_str = "wfi";
          else if(instr_name == FENCE)
            asm_str = $sformatf("fence"); // TODO: Support all fence combinations
          else if(instr_name == FENCE_I)
            asm_str = "fence.i";
          else if(category == LOAD) // Use psuedo instruction format
            asm_str = $sformatf("%0s%0s, %0s(%0s)", asm_str, rd.name(), get_imm(), rs1.name());
          else if(category == CSR)
            asm_str = $sformatf("%0s%0s, 0x%0x, %0s", asm_str, rd.name(), csr, get_imm());
          else
            asm_str = $sformatf("%0s%0s, %0s, %0s", asm_str, rd.name(), rs1.name(), get_imm());
        S_FORMAT, B_FORMAT: // instr rs1,rs2,imm
          if(category == STORE) // Use psuedo instruction format
            asm_str = $sformatf("%0s%0s, %0s(%0s)", asm_str, rs2.name(), get_imm(), rs1.name());
          else
            asm_str = $sformatf("%0s%0s, %0s, %0s", asm_str, rs1.name(), rs2.name(), get_imm());
        R_FORMAT: // instr rd,rs1,rs2
          if(category == CSR) begin
            asm_str = $sformatf("%0s%0s, 0x%0x, %0s", asm_str, rd.name(), csr, rs1.name());
          end else if(instr_name == SFENCE_VMA) begin
            asm_str = "sfence.vma x0, x0"; // TODO: Support all possible sfence
          end else begin
            asm_str = $sformatf("%0s%0s, %0s, %0s", asm_str, rd.name(), rs1.name(), rs2.name());
          end
        CI_FORMAT, CIW_FORMAT:
          if(instr_name == C_NOP)
            asm_str = "c.nop";
          else if(instr_name == C_ADDI16SP)
            asm_str = $sformatf("%0ssp, %0s", asm_str, get_imm());
          else
            asm_str = $sformatf("%0s%0s, %0s", asm_str, rd.name(), get_imm());
        CL_FORMAT:
          asm_str = $sformatf("%0s%0s, %0s(%0s)", asm_str, rd.name(), get_imm(), rs1.name());
        CS_FORMAT:
          if(category == STORE)
            asm_str = $sformatf("%0s%0s, %0s(%0s)", asm_str, rs2.name(), get_imm(), rs1.name());
          else
            asm_str = $sformatf("%0s%0s, %0s", asm_str, rs1.name(), rs2.name());
        CA_FORMAT:
          asm_str = $sformatf("%0s%0s, %0s", asm_str, rd.name(), rs2.name());
        CB_FORMAT:
          asm_str = $sformatf("%0s%0s, %0s", asm_str, rs1.name(), get_imm());
        CSS_FORMAT:
          asm_str = $sformatf("%0s%0s, %0s", asm_str, rs2.name(), get_imm());
        CR_FORMAT:
          if (instr_name inside {C_JR, C_JALR}) begin
            asm_str = $sformatf("%0s%0s", asm_str, rs1.name());
          end else begin
            asm_str = $sformatf("%0s%0s, %0s", asm_str, rd.name(), rs2.name());
          end
        CJ_FORMAT:
          asm_str = $sformatf("%0s%0s", asm_str, get_imm());

        VL_FORMAT:
          asm_str = $sformatf("%-10s %s, (%s)%s", vec_instr_name_to_str(), vec_reg_to_str(vd),
                                                  scalar_reg_to_str(rs1), vec_vm_str());
        VS_FORMAT:
          asm_str = $sformatf("%-10s %s, (%s)%s", vec_instr_name_to_str(), vec_reg_to_str(vs3),
                                                  scalar_reg_to_str(rs1), vec_vm_str());
        VLS_FORMAT:
          asm_str = $sformatf("%-10s %s, (%s), %s, %s", vec_instr_name_to_str(), vec_reg_to_str(vd),
                                                  scalar_reg_to_str(rs1), scalar_reg_to_str(rs2), vec_vm_str());
        VSS_FORMAT:
          asm_str = $sformatf("%-10s %s, (%s), %s, %s", vec_instr_name_to_str(), vec_reg_to_str(vs3),
                                                  scalar_reg_to_str(rs1), scalar_reg_to_str(rs2), vec_vm_str());
        VLV_FORMAT:
          asm_str = $sformatf("%-10s %s, (%s), %s, %s", vec_instr_name_to_str(), vec_reg_to_str(vd),
                                                  scalar_reg_to_str(rs1), vec_reg_to_str(vs2), vec_vm_str());
        VSV_FORMAT:
          asm_str = $sformatf("%-10s %s, (%s), %s, %s", vec_instr_name_to_str(), vec_reg_to_str(vs3),
                                                  scalar_reg_to_str(rs1), vec_reg_to_str(vs2), vec_vm_str());
        VV_FORMAT:
          asm_str = $sformatf("%-10s %s, %s, %s%s", vec_instr_name_to_str(), vec_reg_to_str(vd),
                                                    vec_reg_to_str(vs2), vec_reg_to_str(vs1), vec_vm_str());
        VX_FORMAT:
          asm_str = $sformatf("%-10s %s, %s, %s%s", vec_instr_name_to_str(), vec_reg_to_str(vd),
                                                    vec_reg_to_str(vs2), scalar_reg_to_str(rs1), vec_vm_str());
        VF_FORMAT:
          asm_str = $sformatf("%-10s %s, %s, %s%s", vec_instr_name_to_str(), vec_reg_to_str(vd),
                                                    vec_reg_to_str(vs2), float_reg_to_str(fs1), vec_vm_str());
        VI_FORMAT:
          asm_str = $sformatf("%-10s %s, %s, %s%s", vec_instr_name_to_str(), vec_reg_to_str(vd),
                                                    vec_reg_to_str(vs2), get_imm(), vec_vm_str());
        VV1_FORMAT:
          asm_str = $sformatf("%-10s %s, %s, %s, v0", vec_instr_name_to_str(), vec_reg_to_str(vd),
                                                      vec_reg_to_str(vs2), vec_reg_to_str(vs1));
        VX1_FORMAT:
          asm_str = $sformatf("%-10s %s, %s, %s, v0", vec_instr_name_to_str(), vec_reg_to_str(vd),
                                                      vec_reg_to_str(vs2), scalar_reg_to_str(rs1));
        VF1_FORMAT:
          asm_str = $sformatf("%-10s %s, %s, %s, v0", vec_instr_name_to_str(), vec_reg_to_str(vd),
                                                      vec_reg_to_str(vs2), float_reg_to_str(fs1));
        VI1_FORMAT:
          asm_str = $sformatf("%-10s %s, %s, %s, v0", vec_instr_name_to_str(), vec_reg_to_str(vd),
                                                      vec_reg_to_str(vs2), get_imm());
        VV2_FORMAT:
          asm_str = $sformatf("%-10s %s, %s, %s%s", vec_instr_name_to_str(), vec_reg_to_str(vd),
                                                    vec_reg_to_str(vs1), vec_reg_to_str(vs2), vec_vm_str());
        VX2_FORMAT:
          asm_str = $sformatf("%-10s %s, %s, %s%s", vec_instr_name_to_str(), vec_reg_to_str(vd),
                                                    scalar_reg_to_str(rs1), vec_reg_to_str(vs2), vec_vm_str());
        VF2_FORMAT:
          asm_str = $sformatf("%-10s %s, %s, %s%s", vec_instr_name_to_str(), vec_reg_to_str(vd),
                                                    float_reg_to_str(fs1), vec_reg_to_str(vs2), vec_vm_str());
        VV3_FORMAT:
          asm_str = $sformatf("%-10s %s, %s", vec_instr_name_to_str(), vec_reg_to_str(vd), vec_reg_to_str(vs1));
        VX3_FORMAT:
          asm_str = $sformatf("%-10s %s, %s", vec_instr_name_to_str(), vec_reg_to_str(vd), scalar_reg_to_str(rs1));
        VF3_FORMAT:
          asm_str = $sformatf("%-10s %s, %s", vec_instr_name_to_str(), vec_reg_to_str(vd), float_reg_to_str(fs1));
        VI3_FORMAT:
          asm_str = $sformatf("%-10s %s, %s", vec_instr_name_to_str(), vec_reg_to_str(vd), get_imm());
        VV4_FORMAT:
          asm_str = $sformatf("%-10s %s, %s%s", vec_instr_name_to_str(), vec_reg_to_str(vd),
                                                vec_reg_to_str(vs2), vec_vm_str());
        VV5_FORMAT:
          asm_str = $sformatf("%-10s %s, %s, %s", vec_instr_name_to_str(), vec_reg_to_str(vd),
                                                  vec_reg_to_str(vs2), vec_reg_to_str(vs1));
        VX5_FORMAT:
          asm_str = $sformatf("%-10s %s, %s, %s", vec_instr_name_to_str(), vec_reg_to_str(vd),
                                                  vec_reg_to_str(vs2), scalar_reg_to_str(rs1));
        VI5_FORMAT:
          asm_str = $sformatf("%-10s %s, %s, %s", vec_instr_name_to_str(), vec_reg_to_str(vd),
                                                  vec_reg_to_str(vs2), get_imm());
        VV6_FORMAT:
          asm_str = $sformatf("%-10s %s, %s%s", vec_instr_name_to_str(), rd.name(),
                                                vec_reg_to_str(vs2), vec_vm_str());
        VX6_FORMAT:
          asm_str = $sformatf("%-10s %s, %s, %s", vec_instr_name_to_str(), rd.name(),
                                                  vec_reg_to_str(vs2), scalar_reg_to_str(rs1));
        VV7_FORMAT:
          asm_str = $sformatf("%-10s %s%s", vec_instr_name_to_str(), vec_reg_to_str(vd), vec_vm_str());
        VF4_FORMAT:
          asm_str = $sformatf("%-10s %s, %s", vec_instr_name_to_str(), float_reg_to_str(fd), vec_reg_to_str(vs2));
        VV8_FORMAT:
          asm_str = $sformatf("%-10s %s, %s", vec_instr_name_to_str(), rd.name(), vec_reg_to_str(vs2));
        VAMO_FORMAT:
          asm_str = $sformatf("%-10s %s, (%s), %s, %s, %s", vec_instr_name_to_str(), vec_wd_str(0), scalar_reg_to_str(rs1), vec_reg_to_str(vs2), vec_wd_str(1), vec_vm_str());
      endcase
    end else if (group inside {RV32A, RV64A}) begin
      if (instr_name inside {LR_W, LR_D}) begin
        asm_str = $sformatf("%0s %0s, (%0s)", asm_str, rd.name(), rs1.name());
      end else begin
        asm_str = $sformatf("%0s %0s, %0s, (%0s)", asm_str, rd.name(), rs2.name(), rs1.name());
      end
    end else begin
      // For EBREAK,C.EBREAK, making sure pc+4 is a valid instruction boundary
      // This is needed to resume execution from epc+4 after ebreak handling
      if(instr_name == EBREAK) begin
        asm_str = ".4byte 0x00100073 # ebreak";
      end else if(instr_name == C_EBREAK) begin
        asm_str = "c.ebreak;c.nop;";
      end
    end
    if(comment != "")
      asm_str = {asm_str, " #",comment};
    return asm_str.tolower();
  endfunction

  virtual function bit [6:0] get_opcode();
    case (instr_name) inside
      LUI                                                          : get_opcode = 7'b0110111;
      AUIPC                                                        : get_opcode = 7'b0010111;
      JAL                                                          : get_opcode = 7'b1101111;
      JALR                                                         : get_opcode = 7'b1100111;
      BEQ, BNE, BLT, BGE, BLTU, BGEU                               : get_opcode = 7'b1100011;
      LB, LH, LW, LBU, LHU, LWU, LD                                : get_opcode = 7'b0000011;
      SB, SH, SW, SD                                               : get_opcode = 7'b0100011;
      ADDI, SLTI, SLTIU, XORI, ORI, ANDI, SLLI, SRLI, SRAI, NOP    : get_opcode = 7'b0010011;
      ADD, SUB, SLL, SLT, SLTU, XOR, SRL, SRA, OR, AND, MUL,
      MULH, MULHSU, MULHU, DIV, DIVU, REM, REMU                    : get_opcode = 7'b0110011;
      ADDIW, SLLIW, SRLIW, SRAIW                                   : get_opcode = 7'b0011011;
      MULH, MULHSU, MULHU, DIV, DIVU, REM, REMU                    : get_opcode = 7'b0110011;
      FENCE, FENCE_I                                               : get_opcode = 7'b0001111;
      ECALL, EBREAK, CSRRW, CSRRS, CSRRC, CSRRWI, CSRRSI, CSRRCI   : get_opcode = 7'b1110011;
      ADDW, SUBW, SLLW, SRLW, SRAW, MULW, DIVW, DIVUW, REMW, REMUW : get_opcode = 7'b0111011;
      ECALL, EBREAK, URET, SRET, MRET, DRET, WFI, SFENCE_VMA       : get_opcode = 7'b1110011;
      default : `uvm_fatal(`gfn, $sformatf("Unsupported instruction %0s", instr_name.name()))
    endcase
  endfunction

  // Get opcode for compressed instruction
  virtual function bit [1:0] get_c_opcode();
    case (instr_name) inside
      C_ADDI4SPN, C_FLD, C_FLD, C_LQ, C_LW, C_FLW,
      C_LD, C_FSD, C_SQ, C_SW, C_FSW, C_SD            : get_c_opcode = 2'b00;
      C_NOP, C_ADDI, C_JAL, C_ADDIW, C_LI, C_ADDI16SP,
      C_LUI, C_SRLI, C_SRLI64, C_SRAI, C_SRAI64,
      C_ANDI, C_SUB, C_XOR, C_OR, C_AND, C_SUBW,
      C_ADDW, C_J, C_BEQZ, C_BNEZ                     : get_c_opcode = 2'b01;
      C_SLLI, C_SLLI64, C_FLDSP, C_LQSP, C_LWSP,
      C_FLWSP, C_LDSP, C_JR, C_MV, C_EBREAK, C_JALR,
      C_ADD, C_FSDSP, C_SQSP, C_SWSP, C_FSWSP, C_SDSP : get_c_opcode = 2'b10;
      default : `uvm_fatal(`gfn, $sformatf("Unsupported instruction %0s", instr_name.name()))
    endcase
  endfunction

  virtual function bit [2:0] get_func3();
    case (instr_name) inside
      JALR       : get_func3 = 3'b000;
      BEQ        : get_func3 = 3'b000;
      BNE        : get_func3 = 3'b001;
      BLT        : get_func3 = 3'b100;
      BGE        : get_func3 = 3'b101;
      BLTU       : get_func3 = 3'b110;
      BGEU       : get_func3 = 3'b111;
      LB         : get_func3 = 3'b000;
      LH         : get_func3 = 3'b001;
      LW         : get_func3 = 3'b010;
      LBU        : get_func3 = 3'b100;
      LHU        : get_func3 = 3'b101;
      SB         : get_func3 = 3'b000;
      SH         : get_func3 = 3'b001;
      SW         : get_func3 = 3'b010;
      ADDI       : get_func3 = 3'b000;
      NOP        : get_func3 = 3'b000;
      SLTI       : get_func3 = 3'b010;
      SLTIU      : get_func3 = 3'b011;
      XORI       : get_func3 = 3'b100;
      ORI        : get_func3 = 3'b110;
      ANDI       : get_func3 = 3'b111;
      SLLI       : get_func3 = 3'b001;
      SRLI       : get_func3 = 3'b101;
      SRAI       : get_func3 = 3'b101;
      ADD        : get_func3 = 3'b000;
      SUB        : get_func3 = 3'b000;
      SLL        : get_func3 = 3'b001;
      SLT        : get_func3 = 3'b010;
      SLTU       : get_func3 = 3'b011;
      XOR        : get_func3 = 3'b100;
      SRL        : get_func3 = 3'b101;
      SRA        : get_func3 = 3'b101;
      OR         : get_func3 = 3'b110;
      AND        : get_func3 = 3'b111;
      FENCE      : get_func3 = 3'b000;
      FENCE_I    : get_func3 = 3'b001;
      ECALL      : get_func3 = 3'b000;
      EBREAK     : get_func3 = 3'b000;
      CSRRW      : get_func3 = 3'b001;
      CSRRS      : get_func3 = 3'b010;
      CSRRC      : get_func3 = 3'b011;
      CSRRWI     : get_func3 = 3'b101;
      CSRRSI     : get_func3 = 3'b110;
      CSRRCI     : get_func3 = 3'b111;
      LWU        : get_func3 = 3'b110;
      LD         : get_func3 = 3'b011;
      SD         : get_func3 = 3'b011;
      ADDIW      : get_func3 = 3'b000;
      SLLIW      : get_func3 = 3'b001;
      SRLIW      : get_func3 = 3'b101;
      SRAIW      : get_func3 = 3'b101;
      ADDW       : get_func3 = 3'b000;
      SUBW       : get_func3 = 3'b000;
      SLLW       : get_func3 = 3'b001;
      SRLW       : get_func3 = 3'b101;
      SRAW       : get_func3 = 3'b101;
      MUL        : get_func3 = 3'b000;
      MULH       : get_func3 = 3'b001;
      MULHSU     : get_func3 = 3'b010;
      MULHU      : get_func3 = 3'b011;
      DIV        : get_func3 = 3'b100;
      DIVU       : get_func3 = 3'b101;
      REM        : get_func3 = 3'b110;
      REMU       : get_func3 = 3'b111;
      MULW       : get_func3 = 3'b000;
      DIVW       : get_func3 = 3'b100;
      DIVUW      : get_func3 = 3'b101;
      REMW       : get_func3 = 3'b110;
      REMUW      : get_func3 = 3'b111;
      C_ADDI4SPN : get_func3 = 3'b000;
      C_FLD      : get_func3 = 3'b001;
      C_LQ       : get_func3 = 3'b001;
      C_LW       : get_func3 = 3'b010;
      C_FLW      : get_func3 = 3'b011;
      C_LD       : get_func3 = 3'b011;
      C_FSD      : get_func3 = 3'b101;
      C_SQ       : get_func3 = 3'b101;
      C_SW       : get_func3 = 3'b110;
      C_FSW      : get_func3 = 3'b111;
      C_SD       : get_func3 = 3'b111;
      C_NOP      : get_func3 = 3'b000;
      C_ADDI     : get_func3 = 3'b000;
      C_JAL      : get_func3 = 3'b001;
      C_ADDIW    : get_func3 = 3'b001;
      C_LI       : get_func3 = 3'b010;
      C_ADDI16SP : get_func3 = 3'b011;
      C_LUI      : get_func3 = 3'b011;
      C_SRLI     : get_func3 = 3'b100;
      C_SRLI64   : get_func3 = 3'b100;
      C_SRAI     : get_func3 = 3'b100;
      C_SRAI64   : get_func3 = 3'b100;
      C_ANDI     : get_func3 = 3'b100;
      C_SUB      : get_func3 = 3'b100;
      C_XOR      : get_func3 = 3'b100;
      C_OR       : get_func3 = 3'b100;
      C_AND      : get_func3 = 3'b100;
      C_SUBW     : get_func3 = 3'b100;
      C_ADDW     : get_func3 = 3'b100;
      C_J        : get_func3 = 3'b101;
      C_BEQZ     : get_func3 = 3'b110;
      C_BNEZ     : get_func3 = 3'b111;
      C_SLLI     : get_func3 = 3'b000;
      C_SLLI64   : get_func3 = 3'b000;
      C_FLDSP    : get_func3 = 3'b001;
      C_LQSP     : get_func3 = 3'b001;
      C_LWSP     : get_func3 = 3'b010;
      C_FLWSP    : get_func3 = 3'b011;
      C_LDSP     : get_func3 = 3'b011;
      C_JR       : get_func3 = 3'b100;
      C_MV       : get_func3 = 3'b100;
      C_EBREAK   : get_func3 = 3'b100;
      C_JALR     : get_func3 = 3'b100;
      C_ADD      : get_func3 = 3'b100;
      C_FSDSP    : get_func3 = 3'b101;
      C_SQSP     : get_func3 = 3'b101;
      C_SWSP     : get_func3 = 3'b110;
      C_FSWSP    : get_func3 = 3'b111;
      C_SDSP     : get_func3 = 3'b111;
      ECALL, EBREAK, URET, SRET, MRET, DRET, WFI, SFENCE_VMA : get_func3 = 3'b000;
      default : `uvm_fatal(`gfn, $sformatf("Unsupported instruction %0s", instr_name.name()))
    endcase
  endfunction

  virtual function bit [6:0] get_func7();
    case (instr_name)
      SLLI   : get_func7 = 7'b0000000;
      SRLI   : get_func7 = 7'b0000000;
      SRAI   : get_func7 = 7'b0100000;
      ADD    : get_func7 = 7'b0000000;
      SUB    : get_func7 = 7'b0100000;
      SLL    : get_func7 = 7'b0000000;
      SLT    : get_func7 = 7'b0000000;
      SLTU   : get_func7 = 7'b0000000;
      XOR    : get_func7 = 7'b0000000;
      SRL    : get_func7 = 7'b0000000;
      SRA    : get_func7 = 7'b0100000;
      OR     : get_func7 = 7'b0000000;
      AND    : get_func7 = 7'b0000000;
      FENCE  : get_func7 = 7'b0000000;
      FENCE_I : get_func7 = 7'b0000000;
      SLLIW  : get_func7 = 7'b0000000;
      SRLIW  : get_func7 = 7'b0000000;
      SRAIW  : get_func7 = 7'b0100000;
      ADDW   : get_func7 = 7'b0000000;
      SUBW   : get_func7 = 7'b0100000;
      SLLW   : get_func7 = 7'b0000000;
      SRLW   : get_func7 = 7'b0000000;
      SRAW   : get_func7 = 7'b0100000;
      MUL    : get_func7 = 7'b0000001;
      MULH   : get_func7 = 7'b0000001;
      MULHSU : get_func7 = 7'b0000001;
      MULHU  : get_func7 = 7'b0000001;
      DIV    : get_func7 = 7'b0000001;
      DIVU   : get_func7 = 7'b0000001;
      REM    : get_func7 = 7'b0000001;
      REMU   : get_func7 = 7'b0000001;
      MULW   : get_func7 = 7'b0000001;
      DIVW   : get_func7 = 7'b0000001;
      DIVUW  : get_func7 = 7'b0000001;
      REMW   : get_func7 = 7'b0000001;
      REMUW  : get_func7 = 7'b0000001;
      ECALL  : get_func7 = 7'b0000000;
      EBREAK : get_func7 = 7'b0000000;
      URET   : get_func7 = 7'b0000000;
      SRET   : get_func7 = 7'b0001000;
      MRET   : get_func7 = 7'b0011000;
      DRET   : get_func7 = 7'b0111101;
      WFI    : get_func7 = 7'b0001000;
      SFENCE_VMA: get_func7 = 7'b0001001;
      default : `uvm_fatal(`gfn, $sformatf("Unsupported instruction %0s", instr_name.name()))
    endcase
  endfunction

  // Convert the instruction to assembly code
  virtual function string convert2bin(string prefix = "");
    string binary;
    if (!is_compressed) begin
      case(format)
        J_FORMAT: begin
            binary = $sformatf("%8h", {imm[20], imm[10:1], imm[11], imm[19:12], rd,  get_opcode()});
        end
        U_FORMAT: begin
            binary = $sformatf("%8h", {imm[31:12], rd,  get_opcode()});
        end
        I_FORMAT: begin
          if(instr_name inside {FENCE, FENCE_I})
            binary = $sformatf("%8h", {17'b0, get_func3(), 5'b0, get_opcode()});
          else if(category == CSR)
            binary = $sformatf("%8h", {csr[10:0], imm[4:0], get_func3(), rd, get_opcode()});
          else if(instr_name == ECALL)
            binary = $sformatf("%8h", {get_func7(), 18'b0, get_opcode()});
          else if(instr_name inside {URET, SRET, MRET})
            binary = $sformatf("%8h", {get_func7(), 5'b10, 13'b0, get_opcode()});
          else if(instr_name inside {DRET})
            binary = $sformatf("%8h", {get_func7(), 5'b10010, 13'b0, get_opcode()});
          else if(instr_name == EBREAK)
            binary = $sformatf("%8h", {get_func7(), 5'b01, 13'b0, get_opcode()});
          else if(instr_name == WFI)
            binary = $sformatf("%8h", {get_func7(), 5'b101, 13'b0, get_opcode()});
          else
            binary = $sformatf("%8h", {imm[11:0], rs1, get_func3(), rd, get_opcode()});
        end
        S_FORMAT: begin
            binary = $sformatf("%8h", {imm[11:5], rs2, rs1, get_func3(), imm[4:0], get_opcode()});
        end
        B_FORMAT: begin
            binary = $sformatf("%8h",
                               {imm[12], imm[10:5], rs2, rs1, get_func3(),
                                imm[4:1], imm[11], get_opcode()});
        end
        R_FORMAT: begin
          if(category == CSR)
            binary = $sformatf("%8h", {csr[10:0], rs1, get_func3(), rd, get_opcode()});
          else if(instr_name == SFENCE_VMA)
            binary = $sformatf("%8h", {get_func7(), 18'b0, get_opcode()});
          else
            binary = $sformatf("%8h", {get_func7(), rs2, rs1, get_func3(), rd, get_opcode()});
        end
      endcase
    end else begin
      case (instr_name) inside
        C_ADDI4SPN:
          binary = $sformatf("%4h", {get_func3(), imm[5:4], imm[9:6],
                                     imm[2], imm[3], get_c_gpr(rd), get_c_opcode()});
        C_LQ:
          binary = $sformatf("%4h", {get_func3(), imm[5:4], imm[8],
                                     get_c_gpr(rs1), imm[7:6], get_c_gpr(rd), get_c_opcode()});
        C_FLD, C_LD:
          binary = $sformatf("%4h", {get_func3(), imm[5:3], get_c_gpr(rs1),
                                     imm[7:6], get_c_gpr(rd), get_c_opcode()});
        C_LW, C_FLW:
          binary = $sformatf("%4h", {get_func3(), imm[5:3], get_c_gpr(rs1),
                                     imm[2], imm[6], get_c_gpr(rd), get_c_opcode()});
        C_SQ:
          binary = $sformatf("%4h", {get_func3(), imm[5:4], imm[8],
                                     get_c_gpr(rs1), imm[7:6], get_c_gpr(rs2), get_c_opcode()});
        C_FSD, C_SD:
          binary = $sformatf("%4h", {get_func3(), imm[5:3], get_c_gpr(rs1),
                                     imm[7:6], get_c_gpr(rs2), get_c_opcode()});
        C_SW, C_FSW:
          binary = $sformatf("%4h", {get_func3(), imm[5:3], get_c_gpr(rs1),
                                     imm[2], imm[6], get_c_gpr(rs2), get_c_opcode()});
        C_NOP, C_ADDI, C_LI, C_ADDIW:
          binary = $sformatf("%4h", {get_func3(), imm[5], rd, imm[4:0], get_c_opcode()});
        C_JAL, C_J:
          binary = $sformatf("%4h", {get_func3(), imm[11], imm[4], imm[9:8],
                                     imm[10], imm[6], imm[7], imm[3:1], imm[5], get_c_opcode()});
        C_ADDI16SP:
          binary = $sformatf("%4h", {get_func3(), imm[9], 5'b10,
                                     imm[4], imm[6], imm[8:7], imm[5], get_c_opcode()});
        C_LUI:
          binary = $sformatf("%4h", {get_func3(), imm[5], rd, imm[4:0], get_c_opcode()});
        C_SRLI:
          binary = $sformatf("%4h", {get_func3(), imm[5],
                                     2'b0, get_c_gpr(rd), imm[4:0], get_c_opcode()});
        C_SRLI64:
          binary = $sformatf("%4h", {get_func3(), 3'b0, get_c_gpr(rd), 5'b0, get_c_opcode()});
        C_SRAI:
          binary = $sformatf("%4h", {get_func3(), imm[5],
                                     2'b01, get_c_gpr(rd), imm[4:0], get_c_opcode()});
        C_SRAI64:
          binary = $sformatf("%4h", {get_func3(), 3'b001,
                                     get_c_gpr(rd), 5'b0, get_c_opcode()});
        C_ANDI:
          binary = $sformatf("%4h", {get_func3(), imm[5],
                                     2'b10, get_c_gpr(rd), imm[4:0], get_c_opcode()});
        C_SUB:
          binary = $sformatf("%4h", {get_func3(), 3'b011, get_c_gpr(rd),
                                     2'b00, get_c_gpr(rs2), get_c_opcode()});
        C_XOR:
          binary = $sformatf("%4h", {get_func3(), 3'b011, get_c_gpr(rd),
                                     2'b01, get_c_gpr(rs2), get_c_opcode()});
        C_OR:
          binary = $sformatf("%4h", {get_func3(), 3'b011, get_c_gpr(rd),
                                     2'b10, get_c_gpr(rs2), get_c_opcode()});
        C_AND:
          binary = $sformatf("%4h", {get_func3(), 3'b011, get_c_gpr(rd),
                                     2'b11, get_c_gpr(rs2), get_c_opcode()});
        C_SUBW:
          binary = $sformatf("%4h", {get_func3(), 3'b111, get_c_gpr(rd),
                                     2'b00, get_c_gpr(rs2), get_c_opcode()});
        C_ADDW:
          binary = $sformatf("%4h", {get_func3(), 3'b111, get_c_gpr(rd),
                                     2'b01, get_c_gpr(rs2), get_c_opcode()});
        C_BEQZ, C_BNEZ:
          binary = $sformatf("%4h", {get_func3(), imm[8], imm[4:3],
                                     get_c_gpr(rs1), imm[7:6], imm[2:1], imm[5], get_c_opcode()});
        C_SLLI:
          binary = $sformatf("%4h", {get_func3(), imm[5], rd, imm[4:0], get_c_opcode()});
        C_SLLI64:
          binary = $sformatf("%4h", {get_func3(), 1'b0, rd, 5'b0, get_c_opcode()});
        C_FLDSP, C_LDSP:
          binary = $sformatf("%4h", {get_func3(), imm[5], rd, imm[4:3], imm[8:6], get_c_opcode()});
        C_LQSP:
          binary = $sformatf("%4h", {get_func3(), imm[5], rd, imm[4], imm[9:6], get_c_opcode()});
        C_LWSP, C_FLWSP:
          binary = $sformatf("%4h", {get_func3(), imm[5], rd, imm[4:2], imm[7:6], get_c_opcode()});
        C_JR:
          binary = $sformatf("%4h", {get_func3(), 1'b0, rs1, 5'b0, get_c_opcode()});
        C_MV:
          binary = $sformatf("%4h", {get_func3(), 1'b0, rd, rs2, get_c_opcode()});
        C_EBREAK:
          binary = $sformatf("%4h", {get_func3(), 1'b1, 10'b0, get_c_opcode()});
        C_JALR:
          binary = $sformatf("%4h", {get_func3(), 1'b1, 10'b0, get_c_opcode()});
        C_ADD:
          binary = $sformatf("%4h", {get_func3(), 1'b1, rd, rs2, get_c_opcode()});
        C_FSDSP, C_SDSP:
          binary = $sformatf("%4h", {get_func3(), 1'b0, imm[5:3], imm[8:6], rs2, get_c_opcode()});
        C_SQSP:
          binary = $sformatf("%4h", {get_func3(), 1'b0, imm[5:4], imm[9:6], rs2, get_c_opcode()});
        C_SWSP, C_FSWSP:
          binary = $sformatf("%4h", {get_func3(), 1'b0, imm[5:2], imm[7:6], rs2, get_c_opcode()});
        default : `uvm_fatal(`gfn, $sformatf("Unsupported instruction %0s", instr_name.name()))
      endcase
    end
    return {prefix, binary};
  endfunction

  virtual function string get_instr_name();
    get_instr_name = instr_name.name();
    if(get_instr_name.substr(0, 1) == "C_") begin
      get_instr_name = {"c.", get_instr_name.substr(2, get_instr_name.len() - 1)};
    end else if (group == RV32A) begin
      get_instr_name = {get_instr_name.substr(0, get_instr_name.len() - 3), ".w"};
      get_instr_name = aq ? {get_instr_name, ".aq"} :
                       rl ? {get_instr_name, ".rl"} : get_instr_name;
    end else if (group == RV64A) begin
      get_instr_name = {get_instr_name.substr(0, get_instr_name.len() - 3), ".d"};
      get_instr_name = aq ? {get_instr_name, ".aq"} :
                       rl ? {get_instr_name, ".rl"} : get_instr_name;
    end else if (group inside {RV32F, RV64F, RV32D, RV64D}) begin
      foreach(get_instr_name[i]) begin
        if (get_instr_name[i] == "_") begin
          get_instr_name[i] = ".";
        end
      end
    end
    return get_instr_name;
  endfunction

  // Get RVC register name for CIW, CL, CS, CB format
  virtual function bit [2:0] get_c_gpr(riscv_reg_t gpr);
    return gpr[2:0];
  endfunction

  // Default return imm value directly, can be overriden to use labels and symbols
  // Example: %hi(symbol), %pc_rel(label) ...
  virtual function string get_imm();
    return imm_str;
  endfunction

  virtual function void clear_unused_label();
    if(has_label && !is_branch_target && is_local_numeric_label) begin
      has_label = 1'b0;
    end
  endfunction

  // Copy the rand fields of the base instruction
  virtual function void copy_base_instr(riscv_instr_base obj);
    this.group             = obj.group;
    this.format            = obj.format;
    this.category          = obj.category;
    this.instr_name        = obj.instr_name;
    this.rs2               = obj.rs2;
    this.rs1               = obj.rs1;
    this.rd                = obj.rd;
    this.imm               = obj.imm;
    this.imm_type          = obj.imm_type;
    this.imm_len           = obj.imm_len;
    this.imm_mask          = obj.imm_mask;
    this.imm_str           = obj.imm_str;
    this.is_pseudo_instr   = obj.is_pseudo_instr;
    this.aq                = obj.aq;
    this.rl                = obj.rl;
    this.is_compressed     = obj.is_compressed;
    this.has_imm           = obj.has_imm;
    this.has_rs1           = obj.has_rs1;
    this.has_rs2           = obj.has_rs2;
    this.has_rd            = obj.has_rd;
    this.fs3               = obj.fs3;
    this.fs2               = obj.fs2;
    this.fs1               = obj.fs1;
    this.fd                = obj.fd;
    this.has_fs1           = obj.has_fs1;
    this.has_fs2           = obj.has_fs2;
    this.has_fs3           = obj.has_fs3;
    this.has_fd            = obj.has_fd;
    this.is_floating_point = obj.is_floating_point;
    this.vd                = obj.vd;
    this.vs1               = obj.vs1;
    this.vs2               = obj.vs2;
    this.vs3               = obj.vs3;
    this.vm                = obj.vm;
  endfunction

  static string vec_instr_name_map[riscv_instr_name_t] = '{
    VLE_V:"vle.v", VSE_V:"vse.v", VLB_V:"vlb.v", VSB_V:"vsb.v", VLH_V:"vlh.v", VSH_V:"vsh.v", VLW_V:"vlw.v",
    VSW_V:"vsw.v", VLBU_V:"vlbu.v", VLHU_V:"vlhu.v", VLWU_V:"vlwu.v", VLSB_V:"vlsb.v", VLSH_V:"vlsh.v", VLSW_V:"vlsw.v",
    VLSBU_V:"vlsbu.v", VLSHU_V:"vlshu.v", VLSWU_V:"vlswu.v", VLSE_V:"vlse.v", VSSB_V:"vssb.v", VSSH_V:"vssh.v",
    VSSW_V:"vssw.v", VSSE_V:"vsse.v", VLXB_V:"vlxb.v", VLXH_V:"vlxh.v", VLXW_V:"vlxw.v", VLXBU_V:"vlxbu.v",
    VLXHU_V:"vlxhu.v", VLXWU_V:"vlxwu.v", VLXE_V:"vlxe.v", VSXB_V:"vsxb.v", VSXH_V:"vsxh.v", VSXW_V:"vsxw.v",
    VSXE_V:"vsxe.v", VSUXB_V:"vsuxb.v", VSUXH_V:"vsuxh.v", VSUXW_V:"vsuxw.v", VSUXE_V:"vsuxe.v", VLBFF_V:"vlbff.v",
    VLHFF_V:"vlhff.v", VLWFF_V:"vlwff.v", VLBUFF_V:"vlbuff.v", VLHUFF_V:"vlhuff.v", VLWUFF_V:"vlwuff.v",
    VLEFF_V:"vleff.v", VADD_VV:"vadd.vv", VADD_VX:"vadd.vx", VADD_VI:"vadd.vi", VSUB_VV:"vsub.vv", VSUB_VX:"vsub.vx",
    VRSUB_VX:"vrsub.vx", VRSUB_VI:"vrsub.vi", VWADDU_VV:"vwaddu.vv", VWADDU_VX:"vwaddu.vx", VWSUBU_VV:"vwsubu.vv",
    VWSUBU_VX:"vwsubu.vx", VWADD_VV:"vwadd.vv", VWADD_VX:"vwadd.vx", VWSUB_VV:"vwsub.vv", VWSUB_VX:"vwsub.vx",
    VWADDU_WV:"vwaddu.wv", VWADDU_WX:"vwaddu.wx", VWSUBU_WV:"vwsubu.wv", VWSUBU_WX:"vwsubu.wx", VWADD_WV:"vwadd.wv",
    VWADD_WX:"vwadd.wx", VWSUB_WV:"vwsub.wv", VWSUB_WX:"vwsub.wx", VADC_VVM:"vadc.vvm", VADC_VXM:"vadc.vxm",
    VADC_VIM:"vadc.vim", VMADC_VVM:"vmadc.vvm", VMADC_VXM:"vmadc.vxm", VMADC_VIM:"vmadc.vim", VMADC_VV:"vmadc.vv",
    VMADC_VX:"vmadc.vx", VMADC_VI:"vmadc.vi", VSBC_VVM:"vsbc.vvm", VSBC_VXM:"vsbc.vxm", VMSBC_VVM:"vmsbc.vvm",
    VMSBC_VXM:"vmsbc.vxm", VMSBC_VV:"vmsbc.vv", VMSBC_VX:"vmsbc.vx", VAND_VV:"vand.vv", VAND_VX:"vand.vx",
    VAND_VI:"vand.vi", VOR_VV:"vor.vv", VOR_VX:"vor.vx", VOR_VI:"vor.vi", VXOR_VV:"vxor.vv", VXOR_VX:"vxor.vx",
    VXOR_VI:"vxor.vi", VSLL_VV:"vsll.vv", VSLL_VX:"vsll.vx", VSLL_VI:"vsll.vi", VSRL_VV:"vsrl.vv", VSRL_VX:"vsrl.vx",
    VSRL_VI:"vsrl.vi", VSRA_VV:"vsra.vv", VSRA_VX:"vsra.vx", VSRA_VI:"vsra.vi", VNSRL_WV:"vnsrl.wv",
    VNSRL_WX:"vnsrl.wx", VNSRL_WI:"vnsrl.wi", VNSRA_WV:"vnsra.wv", VNSRA_WX:"vnsra.wx", VNSRA_WI:"vnsra.wi",
    VMSEQ_VV:"vmseq.vv", VMSEQ_VX:"vmseq.vx", VMSEQ_VI:"vmseq.vi", VMSNE_VV:"vmsne.vv", VMSNE_VX:"vmsne.vx",
    VMSNE_VI:"vmsne.vi", VMSLTU_VV:"vmsltu.vv", VMSLTU_VX:"vmsltu.vx", VMSLT_VV:"vmslt.vv", VMSLT_VX:"vmslt.vx",
    VMSLEU_VV:"vmsleu.vv", VMSLEU_VX:"vmsleu.vx", VMSLEU_VI:"vmsleu.vi", VMSLE_VV:"vmsle.vv", VMSLE_VX:"vmsle.vx",
    VMSLE_VI:"vmsle.vi", VMSGTU_VX:"vmsgtu.vx", VMSGTU_VI:"vmsgtu.vi", VMSGT_VX:"vmsgt.vx", VMSGT_VI:"vmsgt.vi",
    VMINU_VV:"vminu.vv", VMINU_VX:"vminu.vx", VMIN_VV:"vmin.vv", VMIN_VX:"vmin.vx", VMAXU_VV:"vmaxu.vv",
    VMAXU_VX:"vmaxu.vx", VMAX_VV:"vmax.vv", VMAX_VX:"vmax.vx", VMUL_VV:"vmul.vv", VMUL_VX:"vmul.vx",
    VMULH_VV:"vmulh.vv", VMULH_VX:"vmulh.vx", VMULHU_VV:"vmulhu.vv", VMULHU_VX:"vmulhu.vx", VMULHSU_VV:"vmulhsu.vv",
    VMULHSU_VX:"vmulhsu.vx", VDIVU_VV:"vdivu.vv", VDIVU_VX:"vdivu.vx", VDIV_VV:"vdiv.vv", VDIV_VX:"vdiv.vx",
    VREMU_VV:"vremu.vv", VREMU_VX:"vremu.vx", VREM_VV:"vrem.vv", VREM_VX:"vrem.vx", VWMUL_VV:"vmul.vv",
    VWMUL_VX:"vmul.vx", VWMULU_VV:"vmulhu.vv", VWMULU_VX:"vmulhu.vx", VWMULSU_VV:"vmulhsu.vv", VWMULSU_VX:"vmulhsu.vx",
    VMACC_VV:"vmacc.vv", VMACC_VX:"vmacc.vx", VNMSAC_VV:"vnmsac.vv", VNMSAC_VX:"vnmsac.vx", VMADD_VV:"vmadd.vv",
    VMADD_VX:"vmadd.vx", VNMSUB_VV:"vnmsub.vv", VNMSUB_VX:"vnmsub.vx", VWMACCU_VV:"vwmaccu.vv", VWMACCU_VX:"vwmaccu.vx",
    VWMACC_VV:"vwmacc.vv", VWMACC_VX:"vwmacc.vx", VWMACCSU_VV:"vwmaccsu.vv", VWMACCSU_VX:"vwmaccsu.vx",
    VWMACCUS_VX:"vwmaccus.vx", VQMACCU_VV:"vqmaccu.vv", VQMACCU_VX:"vqmaccu.vx", VQMACC_VV:"vqmacc.vv",
    VQMACC_VX:"vqmacc.vx", VQMACCSU_VV:"vqmaccsu.vv", VQMACCSU_VX:"vqmaccsu.vx", VQMACCUS_VX:"vqmaccus.vx",
    VMERGE_VVM:"vmerge.vvm", VMERGE_VXM:"vmerge.vxm", VMERGE_VIM:"vmerge.vim", VMV_V_V:"vmv.v.v", VMV_V_X:"vmv.v.x",
    VMV_V_I:"vmv.v.i", VSADDU_VV:"vsaddu.vv", VSADDU_VX:"vsaddu.vx", VSADDU_VI:"vsaddu.vi", VSADD_VV:"vsadd.vv",
    VSADD_VX:"vsadd.vx", VSADD_VI:"vsadd.vi", VSSUBU_VV:"vssubu.vv", VSSUBU_VX:"vssubu.vx", VSSUB_VV:"vssub.vv",
    VSSUB_VX:"vssub.vx", VAADD_VV:"vaadd.vv", VAADD_VX:"vaadd.vx", VAADDU_VV:"vaaddu.vv", VAADDU_VX:"vaaddu.vx",
    VASUBU_VV:"vasubu.vv", VASUBU_VX:"vasubu.vx", VASUB_VV:"vasub.vv", VASUB_VX:"vasub.vx", VSMUL_VV:"vsmul.vv",
    VSMUL_VX:"vsmul.vx", VSSRL_VV:"vssrl.vv", VSSRL_VX:"vssrl.vx", VSSRL_VI:"vssrl.vi", VSSRA_VV:"vssra.vv",
    VSSRA_VX:"vssra.vx", VSSRA_VI:"vssra.vi", VNCLIPU_WV:"vnclipu.wv", VNCLIPU_WX:"vnclipu.wx", VNCLIPU_WI:"vnclipu.wi",
    VNCLIP_WV:"vnclip.wv", VNCLIP_WX:"vnclip.wx", VNCLIP_WI:"vnclip.wi", VFADD_VV:"vfadd.vv", VFADD_VF:"vfadd.vf",
    VFSUB_VV:"vfsub.vv", VFSUB_VF:"vfsub.vf", VFRSUB_VF:"vfrsub.vf", VFWADD_VV:"vfwadd.vv", VFWADD_VF:"vfwadd.vf",
    VFWSUB_VV:"vfwsub.vv", VFWSUB_VF:"vfwsub.vf", VFWADD_WV:"vfwadd.wv", VFWADD_WF:"vfwadd.wf", VFWSUB_WV:"vfwsub.wv",
    VFWSUB_WF:"vfwsub.wf", VFMUL_VV:"vfmul.vv", VFMUL_VF:"vfmul.vf", VFDIV_VV:"vfdiv.vv", VFDIV_VF:"vfdiv.vf",
    VFRDIV_VF:"vfrdiv.vf", VFWMUL_VV:"vfwmul.vv", VFWMUL_VF:"vfwmul.vf", VFMACC_VV:"vfmacc.vv", VFMACC_VF:"vfmacc.vf",
    VFNMACC_VV:"vfnmacc.vv", VFNMACC_VF:"vfnmacc.vf", VFMSAC_VV:"vfmsac.vv", VFMSAC_VF:"vfmsac.vf",
    VFNMSAC_VV:"vfnmsac.vv", VFNMSAC_VF:"vfnmsac.vf", VFMADD_VV:"vfmadd.vv", VFMADD_VF:"vfmadd.vf",
    VFNMADD_VV:"vfnmadd.vv", VFNMADD_VF:"vfnmadd.vf", VFMSUB_VV:"vfmsub.vv", VFMSUB_VF:"vfmsub.vf",
    VFNMSUB_VV:"vfnmsub.vv", VFNMSUB_VF:"vfnmsub.vf", VFWMACC_VV:"vfwmacc.vv", VFWMACC_VF:"vfwmacc.vf",
    VFWNMACC_VV:"vfwnmacc.vv", VFWNMACC_VF:"vfwnmacc.vf", VFWMSAC_VV:"vfwmsac.vv", VFWMSAC_VF:"vfwmsac.vf",
    VFWNMSAC_VV:"vfwnmsac.vv", VFWNMSAC_VF:"vfwnmsac.vf", VFSQRT_V:"vfsqrt.v", VFMIN_VV:"vfmin.vv", VFMIN_VF:"vfmin.vf",
    VFMAX_VV:"vfmax.vv", VFMAX_VF:"vfmax.vf", VFSGNJ_VV:"vfsgnj.vv", VFSGNJ_VF:"vfsgnj.vf", VFSGNJN_VV:"vfsgnjn.vv",
    VFSGNJN_VF:"vfsgnjn.vf", VFSGNJX_VV:"vfsgnjx.vv", VFSGNJX_VF:"vfsgnjx.vf", VMFEQ_VV:"vmfeq.vv", VMFEQ_VF:"vmfeq.vf",
    VMFNE_VV:"vmfne.vv", VMFNE_VF:"vmfne.vf", VMFLT_VV:"vmflt.vv", VMFLT_VF:"vmflt.vf", VMFLE_VV:"vmfle.vv",
    VMFLE_VF:"vmfle.vf", VMFGT_VF:"vmfgt.vf", VMFGE_VF:"vmfge.vf", VFCLASS_V:"vfclass.v", VFMERGE_VFM:"vfmerge.vfm",
    VFMV_V_F:"vfmv.v.f", VFCVT_XU_F_V:"vfcvt.xu.f.v", VFCVT_X_F_V:"vfcvt.x.f.v", VFCVT_F_XU_V:"vfcvt.f.xu.v",
    VFCVT_F_X_V:"vfcvt.f.x.v", VFWCVT_XU_F_V:"vfwcvt.xu.f.v", VFWCVT_X_F_V:"vfwcvt.x.f.v", VFWCVT_F_XU_V:"vfwcvt.f.xu.v",
    VFWCVT_F_X_V:"vfwcvt.f.x.v", VFWCVT_F_F_V:"vfwcvt.f.x.v", VFNCVT_XU_F_W:"vfncvt.xu.f.w",
    VFNCVT_X_F_W:"vfncvt.x.f.w", VFNCVT_F_XU_W:"vfncvt.f.xu.w", VFNCVT_F_X_W:"vfncvt.f.x.w",
    VFNCVT_F_F_W:"vfncvt.f.x.w", VFNCVT_ROD_F_F_W:"vfncvt.rod.f.f.w", VREDSUM_VS:"vredsum.vs",
    VREDMAXU_VS:"vredmaxu.vs", VREDMAX_VS:"vredmax.vs", VREDMINU_VS:"vredminu.vs", VREDMIN_VS:"vredmin.vs",
    VREDAND_VS:"vredand.vs", VREDOR_VS:"vredor.vs", VREDXOR_VS:"vredxor.vs", VWREDSUMU_VS:"vwredsumu.vs",
    VWREDSUM_VS:"vwredsum.vs", VFREDOSUM_VS:"vfredosum.vs", VFREDMAX_VS:"vfredmax.vs", VFWREDOSUM_VS:"vfwredosum.vs",
    VFWREDSUM_VS:"vfwredsum.vs", VMAND_MM:"vmand.mm", VMNAND_MM:"vmnand.mm", VMANDNOT_MM:"vmandnot.mm",
    VMXOR_MM:"vmxor.mm", VMOR_MM:"vmor.mm", VMNOR_MM:"vmnor.mm", VMORNOT_MM:"vmornot.mm", VMXNOR_MM:"vmxnor.mm",
    VMSBF_M:"vmsbf.m", VMSIF_M:"vmsif.m", VMSOF_M:"vmsof.m", VIOTA_M:"viota.m", VID_V:"vid.v", VMV_X_S:"vmv.x.s",
    VMV_S_X:"vmv.s.x", VFMV_F_S:"vfmv.f.s", VFMV_S_F:"vfmv.s.f", VSLIDE1UP_VX:"vslide1up.vx",
    VSLIDE1DOWN_VX:"vslide1down.vx", VRGATHER_VV:"vrgather.vv", VRGATHER_VX:"vrgather.vx", VRGATHER_VI:"vrgather.vi",
    VDOTU_VV:"vdotu.vv", VDOT_VV:"vdot.vv", VFDOT_VV:"vfdot.vv", VFREDSUM_VS:"vfredsum.vs", VFREDMIN_VS:"vfredmin.vs",
    VPOPC_M:"vpopc.m", VFIRST_M:"vfirst.m", VSLIDEUP_VX:"vslideup.vx", VSLIDEUP_VI:"vslideup.vi",
    VSLIDEDOWN_VX:"vslidedown.vx", VSLIDEDOWN_VI:"vslidedown.vi", VCOMPRESS_VM:"vcompress.vm",
    VAMOSWAPW_V:"vamoswapw.v", VAMOADDW_V:"vamoaddw.v", VAMOXORW_V:"vamoxorw.v", VAMOANDW_V:"vamoandw.v",
    VAMOORW_V:"vamoorw.v", VAMOMINW_V:"vamominw.v", VAMOMAXW_V:"vamomaxw.v", VAMOMINUW_V:"vamominuw.v",
    VAMOMAXUW_V:"vamomaxuw.v", VAMOSWAPE_V:"vamoswape.v", VAMOADDE_V:"vamoadde.v", VAMOXORE_V:"vamoxore.v",
    VAMOANDE_V:"vamoande.v", VAMOORE_V:"vamoore.v", VAMOMINE_V:"vamomine.v", VAMOMAXE_V:"vamomaxe.v",
    VAMOMINUE_V:"vamominue.v", VAMOMAXUE_V:"vamomaxue.v"
  };

  virtual function string vec_instr_name_to_str();
    if (vec_instr_name_map.exists(instr_name)) return vec_instr_name_map[instr_name];
    vec_instr_name_to_str = instr_name.name();
    vec_instr_name_to_str = vec_instr_name_to_str.tolower();
  endfunction

  virtual function string vec_reg_to_str(riscv_vec_reg_t vreg);
    vec_reg_to_str = vreg.name();
    vec_reg_to_str = vec_reg_to_str.tolower();
  endfunction

  virtual function string scalar_reg_to_str(riscv_reg_t sreg);
    scalar_reg_to_str = sreg.name();
    scalar_reg_to_str = scalar_reg_to_str.tolower();
  endfunction

  virtual function string float_reg_to_str(riscv_fpr_t freg);
    float_reg_to_str = freg.name();
    float_reg_to_str = float_reg_to_str.tolower();
  endfunction

  virtual function string vec_wd_str(bit reg_sel);
    vec_wd_str = wd ? vd.name() : reg_sel ? vec_reg_to_str(vs3) : "x0";
  endfunction

  virtual function string vec_vm_str();
    vec_vm_str = vm ? "" : ", v0.t";
  endfunction

endclass

// Psuedo instructions are used to simplify assembly program writing
class riscv_pseudo_instr extends riscv_instr_base;

  rand riscv_pseudo_instr_name_t  pseudo_instr_name;

  constraint default_c {
    is_pseudo_instr == 1'b1;
  }

  `add_pseudo_instr(LI,    I_FORMAT, LOAD, RV32I)
  `add_pseudo_instr(LA,    I_FORMAT, LOAD, RV32I)

  `uvm_object_utils(riscv_pseudo_instr)

  function new(string name = "");
    super.new(name);
    process_load_store = 0;
  endfunction

  // Convert the instruction to assembly code
  virtual function string convert2asm(string prefix = "");
    string asm_str;
    asm_str = format_string(get_instr_name(), MAX_INSTR_STR_LEN);
    // instr rd,imm
    asm_str = $sformatf("%0s%0s, %0s", asm_str, rd.name(), get_imm());
    if(comment != "")
      asm_str = {asm_str, " #",comment};
    return asm_str.tolower();
  endfunction

  virtual function string get_instr_name();
    return pseudo_instr_name.name();
  endfunction

endclass
