;; Machine description for CORE-V vendor extensions.
;; Copyright (C) 2023-2024 Free Software Foundation, Inc.

;; This file is part of GCC.

;; GCC is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; GCC is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GCC; see the file COPYING3.  If not see
;; <http://www.gnu.org/licenses/>.

(define_c_enum "unspec" [

  ;;CORE-V ALU
  UNSPEC_CV_ALU_CLIP
  UNSPEC_CV_ALU_CLIPR
  UNSPEC_CV_ALU_CLIPU
  UNSPEC_CV_ALU_CLIPUR

  ;;CORE-V EVENT LOAD
  UNSPECV_CV_ELW
])

;; XCVMAC extension.

(define_insn "riscv_cv_mac_mac"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (plus:SI (mult:SI (match_operand:SI 1 "register_operand" "r")
                          (match_operand:SI 2 "register_operand" "r"))
                 (match_operand:SI 3 "register_operand" "0")))]

  "TARGET_XCVMAC && !TARGET_64BIT"
  "cv.mac\t%0,%1,%2"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_mac_msu"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (minus:SI (match_operand:SI 3 "register_operand" "0")
                  (mult:SI (match_operand:SI 1 "register_operand" "r")
                           (match_operand:SI 2 "register_operand" "r"))))]

  "TARGET_XCVMAC && !TARGET_64BIT"
  "cv.msu\t%0,%1,%2"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_mac_muluN"
  [(set (match_operand:SI 0 "register_operand" "=r")
    (lshiftrt:SI
      (mult:SI
        (zero_extend:SI
          (truncate:HI
            (match_operand:SI 1 "register_operand" "r")))
        (zero_extend:SI
          (truncate:HI
            (match_operand:SI 2 "register_operand" "r"))))
      (match_operand:QI 3 "const_csr_operand" "K")))]

  "TARGET_XCVMAC && !TARGET_64BIT"
  "cv.mulun\t%0,%1,%2,%3"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_mac_mulhhuN"
  [(set (match_operand:SI 0 "register_operand" "=r")
    (lshiftrt:SI
      (mult:SI
        (zero_extend:SI
          (truncate:HI
            (lshiftrt:SI (match_operand:SI 1 "register_operand" "r")
                         (const_int 16))))
        (zero_extend:SI
          (truncate:HI
            (lshiftrt:SI (match_operand:SI 2 "register_operand" "r")
                         (const_int 16)))))
      (match_operand:QI 3 "const_csr_operand" "K")))]

  "TARGET_XCVMAC && !TARGET_64BIT"
  "cv.mulhhun\t%0,%1,%2,%3"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_mac_mulsN"
  [(set (match_operand:SI 0 "register_operand" "=r")
    (ashiftrt:SI
      (mult:SI
        (sign_extend:SI
          (truncate:HI
            (match_operand:SI 1 "register_operand" "r")))
        (sign_extend:SI
          (truncate:HI
            (match_operand:SI 2 "register_operand" "r"))))
      (match_operand:QI 3 "const_csr_operand" "K")))]

  "TARGET_XCVMAC && !TARGET_64BIT"
  "cv.mulsn\t%0,%1,%2,%3"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_mac_mulhhsN"
  [(set (match_operand:SI 0 "register_operand" "=r")
    (ashiftrt:SI
      (mult:SI
        (sign_extend:SI
          (truncate:HI
            (lshiftrt:SI (match_operand:SI 1 "register_operand" "r")
                         (const_int 16))))
        (sign_extend:SI
          (truncate:HI
            (lshiftrt:SI (match_operand:SI 2 "register_operand" "r")
                         (const_int 16)))))
      (match_operand:QI 3 "const_csr_operand" "K")))]

  "TARGET_XCVMAC && !TARGET_64BIT"
  "cv.mulhhsn\t%0,%1,%2,%3"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_mac_muluRN"
  [(set (match_operand:SI 0 "register_operand" "=r")
    (lshiftrt:SI
      (fma:SI
        (zero_extend:SI
          (truncate:HI
            (match_operand:SI 1 "register_operand" "r")))
        (zero_extend:SI
          (truncate:HI
            (match_operand:SI 2 "register_operand" "r")))
        (if_then_else
          (ne:QI (match_operand:QI 3 "const_csr_operand" "K") (const_int 0))
          (ashift:SI (const_int 1)
            (minus:QI (match_dup 3)
                      (const_int 1)))
          (const_int 0)))
      (match_dup 3)))]

  "TARGET_XCVMAC && !TARGET_64BIT"
  "cv.mulurn\t%0,%1,%2,%3"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_mac_mulhhuRN"
  [(set (match_operand:SI 0 "register_operand" "=r")
    (lshiftrt:SI
      (fma:SI
        (zero_extend:SI
          (truncate:HI
            (lshiftrt:SI (match_operand:SI 1 "register_operand" "r")
                         (const_int 16))))
        (zero_extend:SI
          (truncate:HI
            (lshiftrt:SI (match_operand:SI 2 "register_operand" "r")
                         (const_int 16))))
        (if_then_else
          (ne:QI (match_operand:QI 3 "const_csr_operand" "K") (const_int 0))
          (ashift:SI (const_int 1)
            (minus:QI (match_dup 3)
                      (const_int 1)))
          (const_int 0)))
      (match_dup 3)))]

  "TARGET_XCVMAC && !TARGET_64BIT"
  "cv.mulhhurn\t%0,%1,%2,%3"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_mac_mulsRN"
  [(set (match_operand:SI 0 "register_operand" "=r")
    (ashiftrt:SI
      (fma:SI
        (sign_extend:SI
          (truncate:HI
            (match_operand:SI 1 "register_operand" "r")))
        (sign_extend:SI
          (truncate:HI
            (match_operand:SI 2 "register_operand" "r")))
        (if_then_else
          (ne:QI (match_operand:QI 3 "const_csr_operand" "K") (const_int 0))
          (ashift:SI (const_int 1)
                     (minus:QI (match_dup 3)
                               (const_int 1)))
          (const_int 0)))
      (match_dup 3)))]

  "TARGET_XCVMAC && !TARGET_64BIT"
  "cv.mulsrn\t%0,%1,%2,%3"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_mac_mulhhsRN"
  [(set (match_operand:SI 0 "register_operand" "=r")
    (ashiftrt:SI
      (fma:SI
        (sign_extend:SI
          (truncate:HI
            (lshiftrt:SI (match_operand:SI 1 "register_operand" "r")
                         (const_int 16))))
        (sign_extend:SI
          (truncate:HI
            (lshiftrt:SI (match_operand:SI 2 "register_operand" "r")
                         (const_int 16))))
        (if_then_else
          (ne:QI (match_operand:QI 3 "const_csr_operand" "K") (const_int 0))
          (ashift:SI (const_int 1)
                     (minus:QI (match_dup 3)
                               (const_int 1)))
          (const_int 0)))
      (match_dup 3)))]

  "TARGET_XCVMAC && !TARGET_64BIT"
  "cv.mulhhsrn\t%0,%1,%2,%3"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_mac_macuN"
  [(set (match_operand:SI 0 "register_operand" "=r")
    (lshiftrt:SI
      (fma:SI
        (zero_extend:SI
          (truncate:HI
            (match_operand:SI 1 "register_operand" "r")))
        (zero_extend:SI
          (truncate:HI
            (match_operand:SI 2 "register_operand" "r")))
        (match_operand:SI 3 "register_operand" "0"))
      (match_operand:QI 4 "const_csr_operand" "K")))]

  "TARGET_XCVMAC && !TARGET_64BIT"
  "cv.macun\t%0,%1,%2,%4"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_mac_machhuN"
  [(set (match_operand:SI 0 "register_operand" "=r")
    (lshiftrt:SI
      (fma:SI
        (zero_extend:SI
          (truncate:HI
            (lshiftrt:SI (match_operand:SI 1 "register_operand" "r")
                         (const_int 16))))
        (zero_extend:SI
          (truncate:HI
            (lshiftrt:SI (match_operand:SI 2 "register_operand" "r")
                         (const_int 16))))
        (match_operand:SI 3 "register_operand" "0"))
      (match_operand:QI 4 "const_csr_operand" "K")))]

  "TARGET_XCVMAC && !TARGET_64BIT"
  "cv.machhun\t%0,%1,%2,%4"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_mac_macsN"
  [(set (match_operand:SI 0 "register_operand" "=r")
    (ashiftrt:SI
      (fma:SI
        (sign_extend:SI
          (truncate:HI
            (match_operand:SI 1 "register_operand" "r")))
        (sign_extend:SI
          (truncate:HI
            (match_operand:SI 2 "register_operand" "r")))
        (match_operand:SI 3 "register_operand" "0"))
      (match_operand:QI 4 "const_csr_operand" "K")))]

  "TARGET_XCVMAC && !TARGET_64BIT"
  "cv.macsn\t%0,%1,%2,%4"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_mac_machhsN"
  [(set (match_operand:SI 0 "register_operand" "=r")
    (ashiftrt:SI
      (fma:SI
        (sign_extend:SI
          (truncate:HI
            (lshiftrt:SI (match_operand:SI 1 "register_operand" "r")
                         (const_int 16))))
        (sign_extend:SI
          (truncate:HI
            (lshiftrt:SI (match_operand:SI 2 "register_operand" "r")
                         (const_int 16))))
        (match_operand:SI 3 "register_operand" "0"))
      (match_operand:QI 4 "const_csr_operand" "K")))]

  "TARGET_XCVMAC && !TARGET_64BIT"
  "cv.machhsn\t%0,%1,%2,%4"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_mac_macuRN"
  [(set (match_operand:SI 0 "register_operand" "=r")
    (lshiftrt:SI
      (plus:SI
        (fma:SI
          (zero_extend:SI
            (truncate:HI
              (match_operand:SI 1 "register_operand" "r")))
          (zero_extend:SI
            (truncate:HI
              (match_operand:SI 2 "register_operand" "r")))
          (match_operand:SI 3 "register_operand" "0"))
        (if_then_else
          (ne:QI (match_operand:QI 4 "const_csr_operand" "K") (const_int 0))
          (ashift:SI (const_int 1)
                     (minus:QI (match_dup 4)
                               (const_int 1)))
          (const_int 0)))
      (match_dup 4)))]

  "TARGET_XCVMAC && !TARGET_64BIT"
  "cv.macurn\t%0,%1,%2,%4"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_mac_machhuRN"
  [(set (match_operand:SI 0 "register_operand" "=r")
    (lshiftrt:SI
      (plus:SI
        (fma:SI
          (zero_extend:SI
            (truncate:HI
              (lshiftrt:SI (match_operand:SI 1 "register_operand" "r")
                           (const_int 16))))
          (zero_extend:SI
            (truncate:HI
              (lshiftrt:SI (match_operand:SI 2 "register_operand" "r")
                           (const_int 16))))
          (match_operand:SI 3 "register_operand" "0"))
        (if_then_else
          (ne:QI (match_operand:QI 4 "const_csr_operand" "K") (const_int 0))
          (ashift:SI (const_int 1)
                     (minus:QI (match_dup 4)
                               (const_int 1)))
          (const_int 0)))
      (match_dup 4)))]

  "TARGET_XCVMAC && !TARGET_64BIT"
  "cv.machhurn\t%0,%1,%2,%4"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_mac_macsRN"
  [(set (match_operand:SI 0 "register_operand" "=r")
    (ashiftrt:SI
      (plus:SI
        (fma:SI
          (sign_extend:SI
            (truncate:HI
              (match_operand:SI 1 "register_operand" "r")))
          (sign_extend:SI
            (truncate:HI
              (match_operand:SI 2 "register_operand" "r")))
          (match_operand:SI 3 "register_operand" "0"))
        (if_then_else
          (ne:QI (match_operand:QI 4 "const_csr_operand" "K") (const_int 0))
          (ashift:SI (const_int 1)
                     (minus:QI (match_dup 4)
                               (const_int 1)))
          (const_int 0)))
      (match_dup 4)))]

  "TARGET_XCVMAC && !TARGET_64BIT"
  "cv.macsrn\t%0,%1,%2,%4"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_mac_machhsRN"
  [(set (match_operand:SI 0 "register_operand" "=r")
    (ashiftrt:SI
      (plus:SI
        (fma:SI
          (sign_extend:SI
            (truncate:HI
              (lshiftrt:SI (match_operand:SI 1 "register_operand" "r")
                           (const_int 16))))
          (sign_extend:SI
            (truncate:HI
              (lshiftrt:SI (match_operand:SI 2 "register_operand" "r")
                           (const_int 16))))
          (match_operand:SI 3 "register_operand" "0"))
        (if_then_else
          (ne:QI (match_operand:QI 4 "const_csr_operand" "K") (const_int 0))
          (ashift:SI (const_int 1)
                     (minus:QI (match_dup 4)
                               (const_int 1)))
          (const_int 0)))
      (match_dup 4)))]

  "TARGET_XCVMAC && !TARGET_64BIT"
  "cv.machhsrn\t%0,%1,%2,%4"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

;; XCVALU builtins

(define_insn "riscv_cv_alu_slet"
  [(set (match_operand:SI 0 "register_operand" "=r")
    (le:SI
      (match_operand:SI 1 "register_operand" "r")
      (match_operand:SI 2 "register_operand" "r")))]

  "TARGET_XCVALU && !TARGET_64BIT"
  "cv.sle\t%0, %1, %2"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_alu_sletu"
  [(set (match_operand:SI 0 "register_operand" "=r")
    (leu:SI
      (match_operand:SI 1 "register_operand" "r")
      (match_operand:SI 2 "register_operand" "r")))]

  "TARGET_XCVALU && !TARGET_64BIT"
  "cv.sleu\t%0, %1, %2"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_alu_min"
  [(set (match_operand:SI 0 "register_operand" "=r")
    (smin:SI
      (match_operand:SI 1 "register_operand" "r")
      (match_operand:SI 2 "register_operand" "r")))]

  "TARGET_XCVALU && !TARGET_64BIT"
  "cv.min\t%0, %1, %2"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_alu_minu"
  [(set (match_operand:SI 0 "register_operand" "=r")
    (umin:SI
      (match_operand:SI 1 "register_operand" "r")
      (match_operand:SI 2 "register_operand" "r")))]

  "TARGET_XCVALU && !TARGET_64BIT"
  "cv.minu\t%0, %1, %2"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_alu_max"
  [(set (match_operand:SI 0 "register_operand" "=r")
    (smax:SI
      (match_operand:SI 1 "register_operand" "r")
      (match_operand:SI 2 "register_operand" "r")))]

  "TARGET_XCVALU && !TARGET_64BIT"
  "cv.max\t%0, %1, %2"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_alu_maxu"
  [(set (match_operand:SI 0 "register_operand" "=r")
    (umax:SI
      (match_operand:SI 1 "register_operand" "r")
      (match_operand:SI 2 "register_operand" "r")))]

  "TARGET_XCVALU && !TARGET_64BIT"
  "cv.maxu\t%0, %1, %2"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_alu_exths"
  [(set (match_operand:SI 0 "register_operand" "=r")
   (sign_extend:SI
     (truncate:HI
       (match_operand:HI 1 "register_operand" "r"))))]

  "TARGET_XCVALU && !TARGET_64BIT"
  "cv.exths\t%0, %1"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_alu_exthz"
  [(set (match_operand:SI 0 "register_operand" "=r")
   (zero_extend:SI
     (truncate:HI
       (match_operand:HI 1 "register_operand" "r"))))]

  "TARGET_XCVALU && !TARGET_64BIT"
  "cv.exthz\t%0, %1"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_alu_extbs"
  [(set (match_operand:SI 0 "register_operand" "=r")
   (sign_extend:SI
     (truncate:QI
       (match_operand:QI 1 "register_operand" "r"))))]

  "TARGET_XCVALU && !TARGET_64BIT"
  "cv.extbs\t%0, %1"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_alu_extbz"
  [(set (match_operand:SI 0 "register_operand" "=r")
   (zero_extend:SI
     (truncate:QI
   (match_operand:QI 1 "register_operand" "r"))))]

  "TARGET_XCVALU && !TARGET_64BIT"
  "cv.extbz\t%0, %1"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_alu_clip"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
   (unspec:SI [(match_operand:SI 1 "register_operand" "r,r")
               (match_operand:SI 2 "immediate_register_operand" "CV_alu_pow2,r")]
    UNSPEC_CV_ALU_CLIP))]

  "TARGET_XCVALU && !TARGET_64BIT"
  "@
  cv.clip\t%0,%1,%X2
  cv.clipr\t%0,%1,%2"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_alu_clipu"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
   (unspec:SI [(match_operand:SI 1 "register_operand" "r,r")
               (match_operand:SI 2 "immediate_register_operand" "CV_alu_pow2,r")]
    UNSPEC_CV_ALU_CLIPU))]

  "TARGET_XCVALU && !TARGET_64BIT"
  "@
  cv.clipu\t%0,%1,%X2
  cv.clipur\t%0,%1,%2"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_alu_addN"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
    (ashiftrt:SI
      (plus:SI
        (match_operand:SI 1 "register_operand" "r,0")
        (match_operand:SI 2 "register_operand" "r,r"))
      (and:SI (match_operand:QI 3 "csr_operand" "K,r")
              (const_int 31))))]

  "TARGET_XCVALU && !TARGET_64BIT"
  "@
  cv.addn\t%0,%1,%2,%3
  cv.addnr\t%0,%2,%3"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_alu_adduN"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
    (lshiftrt:SI
      (plus:SI
        (match_operand:SI 1 "register_operand" "r,0")
        (match_operand:SI 2 "register_operand" "r,r"))
      (and:SI (match_operand:QI 3 "csr_operand" "K,r")
              (const_int 31))))]

  "TARGET_XCVALU && !TARGET_64BIT"
  "@
  cv.addun\t%0,%1,%2,%3
  cv.addunr\t%0,%2,%3"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_alu_addRN"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
    (ashiftrt:SI
      (plus:SI
        (plus:SI
          (match_operand:SI 1 "register_operand" "r,0")
          (match_operand:SI 2 "register_operand" "r,r"))
        (if_then_else (eq (match_operand:QI 3 "csr_operand" "K,r")
                          (const_int 0))
          (const_int 1)
          (ashift:SI (const_int 1)
            (minus:QI (match_dup 3)
                      (const_int 1)))))
      (and:SI (match_dup 3)
              (const_int 31))))]

  "TARGET_XCVALU && !TARGET_64BIT"
  "@
  cv.addrn\t%0,%1,%2,%3
  cv.addrnr\t%0,%2,%3"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_alu_adduRN"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
    (lshiftrt:SI
      (plus:SI
        (plus:SI
          (match_operand:SI 1 "register_operand" "r,0")
          (match_operand:SI 2 "register_operand" "r,r"))
        (if_then_else (eq (match_operand:QI 3 "csr_operand" "K,r")
                          (const_int 0))
          (const_int 1)
          (ashift:SI (const_int 1)
            (minus:QI (match_dup 3)
                      (const_int 1)))))
      (and:SI (match_dup 3)
              (const_int 31))))]

  "TARGET_XCVALU && !TARGET_64BIT"
  "@
  cv.addurn\t%0,%1,%2,%3
  cv.addurnr\t%0,%2,%3"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_alu_subN"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
    (ashiftrt:SI
      (minus:SI
        (match_operand:SI 1 "register_operand" "r,0")
        (match_operand:SI 2 "register_operand" "r,r"))
      (and:SI (match_operand:QI 3 "csr_operand" "K,r")
              (const_int 31))))]

  "TARGET_XCVALU && !TARGET_64BIT"
  "@
  cv.subn\t%0,%1,%2,%3
  cv.subnr\t%0,%2,%3"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_alu_subuN"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
    (lshiftrt:SI
      (minus:SI
        (match_operand:SI 1 "register_operand" "r,0")
        (match_operand:SI 2 "register_operand" "r,r"))
      (and:SI (match_operand:QI 3 "csr_operand" "K,r")
              (const_int 31))))]

  "TARGET_XCVALU && !TARGET_64BIT"
  "@
  cv.subun\t%0,%1,%2,%3
  cv.subunr\t%0,%2,%3"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_alu_subRN"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
    (ashiftrt:SI
      (plus:SI
        (minus:SI
          (match_operand:SI 1 "register_operand" "r,0")
          (match_operand:SI 2 "register_operand" "r,r"))
        (if_then_else (eq (match_operand:QI 3 "csr_operand" "K,r")
                          (const_int 0))
          (const_int 1)
          (ashift:SI (const_int 1)
            (minus:QI (match_dup 3)
                      (const_int 1)))))
      (and:SI (match_dup 3)
              (const_int 31))))]

  "TARGET_XCVALU && !TARGET_64BIT"
  "@
  cv.subrn\t%0,%1,%2,%3
  cv.subrnr\t%0,%2,%3"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_alu_subuRN"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
    (lshiftrt:SI
      (plus:SI
        (minus:SI
          (match_operand:SI 1 "register_operand" "r,0")
          (match_operand:SI 2 "register_operand" "r,r"))
        (if_then_else (eq (match_operand:QI 3 "csr_operand" "K,r")
                          (const_int 0))
          (const_int 1)
          (ashift:SI (const_int 1)
            (minus:QI (match_dup 3)
                      (const_int 1)))))
      (and:SI (match_dup 3)
              (const_int 31))))]

  "TARGET_XCVALU && !TARGET_64BIT"
  "@
  cv.suburn\t%0,%1,%2,%3
  cv.suburnr\t%0,%2,%3"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

;; XCVELW builtins
(define_insn "riscv_cv_elw_elw_si"
  [(set (match_operand:SI 0 "register_operand" "=r")
   (unspec_volatile [(match_operand:SI 1 "move_operand" "p")]
     UNSPECV_CV_ELW))]

  "TARGET_XCVELW && !TARGET_64BIT"
  "cv.elw\t%0,%a1"

  [(set_attr "type" "load")
  (set_attr "mode" "SI")])

;; CORE-V Post Increment Load/ Store Instructions
;; Post Increment Register-Immediate and Register-Register Load/Store

(define_insn "*cv_load<mode>_postinc"
   [(set (match_operand:ANYI 0 "register_operand" "=r")
         (match_operand:ANYI 1 "mem_post_inc" "CV_mem_post"))]
  "TARGET_XCVMEM && riscv_legitimate_xcvmem_address_p (<MODE>mode, XEXP (operands[1], 0), (lra_in_progress || reload_completed))"
  "cv.<load>\t%0,%1"
  [(set_attr "type" "load")
   (set_attr "mode" "<MODE>")])

(define_insn "*cv_load_<optab><SHORT:mode>_postinc"
   [(set (match_operand:SI 0 "register_operand" "=r")
     (any_extend:SI (match_operand:SHORT 1 "mem_post_inc" "CV_mem_post")))]
  "TARGET_XCVMEM && riscv_legitimate_xcvmem_address_p (<MODE>mode, XEXP (operands[1], 0), (lra_in_progress || reload_completed))"
  "cv.<load><u>\t%0,%1"
  [(set_attr "type" "load")
   (set_attr "mode" "<MODE>")])

(define_insn "*cv_load<ANYF:mode>_postinc"
   [(set (match_operand:ANYF 0 "register_operand" "=r")
         (match_operand:ANYF 1 "mem_post_inc" "CV_mem_post"))]
  "TARGET_XCVMEM
   && riscv_legitimate_xcvmem_address_p (<MODE>mode, XEXP (operands[1], 0), (lra_in_progress || reload_completed))
   && (register_operand (operands[0], <MODE>mode)
       || reg_or_0_operand (operands[1], <MODE>mode))"
  "cv.<load>\t%0,%1"
  [(set_attr "type" "load")
   (set_attr "mode" "<MODE>")])

(define_insn "*cv_store<mode>_postinc"
   [(set (match_operand:ANYI 0 "mem_post_inc" "=CV_mem_post")
         (match_operand:ANYI 1 "register_operand" "r"))]
  "TARGET_XCVMEM && riscv_legitimate_xcvmem_address_p (<MODE>mode, XEXP (operands[0], 0), (lra_in_progress || reload_completed))"
  "cv.<store>\t%1,%0"
  [(set_attr "type" "store")
   (set_attr "mode" "<MODE>")])

(define_insn "*cv_store<ANYF:mode>_postinc"
   [(set (match_operand:ANYF 0 "mem_post_inc" "=CV_mem_post")
         (match_operand:ANYF 1 "register_operand" "r"))]
  "TARGET_XCVMEM
   && riscv_legitimate_xcvmem_address_p (<MODE>mode, XEXP (operands[0], 0), (lra_in_progress || reload_completed))
   && (register_operand (operands[0], <MODE>mode)
       || reg_or_0_operand (operands[1], <MODE>mode))"
  "cv.<store>\t%1,%0"
  [(set_attr "type" "store")
   (set_attr "mode" "<MODE>")])

;; Normal Register-Register Load/Store
(define_insn "*cv_load<mode>"
   [(set (match_operand:ANYI 0 "register_operand" "=r")
         (match_operand:ANYI 1 "mem_plus_reg" "CV_mem_plus"))]
  "TARGET_XCVMEM && riscv_legitimate_xcvmem_address_p (<MODE>mode, XEXP (operands[1], 0), (lra_in_progress || reload_completed))"
  "cv.<load>\t%0,%1"
  [(set_attr "type" "load")
   (set_attr "mode" "<MODE>")])

(define_insn "*cv_load<optab><SHORT:mode>"
   [(set (match_operand:SI 0 "register_operand" "=r")
     (any_extend:SI (match_operand:SHORT 1 "mem_plus_reg" "CV_mem_plus")))]
  "TARGET_XCVMEM && riscv_legitimate_xcvmem_address_p (<MODE>mode, XEXP (operands[1], 0), (lra_in_progress || reload_completed))"
  "cv.<load><u>\t%0,%1"
  [(set_attr "type" "load")
   (set_attr "mode" "<MODE>")])

(define_insn "*cv_load<ANYF:mode>"
   [(set (match_operand:ANYF 0 "register_operand" "=r")
         (match_operand:ANYF 1 "mem_plus_reg" "CV_mem_plus"))]
  "TARGET_XCVMEM
   && riscv_legitimate_xcvmem_address_p (<MODE>mode, XEXP (operands[1], 0), (lra_in_progress || reload_completed))
   && (register_operand (operands[0], <MODE>mode)
       || reg_or_0_operand (operands[1], <MODE>mode))"
  "cv.<load>\t%0,%1"
  [(set_attr "type" "load")
   (set_attr "mode" "<MODE>")])

(define_insn "*cv_store<mode>"
   [(set (match_operand:ANYI 0 "mem_plus_reg" "=CV_mem_plus")
     (match_operand:ANYI 1 "register_operand" "r"))]
  "TARGET_XCVMEM && riscv_legitimate_xcvmem_address_p (<MODE>mode, XEXP (operands[0], 0), (lra_in_progress || reload_completed))"
  "cv.<store>\t%1,%0"
  [(set_attr "type" "store")
   (set_attr "mode" "<MODE>")])

(define_insn "*cv_store<ANYF:mode>"
  [(set (match_operand:ANYF 0 "mem_plus_reg"     "=CV_mem_plus")
        (match_operand:ANYF 1 "register_operand" " r"))]
  "TARGET_XCVMEM
   && riscv_legitimate_xcvmem_address_p (<MODE>mode, XEXP (operands[0], 0), (lra_in_progress || reload_completed))
   && (register_operand (operands[0], <MODE>mode)
       || reg_or_0_operand (operands[1], <MODE>mode))"
  "cv.<store>\t%1,%0"
  [(set_attr "move_type" "store")
   (set_attr "mode" "<MODE>")])

;;
;; Generic RISC-V moves for XCVMEM
;;

(define_insn "*movsi_internal"
  [(set (match_operand:SI 0 "nonimmediate_nonpostinc" "=r,r,r,CV_mem_nopm,  *f,*f,*r,*CV_mem_nopm,r")
        (match_operand:SI 1 "move_operand"      " r,T,CV_mem_nopm,rJ,*r*J,*CV_mem_nopm,*f,*f,vp"))]
  "TARGET_XCVMEM && (register_operand (operands[0], SImode)
    || reg_or_0_operand (operands[1], SImode))
    && !(register_operand (operands[1], SImode)
         && reg_or_subregno (operands[1]) == VL_REGNUM)"
  { return riscv_output_move (operands[0], operands[1]); }
  [(set_attr "move_type" "move,const,load,store,mtc,fpload,mfc,fpstore,rdvlenb")
   (set_attr "mode" "SI")
   (set_attr "type" "move")
   (set_attr "ext" "base,base,base,base,f,f,f,f,vector")])

(define_insn "*movhi_internal"
  [(set (match_operand:HI 0 "nonimmediate_nonpostinc" "=r,r,r,CV_mem_nopm,  *f,*r,r")
        (match_operand:HI 1 "move_operand"            " r,T,CV_mem_nopm,rJ,*r*J,*f,vp"))]
  "TARGET_XCVMEM && (register_operand (operands[0], HImode)
    || reg_or_0_operand (operands[1], HImode))"
  { return riscv_output_move (operands[0], operands[1]); }
  [(set_attr "move_type" "move,const,load,store,mtc,mfc,rdvlenb")
   (set_attr "mode" "HI")
   (set_attr "type" "move")
   (set_attr "ext" "base,base,base,base,f,f,vector")])

(define_insn "*movqi_internal"
  [(set (match_operand:QI 0 "nonimmediate_nonpostinc" "=r,r,r,CV_mem_nopm,  *f,*r,r")
        (match_operand:QI 1 "move_operand"            " r,I,CV_mem_nopm,rJ,*r*J,*f,vp"))]
  "TARGET_XCVMEM && (register_operand (operands[0], QImode)
    || reg_or_0_operand (operands[1], QImode))"
  { return riscv_output_move (operands[0], operands[1]); }
  [(set_attr "move_type" "move,const,load,store,mtc,mfc,rdvlenb")
   (set_attr "mode" "QI")
   (set_attr "type" "move")
   (set_attr "ext" "base,base,base,base,f,f,vector")])

(define_insn "*movhf_hardfloat"
  [(set (match_operand:HF 0 "nonimmediate_nonpostinc" "=f,   f,f,f,CV_mem_nopm,CV_mem_nopm,*f,*r,  *r,*r,*CV_mem_nopm")
        (match_operand:HF 1 "move_operand"         " f,zfli,G,CV_mem_nopm,f,G,*r,*f,*G*r,*CV_mem_nopm,*r"))]
  "TARGET_ZFHMIN && TARGET_XCVMEM
   && (register_operand (operands[0], HFmode)
       || reg_or_0_operand (operands[1], HFmode))"
  { return riscv_output_move (operands[0], operands[1]); }
  [(set_attr "move_type" "fmove,fmove,mtc,fpload,fpstore,store,mtc,mfc,move,load,store")
   (set_attr "type" "fmove")
   (set_attr "mode" "HF")])

(define_insn "*movhf_softfloat"
  [(set (match_operand:HF 0 "nonimmediate_nonpostinc" "=f, r,r,CV_mem_nopm,*f,*r")
        (match_operand:HF 1 "move_operand"         " f,Gr,CV_mem_nopm,r,*r,*f"))]
  "!TARGET_ZFHMIN && TARGET_XCVMEM
   && (register_operand (operands[0], HFmode)
       || reg_or_0_operand (operands[1], HFmode))"
  { return riscv_output_move (operands[0], operands[1]); }
  [(set_attr "move_type" "fmove,move,load,store,mtc,mfc")
   (set_attr "type" "fmove")
   (set_attr "mode" "HF")])

(define_insn_and_split "*zero_extendhi<GPR:mode>2"
  [(set (match_operand:GPR    0 "register_operand"     "=r,r")
        (zero_extend:GPR
            (match_operand:HI 1 "nonimmediate_nonpostinc" " r,CV_mem_nopm")))]
  "!TARGET_ZBB && !TARGET_XTHEADBB && !TARGET_XTHEADMEMIDX && TARGET_XCVMEM"
  "@
   #
   lhu\t%0,%1"
  "&& reload_completed
   && REG_P (operands[1])
   && !paradoxical_subreg_p (operands[0])"
  [(set (match_dup 0)
        (ashift:GPR (match_dup 1) (match_dup 2)))
   (set (match_dup 0)
        (lshiftrt:GPR (match_dup 0) (match_dup 2)))]
  {
    operands[1] = gen_lowpart (<GPR:MODE>mode, operands[1]);
    operands[2] = GEN_INT(GET_MODE_BITSIZE(<GPR:MODE>mode) - 16);
  }
  [(set_attr "move_type" "shift_shift,load")
   (set_attr "type" "load")
   (set_attr "mode" "<GPR:MODE>")])

(define_insn "*zero_extendqi<SUPERQI:mode>2_internal"
  [(set (match_operand:SUPERQI 0 "register_operand"    "=r,r")
        (zero_extend:SUPERQI
            (match_operand:QI 1 "nonimmediate_nonpostinc" " r,CV_mem_nopm")))]
  "!TARGET_XTHEADMEMIDX && TARGET_XCVMEM"
  "@
   andi\t%0,%1,0xff
   lbu\t%0,%1"
  [(set_attr "move_type" "andi,load")
   (set_attr "type" "multi")
   (set_attr "mode" "<SUPERQI:MODE>")])

(define_insn_and_split "*extend<SHORT:mode><SUPERQI:mode>2"
  [(set (match_operand:SUPERQI   0 "register_operand"     "=r,r")
        (sign_extend:SUPERQI
            (match_operand:SHORT 1 "nonimmediate_nonpostinc" " r,CV_mem_nopm")))]
  "!TARGET_ZBB && !TARGET_XTHEADBB && !TARGET_XTHEADMEMIDX && TARGET_XCVMEM"
  "@
   #
   l<SHORT:size>\t%0,%1"
  "&& reload_completed
   && REG_P (operands[1])
   && !paradoxical_subreg_p (operands[0])"
  [(set (match_dup 0) (ashift:SI (match_dup 1) (match_dup 2)))
   (set (match_dup 0) (ashiftrt:SI (match_dup 0) (match_dup 2)))]
{
  operands[0] = gen_lowpart (SImode, operands[0]);
  operands[1] = gen_lowpart (SImode, operands[1]);
  operands[2] = GEN_INT (GET_MODE_BITSIZE (SImode)
                         - GET_MODE_BITSIZE (<SHORT:MODE>mode));
}
  [(set_attr "move_type" "shift_shift,load")
   (set_attr "type" "load")
   (set_attr "mode" "SI")])

(define_insn "*movdf_hardfloat_rv32"
  [(set (match_operand:DF 0 "nonimmediate_nonpostinc" "=f,   f,f,f,CV_mem_nopm,CV_mem_nopm,*zmvf,*zmvr,  *r,*r,*CV_mem_nopm")
        (match_operand:DF 1 "move_operand"         " f,zfli,G,CV_mem_nopm,f,G,*zmvr,*zmvf,*r*G,*CV_mem_nopm,*r"))]
  "!TARGET_64BIT && TARGET_DOUBLE_FLOAT && TARGET_XCVMEM
   && (register_operand (operands[0], DFmode)
       || reg_or_0_operand (operands[1], DFmode))"
  { return riscv_output_move (operands[0], operands[1]); }
  [(set_attr "move_type" "fmove,fmove,mtc,fpload,fpstore,store,mtc,mfc,move,load,store")
   (set_attr "type" "fmove")
   (set_attr "mode" "DF")])

(define_insn "*movdf_hardfloat_rv64"
  [(set (match_operand:DF 0 "nonimmediate_nonpostinc" "=f,   f,f,f,CV_mem_nopm,CV_mem_nopm,*f,*r,  *r,*r,*CV_mem_nopm")
        (match_operand:DF 1 "move_operand"         " f,zfli,G,CV_mem_nopm,f,G,*r,*f,*r*G,*CV_mem_nopm,*r"))]
  "TARGET_64BIT && TARGET_DOUBLE_FLOAT && TARGET_XCVMEM
   && (register_operand (operands[0], DFmode)
       || reg_or_0_operand (operands[1], DFmode))"
  { return riscv_output_move (operands[0], operands[1]); }
  [(set_attr "move_type" "fmove,fmove,mtc,fpload,fpstore,store,mtc,mfc,move,load,store")
   (set_attr "type" "fmove")
   (set_attr "mode" "DF")])

(define_insn "*movdf_softfloat"
  [(set (match_operand:DF 0 "nonimmediate_nonpostinc" "= r,r,CV_mem_nopm")
        (match_operand:DF 1 "move_operand"         " rG,CV_mem_nopm,rG"))]
  "!TARGET_DOUBLE_FLOAT && TARGET_XCVMEM
   && (register_operand (operands[0], DFmode)
       || reg_or_0_operand (operands[1], DFmode))"
  { return riscv_output_move (operands[0], operands[1]); }
  [(set_attr "move_type" "move,load,store")
   (set_attr "type" "fmove")
   (set_attr "mode" "DF")])

(define_insn "*movsf_hardfloat"
  [(set (match_operand:SF 0 "nonimmediate_nonpostinc" "=f,   f,f,f,CV_mem_nopm,CV_mem_nopm,*f,*r,  *r,*r,*CV_mem_nopm")
        (match_operand:SF 1 "move_operand"         " f,zfli,G,CV_mem_nopm,f,G,*r,*f,*G*r,*CV_mem_nopm,*r"))]
  "TARGET_HARD_FLOAT && TARGET_XCVMEM
   && (register_operand (operands[0], SFmode)
       || reg_or_0_operand (operands[1], SFmode))"
  { return riscv_output_move (operands[0], operands[1]); }
  [(set_attr "move_type" "fmove,fmove,mtc,fpload,fpstore,store,mtc,mfc,move,load,store")
   (set_attr "type" "fmove")
   (set_attr "mode" "SF")])

(define_insn "*movsf_softfloat"
  [(set (match_operand:SF 0 "nonimmediate_nonpostinc" "= r,r,CV_mem_nopm")
        (match_operand:SF 1 "move_operand"         " Gr,CV_mem_nopm,r"))]
  "!TARGET_HARD_FLOAT && TARGET_XCVMEM
   && (register_operand (operands[0], SFmode)
       || reg_or_0_operand (operands[1], SFmode))"
  { return riscv_output_move (operands[0], operands[1]); }
  [(set_attr "move_type" "move,load,store")
   (set_attr "type" "fmove")
   (set_attr "mode" "SF")])
