;; Machine description for CORE-V vendor extensions.
;; Copyright (C) 2023 Free Software Foundation, Inc.

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
  (unspec_volatile [(mem:SI (match_operand:SI 1 "address_operand" "p"))]
  UNSPECV_CV_ELW))]

  "TARGET_XCVELW && !TARGET_64BIT"
  "cv.elw\t%0,%a1"

  [(set_attr "type" "load")
  (set_attr "mode" "SI")])

;; XCVBI Builtins
(define_insn "cv_branch<mode>"
  [(set (pc)
	(if_then_else
	 (match_operator 1 "equality_operator"
			 [(match_operand:X 2 "register_operand" "r")
			  (match_operand:X 3 "const_int5s_operand" "CV_bi_sign5")])
	 (label_ref (match_operand 0 "" ""))
	 (pc)))]
  "TARGET_XCVBI"
  "cv.b%C1imm\t%2,%3,%0"
  [(set_attr "type" "branch")
   (set_attr "mode" "none")])

;;CORE-V Post Increment Load/ Store
;; Post Increment Register-Immediate and Register-Register Load/Store
(define_insn "cv_load<mode>_postinc"
   [(set (match_operand:ANYI 0 "register_operand" "=r")
         (match_operand:ANYI 1 "mem_post_inc" "CV_mem_post"))]
  "TARGET_XCVMEM && riscv_legitimate_xcvmem_address_p (<MODE>mode, XEXP (operands[1], 0), (lra_in_progress || reload_completed))"
  "cv.<load>\t%0,%1"
  [(set_attr "type" "load")
   (set_attr "mode" "<MODE>")])

(define_insn "cv_load_<optab><SHORT:mode>_postinc"
   [(set (match_operand:SI 0 "register_operand" "=r")
     (any_extend:SI (match_operand:SHORT 1 "mem_post_inc" "CV_mem_post")))]
  "TARGET_XCVMEM && riscv_legitimate_xcvmem_address_p (<MODE>mode, XEXP (operands[1], 0), (lra_in_progress || reload_completed))"
  "cv.<load><u>\t%0,%1"
  [(set_attr "type" "load")
   (set_attr "mode" "<MODE>")])

(define_insn "cv_loadsf_postinc_hardfloat"
   [(set (match_operand:SF 0 "register_operand" "=r")
         (match_operand:SF 1 "mem_post_inc" "CV_mem_post"))]
  "TARGET_HARD_FLOAT && TARGET_XCVMEM
   && riscv_legitimate_xcvmem_address_p (SFmode, XEXP (operands[1], 0), (lra_in_progress || reload_completed))
   && (register_operand (operands[0], SFmode)
       || reg_or_0_operand (operands[1], SFmode))"
  "cv.lw\t%0,%1"
  [(set_attr "type" "load")
   (set_attr "mode" "SF")])

(define_insn "cv_loadsf_postinc_softfloat"
   [(set (match_operand:SF 0 "register_operand" "=r")
         (match_operand:SF 1 "mem_post_inc" "CV_mem_post"))]
  "!TARGET_HARD_FLOAT && TARGET_XCVMEM
   && riscv_legitimate_xcvmem_address_p (SFmode, XEXP (operands[1], 0), (lra_in_progress || reload_completed))
   && (register_operand (operands[0], SFmode)
       || reg_or_0_operand (operands[1], SFmode))"
  "cv.lw\t%0,%1"
  [(set_attr "type" "load")
   (set_attr "mode" "SF")])

(define_insn "cv_loadhf_postinc_hardfloat"
   [(set (match_operand:HF 0 "register_operand" "=r")
         (match_operand:HF 1 "mem_post_inc" "CV_mem_post"))]
  "TARGET_HARD_FLOAT && TARGET_XCVMEM
   && riscv_legitimate_xcvmem_address_p (HFmode, XEXP (operands[1], 0), (lra_in_progress || reload_completed))
   && (register_operand (operands[0], HFmode)
       || reg_or_0_operand (operands[1], HFmode))"
  "cv.lh\t%0,%1"
  [(set_attr "type" "load")
   (set_attr "mode" "HF")])

(define_insn "cv_loadhf_postinc_softfloat"
   [(set (match_operand:HF 0 "register_operand" "=r")
         (match_operand:HF 1 "mem_post_inc" "CV_mem_post"))]
  "!TARGET_HARD_FLOAT && TARGET_XCVMEM
   && riscv_legitimate_xcvmem_address_p (HFmode, XEXP (operands[1], 0), (lra_in_progress || reload_completed))
   && (register_operand (operands[0], HFmode)
       || reg_or_0_operand (operands[1], HFmode))"
  "cv.lh\t%0,%1"
  [(set_attr "type" "load")
   (set_attr "mode" "HF")])

(define_insn "cv_store<mode>_postinc"
   [(set (match_operand:ANYI 0 "mem_post_inc" "=CV_mem_post")
         (match_operand:ANYI 1 "register_operand" "r"))]
  "TARGET_XCVMEM && riscv_legitimate_xcvmem_address_p (<MODE>mode, XEXP (operands[0], 0), (lra_in_progress || reload_completed))"
  "cv.<store>\t%1,%0"
  [(set_attr "type" "store")
   (set_attr "mode" "<MODE>")])

(define_insn "cv_storesf_postinc_hardfloat"
   [(set (match_operand:SF 0 "mem_post_inc" "=CV_mem_post")
         (match_operand:SF 1 "register_operand" "r"))]
  "TARGET_HARD_FLOAT && TARGET_XCVMEM
   && riscv_legitimate_xcvmem_address_p (SFmode, XEXP (operands[0], 0), (lra_in_progress || reload_completed))
   && (register_operand (operands[0], SFmode)
       || reg_or_0_operand (operands[1], SFmode))"
  "cv.sw\t%1,%0"
  [(set_attr "type" "store")
   (set_attr "mode" "SF")])

(define_insn "cv_storesf_postinc_softfloat"
   [(set (match_operand:SF 0 "mem_post_inc" "=CV_mem_post")
         (match_operand:SF 1 "register_operand" "r"))]
  "!TARGET_HARD_FLOAT && TARGET_XCVMEM
   && riscv_legitimate_xcvmem_address_p (SFmode, XEXP (operands[0], 0), (lra_in_progress || reload_completed))
   && (register_operand (operands[0], SFmode)
       || reg_or_0_operand (operands[1], SFmode))"
  "cv.sw\t%1,%0"
  [(set_attr "type" "store")
   (set_attr "mode" "SF")])

(define_insn "cv_storehf_postinc_hardfloat"
   [(set (match_operand:HF 0 "mem_post_inc" "=CV_mem_post")
         (match_operand:HF 1 "register_operand" "r"))]
  "TARGET_HARD_FLOAT && TARGET_XCVMEM
   && riscv_legitimate_xcvmem_address_p (HFmode, XEXP (operands[0], 0), (lra_in_progress || reload_completed))
   && (register_operand (operands[0], HFmode)
       || reg_or_0_operand (operands[1], HFmode))"
  "cv.sh\t%1,%0"
  [(set_attr "type" "store")
   (set_attr "mode" "HF")])

(define_insn "cv_storehf_postinc_softfloat"
   [(set (match_operand:HF 0 "mem_post_inc" "=CV_mem_post")
         (match_operand:HF 1 "register_operand" "r"))]
  "!TARGET_HARD_FLOAT && TARGET_XCVMEM
   && riscv_legitimate_xcvmem_address_p (HFmode, XEXP (operands[0], 0), (lra_in_progress || reload_completed))
   && (register_operand (operands[0], HFmode)
       || reg_or_0_operand (operands[1], HFmode))"
  "cv.sh\t%1,%0"
  [(set_attr "type" "store")
   (set_attr "mode" "HF")])

;; Normal Register-Register Load/Store
(define_insn "cv_load<mode>"
   [(set (match_operand:ANYI 0 "register_operand" "=r")
         (match_operand:ANYI 1 "mem_plus_reg" "CV_mem_plus"))]
  "TARGET_XCVMEM && riscv_legitimate_xcvmem_address_p (<MODE>mode, XEXP (operands[1], 0), (lra_in_progress || reload_completed))"
  "cv.<load>\t%0,%1"
  [(set_attr "type" "load")
   (set_attr "mode" "<MODE>")])

(define_insn "cv_load_<optab><SHORT:mode>"
   [(set (match_operand:SI 0 "register_operand" "=r")
     (any_extend:SI (match_operand:SHORT 1 "mem_plus_reg" "CV_mem_plus")))]
  "TARGET_XCVMEM && riscv_legitimate_xcvmem_address_p (<MODE>mode, XEXP (operands[1], 0), (lra_in_progress || reload_completed))"
  "cv.<load><u>\t%0,%1"
  [(set_attr "type" "load")
   (set_attr "mode" "<MODE>")])

(define_insn "cv_loadsf_hardfloat"
   [(set (match_operand:SF 0 "register_operand" "=r")
         (match_operand:SF 1 "mem_plus_reg" "CV_mem_plus"))]
  "TARGET_HARD_FLOAT && TARGET_XCVMEM
   && riscv_legitimate_xcvmem_address_p (SFmode, XEXP (operands[1], 0), (lra_in_progress || reload_completed))
   && (register_operand (operands[0], SFmode)
       || reg_or_0_operand (operands[1], SFmode))"
  "cv.lw\t%0,%1"
  [(set_attr "type" "load")
   (set_attr "mode" "SF")])

(define_insn "cv_loadsf_softfloat"
   [(set (match_operand:SF 0 "register_operand" "=r")
         (match_operand:SF 1 "mem_plus_reg" "CV_mem_plus"))]
  "!TARGET_HARD_FLOAT && TARGET_XCVMEM
   && riscv_legitimate_xcvmem_address_p (SFmode, XEXP (operands[1], 0), (lra_in_progress || reload_completed))
   && (register_operand (operands[0], SFmode)
       || reg_or_0_operand (operands[1], SFmode))"
  "cv.lw\t%0,%1"
  [(set_attr "type" "load")
   (set_attr "mode" "SF")])

(define_insn "cv_loadhf_hardfloat"
   [(set (match_operand:HF 0 "register_operand" "=r")
         (match_operand:HF 1 "mem_plus_reg" "CV_mem_plus"))]
  "TARGET_HARD_FLOAT && TARGET_XCVMEM
   && riscv_legitimate_xcvmem_address_p (HFmode, XEXP (operands[1], 0), (lra_in_progress || reload_completed))
   && (register_operand (operands[0], HFmode)
       || reg_or_0_operand (operands[1], HFmode))"
  "cv.lh\t%0,%1"
  [(set_attr "type" "load")
   (set_attr "mode" "HF")])

(define_insn "cv_loadhf_softfloat"
   [(set (match_operand:HF 0 "register_operand" "=r")
         (match_operand:HF 1 "mem_plus_reg" "CV_mem_plus"))]
  "!TARGET_HARD_FLOAT && TARGET_XCVMEM
   && riscv_legitimate_xcvmem_address_p (HFmode, XEXP (operands[1], 0), (lra_in_progress || reload_completed))
   && (register_operand (operands[0], HFmode)
       || reg_or_0_operand (operands[1], HFmode))"
  "cv.lh\t%0,%1"
  [(set_attr "type" "load")
   (set_attr "mode" "HF")])

(define_insn "cv_store<mode>"
   [(set (match_operand:ANYI 0 "mem_plus_reg" "=CV_mem_plus")
     (match_operand:ANYI 1 "register_operand" "r"))]
  "TARGET_XCVMEM && riscv_legitimate_xcvmem_address_p (<MODE>mode, XEXP (operands[0], 0), (lra_in_progress || reload_completed))"
  "cv.<store>\t%1,%0"
  [(set_attr "type" "store")
   (set_attr "mode" "<MODE>")])

(define_insn "cv_storesf_hardfloat"
  [(set (match_operand:SF 0 "mem_plus_reg"     "=CV_mem_plus")
        (match_operand:SF 1 "register_operand" " r"))]
  "TARGET_HARD_FLOAT && TARGET_XCVMEM
   && riscv_legitimate_xcvmem_address_p (SFmode, XEXP (operands[0], 0), (lra_in_progress || reload_completed))
   && (register_operand (operands[0], SFmode)
       || reg_or_0_operand (operands[1], SFmode))"
  "cv.sw\t%1,%0"
  [(set_attr "move_type" "store")
   (set_attr "mode" "SF")])

(define_insn "cv_storesf_softfloat"
  [(set (match_operand:SF 0 "mem_plus_reg"     "=CV_mem_plus")
        (match_operand:SF 1 "register_operand" " r"))]
  "!TARGET_HARD_FLOAT && TARGET_XCVMEM
   && riscv_legitimate_xcvmem_address_p (SFmode, XEXP (operands[0], 0), (lra_in_progress || reload_completed))
   && (register_operand (operands[0], SFmode)
       || reg_or_0_operand (operands[1], SFmode))"
  "cv.sw\t%1,%0"
  [(set_attr "move_type" "store")
   (set_attr "mode" "SF")])

(define_insn "cv_storehf_hardfloat"
  [(set (match_operand:HF 0 "mem_plus_reg"     "=CV_mem_plus")
        (match_operand:HF 1 "register_operand" " r"))]
  "TARGET_HARD_FLOAT && TARGET_XCVMEM
   && riscv_legitimate_xcvmem_address_p (HFmode, XEXP (operands[0], 0), (lra_in_progress || reload_completed))
   && (register_operand (operands[0], HFmode)
       || reg_or_0_operand (operands[1], HFmode))"
  "cv.sh\t%1,%0"
  [(set_attr "move_type" "store")
   (set_attr "mode" "HF")])

(define_insn "cv_storehf_softfloat"
  [(set (match_operand:HF 0 "mem_plus_reg"     "=CV_mem_plus")
        (match_operand:HF 1 "register_operand" " r"))]
  "!TARGET_HARD_FLOAT && TARGET_XCVMEM
   && riscv_legitimate_xcvmem_address_p (HFmode, XEXP (operands[0], 0), (lra_in_progress || reload_completed))
   && (register_operand (operands[0], HFmode)
       || reg_or_0_operand (operands[1], HFmode))"
  "cv.sh\t%1,%0"
  [(set_attr "move_type" "store")
   (set_attr "mode" "HF")])
