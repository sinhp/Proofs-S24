/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import ProofsS24.Theory.ModEq.Lemmas
import ProofsS24.Tactic.Extra.Basic

attribute [aesop safe (rule_sets [extra]) (apply (transparency := instances))]
  Int.modEq_fac_zero Int.modEq_fac_zero' Int.modEq_zero_fac Int.modEq_zero_fac'
  Int.modEq_add_fac_self Int.modEq_add_fac_self' Int.modEq_add_fac_self'' Int.modEq_add_fac_self'''
  Int.modEq_sub_fac_self Int.modEq_sub_fac_self' Int.modEq_sub_fac_self'' Int.modEq_sub_fac_self'''
  Int.modEq_add_fac_self_symm Int.modEq_add_fac_self_symm' Int.modEq_add_fac_self_symm'' Int.modEq_add_fac_self_symm'''
  Int.modEq_sub_fac_self_symm Int.modEq_sub_fac_self_symm' Int.modEq_sub_fac_self_symm'' Int.modEq_sub_fac_self_symm'''
  Int.ModEq.add_right Int.ModEq.add_left
  Int.ModEq.sub_right Int.ModEq.sub_left
  Int.ModEq.refl
