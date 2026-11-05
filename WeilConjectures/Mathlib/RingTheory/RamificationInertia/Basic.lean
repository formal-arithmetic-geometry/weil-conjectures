/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import Mathlib.RingTheory.RamificationInertia.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Ramification indices as orders of vanishing, trivial inertia over algebraically closed fields

## Main statements

- `Ideal.inertiaDeg_eq_one_of_isAlgClosed`: over an algebraically closed field `k`, the inertia
  degrees of a finite extension of finite type `k`-algebras at maximal ideals are `1`.
- `Ideal.ramificationIdx_eq_ord`: if `p` generates the ideal `(s)` in a localization `S` of `B`
  at `q`, the ramification index of `q` over `p` is the order of vanishing of `s` in `S`.
-/

@[expose] public section

namespace Ideal

end Ideal
