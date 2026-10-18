/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q70
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Groupoid laws for morphisms of schemes

Source: Stacks Project, Groupoid Schemes, Definition (Tag 0231), and the
preceding explicit groupoid axioms (blueprint: def-a1-scheme-groupoid-laws).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The maps `s`, `t`, `e`, `i`, `c` make a groupoid on points of every test scheme.
Source: Stacks Project, `groupoids.tex`, Definition `definition-groupoid` and the
preceding axioms (blueprint: def-a1-scheme-groupoid-laws).

The first factor of `pullback s t` is the later arrow: `c(a,b)` means `a` after `b`.
The source and target identities are morphism equalities. The unit, inverse and
associativity laws are written on arbitrary test schemes, using points of the
chosen pullback. In `assoc`, `p=(a,b)`, `q=(b,d)`, `r=(c(a,b),d)`, and
`z=(a,c(b,d))`. The universal property of the pullback supplies each composable
pair, so these equations assert all groupoid laws. Precomposition with a morphism
of test schemes preserves all operations, since they are induced by scheme maps. -/
structure IsGroupoid {U R : Scheme.{u}} (s t : R ⟶ U) (e : U ⟶ R) (i : R ⟶ R)
    (c : pullback s t ⟶ R) : Prop where
  source_id : e ≫ s = 𝟙 U
  target_id : e ≫ t = 𝟙 U
  source_inv : i ≫ s = t
  target_inv : i ≫ t = s
  source_comp : c ≫ s = pullback.snd s t ≫ s
  target_comp : c ≫ t = pullback.fst s t ≫ t
  id_comp : ∀ (H : Scheme.{u}) (a : H ⟶ R) (p : H ⟶ pullback s t),
    p ≫ pullback.fst s t = a ≫ t ≫ e →
    p ≫ pullback.snd s t = a → p ≫ c = a
  comp_id : ∀ (H : Scheme.{u}) (a : H ⟶ R) (p : H ⟶ pullback s t),
    p ≫ pullback.fst s t = a →
    p ≫ pullback.snd s t = a ≫ s ≫ e → p ≫ c = a
  inv_comp : ∀ (H : Scheme.{u}) (a : H ⟶ R) (p : H ⟶ pullback s t),
    p ≫ pullback.fst s t = a ≫ i →
    p ≫ pullback.snd s t = a → p ≫ c = a ≫ s ≫ e
  comp_inv : ∀ (H : Scheme.{u}) (a : H ⟶ R) (p : H ⟶ pullback s t),
    p ≫ pullback.fst s t = a →
    p ≫ pullback.snd s t = a ≫ i → p ≫ c = a ≫ t ≫ e
  assoc : ∀ (H : Scheme.{u}) (p q r z : H ⟶ pullback s t),
    p ≫ pullback.snd s t = q ≫ pullback.fst s t →
    r ≫ pullback.fst s t = p ≫ c →
    r ≫ pullback.snd s t = q ≫ pullback.snd s t →
    z ≫ pullback.fst s t = p ≫ pullback.fst s t →
    z ≫ pullback.snd s t = q ≫ c → r ≫ c = z ≫ c

end AlgebraicGeometry.Scheme
