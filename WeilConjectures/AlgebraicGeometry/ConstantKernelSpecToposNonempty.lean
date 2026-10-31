/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.CategoryTheory.ConstantModuleFiniteTypeReflection

/-! Nondegeneracy of the pro-etale topos of a separably closed point.

This is Step 1 of the three-step proof of
`constantKernelConstructibilityReflection`.  By the fully faithful sheaf Yoneda
embedding of the subcanonical pro-etale site, an isomorphism between the initial
and terminal sheaves would give a morphism of schemes `Spec k ⟶ ∅`.

Source: literature/blueprint/latest/blueprint/sec-proetale-coefficients/
  sk-prop-sf-open-closed-triangle/det-def-sfb-bounded-constructible.proof.md,
  Counterexample construction: reduction to finite type on the separably closed point.
(blueprint: lem-sfb-constant-kernel-spec-topos-nonempty)
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale

/-- The sheaf topos of the pro-etale site of `Spec k` is nonempty: the initial and terminal
sheaves of sets are not isomorphic.

Proof. The pro-etale topology is subcanonical, so the lifted sheaf Yoneda embedding
`uliftYoneda` is fully faithful. Let `T = (𝟙 X : X → X)` and `E = (∅ → X)` as objects of
`X.ProEt`. An isomorphism `e : ⊥_ ≅ ⊤_` gives the composite
`yoneda T ⟶ ⊤_ ⟶ ⊥_ ⟶ yoneda E` (via `e.inv`), and fullness gives a morphism `T ⟶ E`
over `X`, hence a morphism of schemes `X ⟶ ∅`. Since `X = Spec k` has a point (`k` is a
field), its image would be a point of the empty scheme, a contradiction.
Source: blueprint det-def-sfb-bounded-constructible, Counterexample construction
(blueprint: lem-sfb-constant-kernel-spec-topos-nonempty). -/
theorem proEtaleSpec_topos_nonempty
    (k : Type u) [Field k] [IsSepClosed k]
    (X : Scheme.{u})
    (hX : X = Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))
    [HasColimitsOfShape (Discrete PEmpty.{1})
      (Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))] :
    ¬ Nonempty
      ((⊥_ (Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))) ≅
        (⊤_ (Sheaf (Scheme.ProEt.topology X) (Type (u + 1))))) := by
  subst X
  intro ⟨e⟩
  let X := Scheme.Spec.obj (op (CommRingCat.of k))
  let J := Scheme.ProEt.topology X
  let T : X.ProEt := Scheme.ProEt.mk (𝟙 X)
  let E : X.ProEt := Scheme.ProEt.mk (Scheme.emptyTo X)
  let Y := GrothendieckTopology.uliftYoneda.{u + 1} J
  let f : Y.obj T ⟶ Y.obj E :=
    terminal.from _ ≫ e.inv ≫ initial.to _
  let g : T ⟶ E := Y.preimage f
  have z : (∅ : Scheme.{u}) :=
    g.left (default : AlgebraicGeometry.Spec (CommRingCat.of k))
  exact isEmptyElim z

end AlgebraicGeometry.ProEtale
