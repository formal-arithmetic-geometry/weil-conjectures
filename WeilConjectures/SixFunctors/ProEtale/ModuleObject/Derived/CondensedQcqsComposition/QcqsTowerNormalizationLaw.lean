/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Functor.Category

/-! # The component formula for a normalized tower word

The formula is shared before specializing the categories and native functors.
(blueprint: new-k1-qcqs-tower-normalization-law)
-/

@[expose] public section
set_option autoImplicit false
open CategoryTheory
namespace AlgebraicGeometry.ProEtale.CondensedRing.CondensedQcqsComposition

/-- A normalized middle interchange followed by open factorization, proper composition,
and equality transport, stated with abstract categories and functors. Specializing to
native compactification functors gives exactly the component formula of `TowerNormalized`.
Source: latest blueprint, compact-support composition construction, and Stacks Tag 0F7J.
(blueprint: new-k1-qcqs-tower-normalization-law). -/
def TowerNormalizationLaw
    {C₀ C₁ C₂ C₃ C₄ C₅ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category C₃] [Category C₄] [Category C₅]
    (J₁ : C₀ ⥤ C₁) (R₁ : C₁ ⥤ C₂) (J₂ : C₂ ⥤ C₃) (R₂ : C₃ ⥤ C₄)
    (Jq : C₁ ⥤ C₅) (Rp : C₅ ⥤ C₃) (Je : C₀ ⥤ C₅) (Rc Rf : C₅ ⥤ C₄)
    (o : J₁ ⋙ Jq ⟶ Je) (r : Rp ⋙ R₂ ⟶ Rc) (e : Rc ⟶ Rf)
    (N : ∀ M : C₁, (J₂.obj (R₁.obj M) ⟶ Rp.obj (Jq.obj M)) → Prop)
    (K : C₀) (a : R₂.obj (J₂.obj (R₁.obj (J₁.obj K))) ⟶ Rf.obj (Je.obj K)) : Prop :=
  ∃ m, N (J₁.obj K) m ∧ a = R₂.map (m ≫ Rp.map (o.app K)) ≫
    r.app (Je.obj K) ≫ e.app (Je.obj K)

end AlgebraicGeometry.ProEtale.CondensedRing.CondensedQcqsComposition
