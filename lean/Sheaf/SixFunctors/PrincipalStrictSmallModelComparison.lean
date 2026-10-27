/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.RegularRoosKoszulData
public import Sheaf.CategoryTheory.RingedKoszulSmallModelCompletedTensor
public import Sheaf.CategoryTheory.RingedKoszulSystem

/-! # Normalized strict Koszul comparison on the small model

Source: Stacks Project, Tags 099B, 0A0E and 0941.
(blueprint: lem-sf-principal-strict-small-model-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
universe c v r w w₀
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.RegularRoosKoszul
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max c v r})
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasDerivedCategory.{w} (Modules.{c, v, r} R)]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ Modules.{c, v, r} R)]

variable [∀ W : C, HasSheafify (J.over W) AddCommGrpCat.{max c v r}]
  [∀ W : C, HasSheafify (J.over W) CommRingCat.{max c v r}]
  [∀ W : C, (J.over W).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ W : C, HasDerivedCategory.{w}
  (SheafOfModules.{max c v r} ((sheafCompose (J.over W)
    (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj (R.over W)))]

variable
  [HasSheafify ((equivSmallModel.{max c v r} C).inverse.inducedTopology J)
    AddCommGrpCat.{max c v r}]

variable
  [HasDerivedCategory.{w₀} ((SheafOfModules.{max c v r}
    ((sheafCompose ((equivSmallModel.{max c v r} C).inverse.inducedTopology J)
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj
        (KoszulSmallModel.ring.{c, v, max c v r} R))))]
  [HasDerivedCategory.{w₀} (ℕᵒᵖ ⥤ (SheafOfModules.{max c v r}
    ((sheafCompose ((equivSmallModel.{max c v r} C).inverse.inducedTopology J)
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj
        (KoszulSmallModel.ring.{c, v, max c v r} R))))]

/-- The small-site singleton presentation agrees with the actual principal total limit,
including the normalized strict augmentation. This comparison asserts no reflection or
completeness property and requires neither regularity nor exact products.

Source: Stacks Project, algebraization.tex, proof of Tag 0A0E, and
sites-cohomology.tex, Tag 0941.
(blueprint: lem-sf-principal-strict-small-model-comparison).

Proof: restrict module sheaves to the canonical coefficient-universe small model.
The exact equivalence commutes with the ordinary inverse limit and carries K-injective
strict towers to K-injective strict towers, since its inverse is exact. Its derived
functor therefore compares the two total right-derived limits by their universal
properties, compatibly with their comparisons. On the small site, evaluation at one
identifies the dual of the positive singleton Koszul factor with the negative principal
cone: in degree -1 the Hom differential is -(-1)^(-1), giving the positive scalar
multiplication. Dual transitions are (t,1), and the dual projection is the degree-zero
inclusion. Tensor symmetry identifies the two strict tensor towers; its sign on the
augmentation is one. Transport this augmented tower through the exact module
restriction equivalence and use D.tensorFactors. Naturality of the right-derived
comparison at the ordinary constant/limit unit proves the displayed unit equation.
Naturality of D.unit changes from the localized transported representative to the
image of Q(Q). The same formulas apply to the empty site, zero ring, zero complex and
zero or invertible sections; no quotient or regularity argument is used. -/
theorem principal_strict_small_model_comparison
    (t : (SheafOfModules.unit (ring.{c, v, r} R)).sections)
    (Q : CochainComplex (Modules.{c, v, r} R) ℤ)
    (D : RingedKoszulLimitPresentation (KoszulSmallModel.ring.{c, v, max c v r} R) 1
      (fun _ ↦ KoszulSmallModel.globalSection.{c, v, max c v r} R ⟨t.val, t.property⟩)) :
    ∃ e : (KoszulSmallModel.derivedEquiv.{c, v, max c v r, w, w₀} R).functor.obj
        (koszulCompletion R Q t) ≅
        D.completion.obj ((KoszulSmallModel.derivedEquiv.{c, v, max c v r, w, w₀} R).functor.obj
          (DerivedCategory.Q.obj Q)),
      (KoszulSmallModel.derivedEquiv.{c, v, max c v r, w, w₀} R).functor.map
          (koszulUnit.{c, v, r, w} R (DerivedCategory.Q.obj Q) Q (Iso.refl _) t) ≫
        e.hom = D.unit ((KoszulSmallModel.derivedEquiv.{c, v, max c v r, w, w₀} R).functor.obj
          (DerivedCategory.Q.obj Q)) := by sorry

end CategoryTheory.RegularRoosKoszul
