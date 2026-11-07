/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionMatchingSections

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # The completed matching-ring comparison

Source: Stacks Project, Tags 05ER and 05EU.
(blueprint: def-sbc-completed-matching-ring-map)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {U : (Spec (.of A)).Opens} {Y : Scheme.{u}} {q : Y ⟶ U.toScheme}
variable {E : Scheme.{u}} {s : E ⟶ Spec
  (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))}
variable (D : CompletionGluingData A U q E s)

/-- The second matching projection and the completed structural map agree over A.
Source: Stacks Project, Tag 05ER, definition of the comparison.
(blueprint: def-sbc-completed-matching-ring-map)

Proof: project the defining pullback lift for baseMap to its second component,
then use functoriality of global sections and naturality of the affine counit. -/
theorem completedRingMap_condition :
    D.baseMap ≫ pullback.snd
      (pullback.fst q (completionSpecMap A ∣_ U)).appTop D.toCompleted.appTop =
    CommRingCat.ofHom (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) ≫
      (ΓSpecIso (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))).inv ≫
        s.appTop := by
  simp only [baseMap, Category.assoc, pullback.lift_snd, Hom.comp_appTop]
  rw [← Category.assoc, ← Category.assoc, ΓSpecIso_inv_naturality]

/-- The canonical scalar-extension map from matching sections to completed sections.
The ring pushout is the tensor product over A; its maps are the second matching
projection and the structural map C → Γ(E).
Source: Stacks Project, Tags 05ER (the comparison Ψ) and 05EU (algebra structure).
(blueprint: def-sbc-completed-matching-ring-map) -/
noncomputable def completedRingMap :
    pushout D.baseMap (CommRingCat.ofHom
      (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))) ⟶ Γ(E, ⊤) :=
  pushout.desc
    (pullback.snd (pullback.fst q (completionSpecMap A ∣_ U)).appTop D.toCompleted.appTop)
    ((ΓSpecIso (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))).inv ≫ s.appTop)
    D.completedRingMap_condition

end AlgebraicGeometry.Scheme.CompletionGluingData
