/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P5
-/
module

public import Sheaf.Algebra.Homology.LocalRHomSectionEquiv
public import Sheaf.Algebra.Homology.LocalRHomShiftSequence

/-! # Local RHom comparison and its cohomological lower bound

Source: Stacks Project, Tags 0A94, 0A95 and 0149.
(blueprint: lem-per-local-rhom-target-shift-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe uC vC u w wSlice
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open SheafOfModules
namespace CategoryTheory.LocalRHom

variable {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max uC vC u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC u}]
  (R : Sheaf J CommRingCat.{max uC vC u})
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max uC vC u}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max uC vC u}]
  [HasDerivedCategory.{w} (Mod.{uC, vC, u} J R)]
  [∀ U : C, HasDerivedCategory.{wSlice}
    (SheafOfModules.{max uC vC u} ((rings.{uC, vC, u} J R).over U))]


/-- Target shifts on the explicit local presheaf commute with its sheafification comparison.
Source: Stacks Project, Tags 0A8X, 0A95 and 0147.
(blueprint: lem-per-local-rhom-target-shift-comparison).

Proof: reindex the target components of Hom(L,I[t]) by t, without a scalar
factor. Its differential is the shifted Hom differential, since the target
differential is multiplied by (-1)^t. This gives a natural isomorphism of
section complexes and hence of their cohomology presheaves. K-injective
resolutions of shifted targets are compared by the localized augmentation;
quasi-isomorphism invariance descends the comparison to P. On cycle families
it is the identity after the shiftFunctorAdd' reindexing, so the section
comparison gives the first equation. Exact sheafification commutes with the
cycle quotient. The normalized target CommShift of internal Hom is the one
characterized by the same reindexing and the fixed coefficient comparison.
Thus its shift sequence, transported by Shifts.comparison, gives the second
equation. The identity and addition coherence follow from reindexing component
indices, with (-1)^(s+t)=(-1)^s*(-1)^t. -/
theorem target_shift_comparison
    (K : D.{uC, vC, u, w} J R) (L₀ : CochainComplex (Mod.{uC, vC, u} J R) ℤ)
    (k₀ : DerivedCategory.Q.obj L₀ ≅ K) :
    let P := Model.presheaf.{uC, vC, u, w} J R L₀
    let e := Sections.sectionEquiv.{uC, vC, u, w, wSlice} J R K L₀ k₀
    let σ := Model.sheafificationIsoOfRepresentative.{uC, vC, u, w} J R K L₀ k₀
    let S := Shifts.sequence.{uC, vC, u, w} J R K
    let τ := Shifts.comparison.{uC, vC, u, w} J R K
    ∃ ρ : ∀ t n : ℤ, shiftFunctor (D.{uC, vC, u, w} J R) t ⋙ P n ≅ P (n + t),
      (∀ (t n : ℤ) (M : D.{uC, vC, u, w} J R) (U : C)
        (x : ((P n).obj (M⟦t⟧)).obj (op U)),
        e (n + t) M U (((ρ t n).hom.app M).app (op U) x) =
          e n (M⟦t⟧) U x ≫ (res.{uC, vC, u, w, wSlice} J R U).map
            ((shiftFunctorAdd' (D.{uC, vC, u, w} J R) t n (n + t)
              (add_comm t n)).inv.app M)) ∧
      ∀ (t n : ℤ) (M : D.{uC, vC, u, w} J R),
        (sh.{uC, vC, u} J R).map ((ρ t n).hom.app M) ≫ (σ (n + t)).hom.app M =
          (σ n).hom.app (M⟦t⟧) ≫ (τ n).inv.app (M⟦t⟧) ≫
            (S.shiftIso t n (n + t) (add_comm t n)).hom.app M ≫
              (τ (n + t)).hom.app M := by
  sorry

end CategoryTheory.LocalRHom
