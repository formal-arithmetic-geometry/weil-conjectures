/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P5
-/
module

public import Sheaf.Algebra.Homology.LocalRHomSectionEquiv

/-! # Local RHom comparison and its cohomological lower bound

Source: Stacks Project, Tags 0A94, 0A95 and 0149.
(blueprint: lem-per-local-rhom-cycle-unit-normalization).
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


/-- The fixed sheafification comparison has its prescribed cycle-unit normalization.
Source: Stacks Project, Tags 03EI, 0A94 and 0A95.
(blueprint: lem-per-local-rhom-cycle-unit-normalization).

Proof: first take the source L₀ and a target equal to its fixed K-injective
resolution. The homology/sheafification comparison is induced by the maps on
cycles and their quotient. Its composite with the sheafification unit sends the
section class of a cycle to its cohomology class. The kernel equation for the
differential constructs sectionCycle directly, and sectionCycle_i identifies it
with the original component family. The canonical section comparison sends that class to the
localized sheafCycleMap. For a different K-injective target, the augmentation
is a quasi-isomorphism and its Hom map is a quasi-isomorphism; cancelling its
localized isomorphism gives kInjectiveRepresentativeIso. For a different source
representative, lift the comparison to chain maps into K-injective resolutions.
The component formula for the Hom bifunctor gives precomposition by k.inv;
localization naturality and the fixed coefficient factorization identify the
transported cohomology class. Applying these two transports to the first
equation gives the displayed formula for every representative. -/
theorem cycle_unit_normalization
    (K : D.{uC, vC, u, w} J R) (L₀ : CochainComplex (Mod.{uC, vC, u} J R) ℤ)
    (k₀ : DerivedCategory.Q.obj L₀ ≅ K) :
    let P := Model.presheaf.{uC, vC, u, w} J R L₀
    let e := Sections.sectionEquiv.{uC, vC, u, w, wSlice} J R K L₀ k₀
    let σ := Model.sheafificationIsoOfRepresentative.{uC, vC, u, w} J R K L₀ k₀
    ∀ (L I : CochainComplex (Mod.{uC, vC, u} J R) ℤ) [I.IsKInjective]
      (k : DerivedCategory.Q.obj L ≅ K) (n : ℤ) (U : C)
      (z : ((homComplex.{uC, vC, max uC vC u, max uC vC u}
        (R := R) L I).cycles n).val.obj (op U)),
      let h := Model.kInjectiveRepresentativeIso.{uC, vC, u, w} J R L I
      let a := Cocycle.sheafCycleMap.{uC, vC, u, wSlice} J R L I U n z
      ((σ n).inv.app (DerivedCategory.Q.obj I)).val.app (op U)
                (((DerivedCategory.homologyFunctor (Mod.{uC, vC, u} J R) n).map
                  ((derivedInternalHomOfUniverses.{uC, vC, u, w} J R).map
                    (Prod.mkHom k.inv.op (𝟙 (DerivedCategory.Q.obj I))))).val.app (op U)
                    (cycleClass.{uC, vC, u, w} J R L I h n U z)) =
                ((PresheafOfModules.sheafificationAdjunction.{max uC vC u}
                  (𝟙 (rings.{uC, vC, u} J R).obj)).unit.app
                    ((P n).obj (DerivedCategory.Q.obj I))).app (op U)
                      ((e n (DerivedCategory.Q.obj I) U).symm
                        ((res.{uC, vC, u, w, wSlice} J R U).map k.inv ≫ localizedCocycle.{uC, vC, u,
                          w, wSlice} J R L I n U a)) := by
  sorry

end CategoryTheory.LocalRHom
