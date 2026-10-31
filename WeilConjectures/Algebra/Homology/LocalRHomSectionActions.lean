/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.LocalRHomSectionEquiv

/-! # Local RHom comparison and its cohomological lower bound

Source: Stacks Project, Tags 0A94, 0A95 and 0149.
(blueprint: lem-per-local-rhom-section-actions).
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


/-- The concrete local comparison respects derived arrows, local scalars and restriction.
Source: Stacks Project, Tags 0A8Y, 0A94 and 070I.
(blueprint: lem-per-local-rhom-section-actions).

Proof: on complexes with K-injective target, lift a cohomology class to a cycle.
The component formula for the Hom bifunctor gives the precomposition and
postcomposition formula for the associated local chain map. The canonical
cohomology comparison sends that class to its localization. Multiplication by
a section multiplies every component of the family by its restriction to the
slice object, which is precisely postcomposition with section multiplication.
Further restriction evaluates the same family on the composite slice object;
the comparison overFunctorMap is the identity on that family. The localization
factorizations resQ and resComp give the displayed conjugation formula.
The functorial K-injective resolution and the homology factorization are natural
for chain maps. Localization at quasi-isomorphisms then extends these equations
to every derived arrow; changing the representative by objObjPreimageIso gives
exactly sectionEquiv. Naturality of the descended multiplication transformation
and the composition comparison proves the other two equations after transport. -/
theorem section_actions
    (K : D.{uC, vC, u, w} J R) (L₀ : CochainComplex (Mod.{uC, vC, u} J R) ℤ)
    (k₀ : DerivedCategory.Q.obj L₀ ≅ K) :
    let P := Model.presheaf.{uC, vC, u, w} J R L₀
    let e := Sections.sectionEquiv.{uC, vC, u, w, wSlice} J R K L₀ k₀
    (∀ (n : ℤ) (M N : D.{uC, vC, u, w} J R) (v : M ⟶ N) (U : C)
        (x : ((P n).obj M).obj (op U)),
        e n N U (((P n).map v).app (op U) x) =
          e n M U x ≫ (res.{uC, vC, u, w, wSlice} J R U).map (v⟦n⟧')) ∧
      (∀ (n : ℤ) (M : D.{uC, vC, u, w} J R) (U : C) (a : R.obj.obj (op U))
        (x : ((P n).obj M).obj (op U)),
        e n M U (a • x) = e n M U x ≫
          (sectionDerivedMultiplication.{uC, vC, u, w, wSlice} J R U a).app (M⟦n⟧)) ∧
      (∀ (n : ℤ) (M : D.{uC, vC, u, w} J R) (U V : C) (f : V ⟶ U)
        (x : ((P n).obj M).obj (op U)),
        e n M V (((P n).obj M).map f.op x) =
          restrictHom.{uC, vC, u, w, wSlice} J R f (e n M U x)) := by
  sorry

end CategoryTheory.LocalRHom
