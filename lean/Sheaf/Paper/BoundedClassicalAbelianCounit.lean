/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.ProEtale.Comparison
import WeilConjectures.CategoryTheory.DerivedCategory.PlusDevissage
import Mathlib.CategoryTheory.Triangulated.Adjunction
import Mathlib.CategoryTheory.Shift.Adjunction

/-! # Comparison counit for bounded classical abelian complexes

Source: Stacks Tag 099V, bounded truncation argument.
(blueprint: lem-sfb-bounded-classical-abelian-counit).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- The comparison counit identifies a bounded complex with classical abelian cohomology
with the pullback of its ordinary derived direct image.

Source: Stacks Tag 099V and the bounded truncation argument in
`lem-pe-classical-derived-counit`.
(blueprint: lem-sfb-bounded-classical-abelian-counit).

Proof: the underived comparison unit is invertible and pullback of an injective is
acyclic. Hence its bounded-below derived unit is invertible. On a classical sheaf,
write the sheaf as a comparison pullback; compatibility with single complexes and
the triangle identity make the derived counit invertible. Apply finite truncation
induction to the counit, using the distinguished triangles with single cohomology
objects as successive quotients. Finally use the compatibility of bounded-below
and unbounded ordinary derived direct image. This argument uses abelian sheaves
throughout, and requires neither finite coefficients nor completion. -/
theorem bounded_classical_abelian_counit (X : Scheme.{u})
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}))
    (a b : ℤ) [K.IsGE a] [K.IsLE b]
    (hK : ∀ q : ℤ, (comparisonUpperStar Ab.{u + 1} X).essImage
      ((DerivedCategory.Plus.homologyFunctor _ q).obj K)) :
    Nonempty ((comparisonUpperStar Ab.{u + 1} X).mapDerivedCategory.obj
      ((comparisonLowerStar Ab.{u + 1} X).rightDerivedFunctor.obj K.obj) ≅ K.obj) := by
  classical
  let A := Sheaf X.smallEtaleTopology Ab.{u + 1}
  let B := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}
  let L := comparisonUpperStar Ab.{u + 1} X
  let R := comparisonLowerStar Ab.{u + 1} X
  let adj := (comparisonAdjunction Ab.{u + 1} X).derivedPlus
  let : R.rightDerivedFunctorPlus.CommShift ℤ := adj.rightAdjointCommShift ℤ
  let : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  let : R.rightDerivedFunctorPlus.IsTriangulated := adj.isTriangulated_rightAdjoint
  have hunit (M : DerivedCategory.Plus A) : IsIso (adj.unit.app M) :=
    Adjunction.isIso_derivedPlus_unit_app_of_rightAcyclic
      (comparisonAdjunction Ab.{u + 1} X) (fun _ _ ↦ inferInstance)
      (fun I _ ↦ rightAcyclic_comparisonUpperStar_obj_of_injective Ab.{u + 1} X I) M
  let : IsIso adj.unit :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ adj.unit (fun M ↦ hunit M)
  let ff := adj.fullyFaithfulLOfIsIsoUnit
  let : L.mapDerivedCategoryPlus.Full := ff.full
  let : L.mapDerivedCategoryPlus.Faithful := ff.faithful
  have hsingle : ∀ G : B, L.essImage G →
      IsIso (adj.counit.app ((DerivedCategory.Plus.singleFunctor B 0).obj G)) := by
    rintro G ⟨M, ⟨e⟩⟩
    let e' : L.mapDerivedCategoryPlus.obj
        ((DerivedCategory.Plus.singleFunctor A 0).obj M) ≅
        (DerivedCategory.Plus.singleFunctor B 0).obj G :=
      (L.mapDerivedCategoryPlusSingleFunctor 0).app M ≪≫
        (DerivedCategory.Plus.singleFunctor B 0).mapIso e
    exact adj.isIso_counit_app_of_iso e'.symm
  have hc : IsIso (adj.counit.app K) :=
    DerivedCategory.Plus.isIso_app_of_bounded adj.counit L.essImage hsingle K a b hK
  exact ⟨L.mapDerivedCategory.mapIso (R.rightDerivedFunctorPlusCompatibility.app K).symm ≪≫
    (L.mapDerivedCategoryPlusCompatibility.app (R.rightDerivedFunctorPlus.obj K)).symm ≪≫
    DerivedCategory.Plus.ι.mapIso (asIso (adj.counit.app K))⟩

end AlgebraicGeometry.ProEtale
