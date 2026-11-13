/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.CategoryTheory.Preadditive.LeftExact
import WeilConjectures.AlgebraicGeometry.StrictPerfectClosedPushforwardStalkResolution
import WeilConjectures.Algebra.Category.ModuleCat.TorSymmetry
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardCokernel
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-! # Stalkwise Tor bounds for a perfect closed immersion

## References

* Stacks Project, Duality for Schemes, Tag 0A9U.
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory

private theorem tor'_isZero_of_bounded_resolution
    {R : Type u} [CommRing R] (A M : ModuleCat.{u} R)
    (P : ProjectiveResolution A) (j : ℕ) (hj : IsZero (P.complex.X j)) :
    IsZero (((Tor' (ModuleCat.{u} R) j).obj A).obj M) := by
  refine IsZero.of_iso ?_ (P.isoLeftDerivedObj (tensorRight M) j)
  erw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact ShortComplex.exact_of_isZero_X₂ _ ((tensorRight M).map_isZero hj)

private theorem tor_isZero_of_tor'_isZero
    {R : Type u} [CommRing R] (A M : ModuleCat.{u} R) (j : ℕ)
    (h : IsZero (((Tor' (ModuleCat.{u} R) j).obj A).obj M)) :
    IsZero (((Tor (ModuleCat.{u} R) j).obj A).obj M) := by
  obtain ⟨σ⟩ := nonempty_tor'_flip_iso R j
  have h' : IsZero (((Tor' (ModuleCat.{u} R) j).obj M).obj A) :=
    h.of_iso ((σ.app A).app M).symm
  let β := BraidedCategory.tensorLeftIsoTensorRight A
  let e : (tensorLeft A).leftDerived j ≅ (tensorRight A).leftDerived j :=
    { hom := NatTrans.leftDerived β.hom j
      inv := NatTrans.leftDerived β.inv j
      hom_inv_id := by rw [← NatTrans.leftDerived_comp, β.hom_inv_id,
        NatTrans.leftDerived_id]
      inv_hom_id := by rw [← NatTrans.leftDerived_comp, β.inv_hom_id,
        NatTrans.leftDerived_id] }
  exact h'.of_iso (e.app M)

namespace AlgebraicGeometry

/-- Perfection of the pushforward of the unit along a closed immersion gives finite
Tor bounds in both tensor variables on the actual stalk restriction of scalars
(Stacks, Tag 0A9U). -/
theorem perfectImmersion_stalkwiseTorBounds
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (hperfect : Y.IsPerfect ((schemeDerivedDirectImage i).obj
      (𝟙_ (schemeDerivedCategory Z)))) :
    (∀ x : Z, ∃ n : ℕ,
      ∀ (M : ModuleCat.{u} (Y.presheaf.stalk (i x))) (j : ℕ), n < j →
        IsZero (((Tor' (ModuleCat.{u} (Y.presheaf.stalk (i x))) j).obj
          ((ModuleCat.restrictScalars (i.stalkMap x).hom).obj
            (ModuleCat.of (Z.presheaf.stalk x) (Z.presheaf.stalk x)))).obj M)) ∧
    (∀ x : Z, ∃ n : ℕ,
      ∀ (M : ModuleCat.{u} (Y.presheaf.stalk (i x))) (j : ℕ), n < j →
        IsZero (((Tor (ModuleCat.{u} (Y.presheaf.stalk (i x))) j).obj
          ((ModuleCat.restrictScalars (i.stalkMap x).hom).obj
            (ModuleCat.of (Z.presheaf.stalk x) (Z.presheaf.stalk x)))).obj M)) := by
  let F := RingedSpace.moduleDirectImage i.toLRSHom.toShHom
  have {A B : SheafOfModules.{u} (moduleRings Z.toRingedSpace)} (f : A ⟶ B) :
      PreservesColimit (parallelPair f 0) F :=
    Scheme.Modules.closedImmersion_pushforward_preservesCokernel i f
  let : PreservesFiniteColimits F := Functor.preservesFiniteColimits_of_preservesCokernels F
  let : PreservesFiniteLimits F := by
    dsimp [F, RingedSpace.moduleDirectImage]
    infer_instance
  let eunit : 𝟙_ (schemeDerivedCategory Z) ≅
      (DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit Z.ringCatSheaf) :=
    (DerivedCategory.quotientCompQhIso _).app _
  let epush := (schemeDerivedDirectImage i).mapIso eunit ≪≫
    F.singleFunctorCompRightDerivedFunctorIso.app (SheafOfModules.unit Z.ringCatSheaf)
  have hres (x : Z) : ∃ (P : ProjectiveResolution
      ((ModuleCat.restrictScalars (i.stalkMap x).hom).obj
        (ModuleCat.of (Z.presheaf.stalk x) (Z.presheaf.stalk x)))) (n : ℕ),
      ∀ j : ℕ, n < j → IsZero (P.complex.X j) := by
    obtain ⟨U, hx, K, hK, ⟨e⟩⟩ := hperfect (i x)
    let eordinary := (SheafOfModules.overFunctor.{u}
      (moduleRings Y.toRingedSpace) U).mapDerivedCategory.mapIso epush.symm ≪≫ e
    exact strictPerfectClosedPushforward_stalkResolution i x U hx K hK eordinary
  have hTor' : ∀ x : Z, ∃ n : ℕ,
      ∀ (M : ModuleCat.{u} (Y.presheaf.stalk (i x))) (j : ℕ), n < j →
        IsZero (((Tor' (ModuleCat.{u} (Y.presheaf.stalk (i x))) j).obj
          ((ModuleCat.restrictScalars (i.stalkMap x).hom).obj
            (ModuleCat.of (Z.presheaf.stalk x) (Z.presheaf.stalk x)))).obj M) := by
    intro x
    obtain ⟨P, n, hn⟩ := hres x
    refine ⟨n, ?_⟩
    intro M j hj
    exact tor'_isZero_of_bounded_resolution _ M P j (hn j hj)
  refine ⟨hTor', ?_⟩
  intro x
  obtain ⟨n, hn⟩ := hTor' x
  exact ⟨n, fun M j hj ↦ tor_isZero_of_tor'_isZero _ M j (hn M j hj)⟩

end AlgebraicGeometry
