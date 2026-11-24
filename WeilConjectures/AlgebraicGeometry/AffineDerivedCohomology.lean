/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineVanishing


public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.QCohAcyclicDerivedPushforwardCohomology
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-!
# Cohomology of affine derived direct image

## References

* Stacks Project, Tag 0AVW
-/

@[expose] public section

universe u wX wY

open CategoryTheory

namespace AlgebraicGeometry

/-- For an affine morphism, the cohomology sheaves of the unbounded derived direct image
of an object with quasi-coherent cohomology are the ordinary direct images of its
cohomology sheaves, and these direct images are quasi-coherent (Stacks, Tag 0AVW). -/
theorem schemeHigherDirectImage_of_affine
    {X Y : Scheme.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (f : X ⟶ Y) [IsAffineHom f]
    (E : schemeDerivedCategory X) (hE : schemeDerivedQCohProperty X E) (i : ℤ) :
    Nonempty ((schemeHigherDirectImage f i).obj E ≅
      (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E)) ∧
    ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).obj
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E)).IsQuasicoherent := by
  have : IsGrothendieckAbelian.{u} X.Modules :=
    Scheme.Modules.isGrothendieckAbelian X
  have hacyc : ∀ (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)),
      F.IsQuasicoherent → ∀ (p : ℤ), 0 < p →
        Limits.IsZero ((schemeModuleHigherDirectImage f p).obj F) := by
    intro F hF p hp
    have := hF
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = (n : ℤ) := ⟨p.toNat, by omega⟩
    have hn : 0 < n := by omega
    have hz := Scheme.Modules.isZero_higherDirectImage_of_isAffineHom f F hn
    exact hz.of_iso
      (Functor.homologyRightDerivedFunctorObjSingleFunctorIso
        (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) F n)
  obtain ⟨comparison⟩ := qcoh_acyclic_derived_pushforward_cohomology f hacyc i
  refine ⟨⟨comparison.app ⟨E, hE⟩⟩, ?_⟩
  have := hE i
  exact Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom f
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E)

end AlgebraicGeometry
