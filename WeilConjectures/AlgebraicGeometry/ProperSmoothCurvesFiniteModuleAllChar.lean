/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.AlgebraicGeometry.ProperSmoothCurvesPrimeHomologyAllChar
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Proper
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CoefficientDevissage
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-!
# Finite constant coefficients in proper smooth curve families in every characteristic

## References

* [Stacks, Tag 0GKW], [Stacks, Tag 0GKV], [Stacks, Tag 02G1]
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- For a proper smooth morphism over a Noetherian base, with nonempty geometrically
connected fibres of dimension at most one, every integer-degree higher direct image of a
finite constant module over a finite commutative ring is constructible, in every
characteristic. `GeometricallyConnected f` is equivalent to geometric connectedness of
each residue-field fibre and includes nonemptiness of those fibres. (Stacks, Tag 0GKW) -/
theorem properSmoothCurves_finiteModule_higherDirectImage_constructible_all_char
    {C S : Scheme.{u}} [IsLocallyNoetherian S] [CompactSpace S]
    (f : C ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (h_dim : ∀ s : S, topologicalKrullDim (f.fiber s) ≤ 1)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (M : ModuleCat.{u + 1} Λ) [Finite M] (q : ℤ) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
        ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj
            ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))) := by
  classical
  let A := ULift.{u + 1} (ZMod (ringChar Λ))
  have hne : NeZero (ringChar Λ) :=
    ⟨CharP.char_ne_zero_of_finite Λ (ringChar Λ)⟩
  let φ : A →+* Λ :=
    (ZMod.castHom dvd_rfl Λ).comp ULift.ringEquiv.toRingHom
  let MR := (ModuleCat.restrictScalars.{u + 1} φ).obj M
  have : Finite MR := inferInstanceAs (Finite M)
  let FR := (constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} A)).obj MR
  let FΛ := (constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M
  have hprime :
      ∀ (ell : ℕ) [Fact ell.Prime], ell ∣ ringChar Λ →
      Etale.DerivedCategory.constructibleHomology
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) S
        ((R((f)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))])).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((constantSheaf C.smallEtaleTopology
              (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))).obj
              (ModuleCat.of _ (ULift.{u + 1} (ZMod ell)))))) := by
    intro ell _ hell
    exact properSmoothCurves_prime_higherDirectImage_constructible_homology_all_char
      f h_dim ell
  have hR :
      Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} A) S
        ((R((f)_*[ModuleCat.{u + 1} A])).obj
          ((DerivedCategory.singleFunctor _ 0).obj FR)) := by
    exact constructibleHomology_rightDerivedLowerStar_constantSheaf_zmod
      f (ringChar Λ) hprime MR
  have hqR : Scheme.IsConstructibleSheaf
      ((DerivedCategory.homologyFunctor
        (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) q).obj
        ((R((f)_*[ModuleCat.{u + 1} A])).obj
          ((DerivedCategory.singleFunctor _ 0).obj FR))) := by
    rw [Etale.DerivedCategory.constructibleHomology_eq] at hR
    exact hR q
  have hqΛ : Scheme.IsConstructibleSheaf
      ((DerivedCategory.homologyFunctor
        (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
        ((R((f)_*[ModuleCat.{u + 1} Λ])).obj
          ((DerivedCategory.singleFunctor _ 0).obj FΛ))) := by
    apply (isConstructibleSheaf_homology_constantSheaf_restrictScalars_iff
      φ f M q).mp
    exact hqR
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
  have : Scheme.IsConstructibleSheaf
      ((DerivedCategory.homologyFunctor
        (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
        ((R((f)_*[ModuleCat.{u + 1} Λ])).obj
          ((DerivedCategory.singleFunctor _ 0).obj FΛ))) := hqΛ
  exact Scheme.IsConstructibleSheaf.of_iso
    (homologyRightDerivedLowerStarSingleIsoPlus f FΛ q)

end AlgebraicGeometry.Etale
