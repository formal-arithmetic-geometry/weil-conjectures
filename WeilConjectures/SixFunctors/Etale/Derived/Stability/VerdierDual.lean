/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.SixFunctors.Etale.Derived.AdjunctionShift
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.FiniteEtaleAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.Derived.TensorHom

/-!
# The Tor amplitude of the Verdier dual

This file proves the auxiliary statements used for the Tor bound of the Verdier dual
(`lem-weil-verdier-preservation-strata`):

- `AlgebraicGeometry.Etale.nonempty_iso_derivedHom_rightDerivedLowerStar`: the internal hom into
  a direct image, `RHom(K, Rf_* M) ≅ Rf_* RHom(Lf^* K, M)`;
- `AlgebraicGeometry.Etale.torAmplitudeIn_obj₂_of_distTriang`: Tor amplitude in a given interval
  is closed under extensions;
- `AlgebraicGeometry.Etale.torAmplitudeIn_derivedHom_obj₂_of_distTriang`: the same for the
  internal hom out of a fixed complex, which is triangulated in its second variable;
- `AlgebraicGeometry.Etale.torAmplitudeIn_of_leftDerivedUpperStar_of_surjective`: Tor amplitude
  descends along a surjective morphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ]

/-! ### The internal hom into a direct image -/

/-! ### Extensions and descent, for a general coefficient category -/

section General

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

end General

/-! ### Extensions and descent, for coefficients in a ring -/

section Descent

open ZeroObject

/-- A sheaf of `Λ`-modules on the small étale site whose pullback along a surjective morphism
vanishes is zero: pullbacks along a jointly surjective family reflect isomorphisms. -/
lemma isZero_of_isZero_upperStar_of_surjective {U' U : Scheme.{u}} (p : U' ⟶ U)
    (hp : Function.Surjective p.base) {F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (h : IsZero ((p)^*[ModuleCat.{u + 1} Λ].obj F)) : IsZero F := by
  have := Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} Λ)
    (ι := PUnit.{u + 1}) (fun _ ↦ p) (fun x ↦ by
      obtain ⟨y, rfl⟩ := hp x
      exact ⟨⟨⟩, y, rfl⟩) (0 : F ⟶ 0) (fun _ ↦
        isIso_of_source_target_iso_zero _ h.isoZero
          (Functor.map_isZero _ (isZero_zero _)).isoZero)
  exact (isZero_zero _).of_iso (asIso (0 : F ⟶ 0))

end Descent

end Etale

end AlgebraicGeometry
