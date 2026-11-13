/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.OrdinarySupportedKummerScalar
public import WeilConjectures.SixFunctors.BaseChange.RestrictScalars
import WeilConjectures.AlgebraicGeometry.SupportedKummerScalarDerived
import WeilConjectures.AlgebraicGeometry.SupportedKummerScalarMaps

/-!
# Derived scalar extension of a closed supported constant sheaf

The theorem records the canonical scalar-extension comparison by the universal property
of `SupportedDerivedScalarUnit`.  The displayed composite is the coefficient unit on the
closed support transported through the canonical restriction-of-scalars/pushforward
comparison.  No flatness assumption on the new coefficient ring occurs.

## References

* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The canonical coefficient map from the lifted residue ring `ULift (ZMod N)` to `A`: the
finite étale Tate-twist scalar map composed with the canonical `ULift` ring equivalence. -/
def supportedScalarMap (N : ℕ) (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0) :
    ULift.{u + 1} (ZMod N) →+* A :=
  (Scheme.finiteEtaleTwistScalar N A hA).comp ULift.ringEquiv.toRingHom

/--
For a finite coefficient ring killed by `N`, the supported constant scalar extension is
characterized simultaneously on the closed support and on the ambient scheme.  The
maps `ηD` and `ηT` are the coefficient units, fixed on constant-presheaf generators; their
derived universal properties state that the displayed objects are the derived scalar
extensions, and the final equality is naturality of the unit under the closed pushforward.
This is the canonical comparison of `Ri_* Λ_D ⊗ᴸ_{Λ_T} A_T` with `Ri_* A_D`, and does not
assume that `A` is flat over `Λ`.
-/
theorem supported_kummer_scalar_source
    (T : Scheme.{u}) (N : ℕ) (hN : 1 ≤ N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    {D : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i] :
    ∃ (ηD : ordinaryFiniteConstant (ULift.{u + 1} (ZMod N)) D ⟶
        (Sheaf.restrictScalars D.smallEtaleTopology
          (supportedScalarMap N A hA)).obj
          (ordinaryFiniteConstant A D))
      (ηT : ordinaryFiniteConstant (ULift.{u + 1} (ZMod N)) T ⟶
        (Sheaf.restrictScalars T.smallEtaleTopology
          (supportedScalarMap N A hA)).obj
          (ordinaryFiniteConstant A T)),
      (∀ (U : D.Etaleᵒᵖ) (r : ULift.{u + 1} (ZMod N)),
        ηD.hom.app U
          ((toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
            (ModuleCat.of (ULift.{u + 1} (ZMod N)) (ULift.{u + 1} (ZMod N))))).app U r) =
        (toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
          (ModuleCat.of A A))).app U (supportedScalarMap N A hA r)) ∧
      (∀ (U : T.Etaleᵒᵖ) (r : ULift.{u + 1} (ZMod N)),
        ηT.hom.app U
          ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
            (ModuleCat.of (ULift.{u + 1} (ZMod N)) (ULift.{u + 1} (ZMod N))))).app U r) =
        (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
          (ModuleCat.of A A))).app U (supportedScalarMap N A hA r)) ∧
      SupportedDerivedScalarUnit
          (supportedScalarMap N A hA) D
          (ordinaryFiniteConstant (ULift.{u + 1} (ZMod N)) D)
          (ordinaryFiniteConstant A D) ηD ∧
      SupportedDerivedScalarUnit
          (supportedScalarMap N A hA) T
          ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N))) i).obj
            (ordinaryFiniteConstant (ULift.{u + 1} (ZMod N)) D))
          ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
          ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N))) i).map ηD ≫
            (lowerStarCompRestrictScalarsIso
              (supportedScalarMap N A hA) i).inv.app
              (ordinaryFiniteConstant A D)) ∧
      SupportedDerivedScalarUnit
          (supportedScalarMap N A hA) T
          (ordinaryFiniteConstant (ULift.{u + 1} (ZMod N)) T)
          (ordinaryFiniteConstant A T) ηT ∧
      ηT ≫
          (Sheaf.restrictScalars T.smallEtaleTopology
            (supportedScalarMap N A hA)).map
            (supportedConstantUnit A i) =
        supportedConstantUnit (ULift.{u + 1} (ZMod N)) i ≫
          (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N))) i).map ηD ≫
          (lowerStarCompRestrictScalarsIso
            (supportedScalarMap N A hA) i).inv.app
            (ordinaryFiniteConstant A D) := by
  have _ := hN
  let φ := supportedScalarMap N A hA
  obtain ⟨ηD, ηT, hD, hT⟩ := exists_supported_kummer_scalar_maps T N A φ i
  obtain ⟨huD, huI, huT⟩ :=
    supported_kummer_scalar_derived_units T (ULift.{u + 1} (ZMod N)) A φ i ηD ηT hD hT
  exact ⟨ηD, ηT, hD, hT, huD, huI, huT,
    supported_kummer_scalar_units_commute φ i ηD ηT hD hT⟩

end AlgebraicGeometry.Etale
