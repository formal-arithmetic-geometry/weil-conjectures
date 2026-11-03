/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundleIntegration
public import WeilConjectures.AlgebraicGeometry.VectorTraceGeometry.VectorTraceGeometry
public import WeilConjectures.AlgebraicGeometry.Vector.VectorTraceGeometricDescent
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportFiniteTorsion
public import WeilConjectures.AlgebraicGeometry.ConstantTraceLineAutomorphismUnit

/-!
# Translation family on the vector-bundle trace line

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-orientation-from-the-diagonal/sk-prop-sp-orientation/
sk-prop-sp-orientation-vector-bundle.proof.md`, Step 1 (blueprint:
lem-pur-vector-translation-trace-unit-family).

The module constructs the canonical self-product translation from the direct-sum
symmetric-algebra map `(v,w) ↦ (v,w-v)`.  Its compact-support action is the
published Cartesian exchange followed by the canonical Tate/shift comparison.
The theorem then records the degree-zero multiplication equation and its
zero-section normalization.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The linear map on `M ⊞ M` sending `(v,w)` to `(v,w-v)`.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-orientation-from-the-diagonal/sk-prop-sp-orientation/
sk-prop-sp-orientation-vector-bundle.proof.md`, Step 1, the translation
automorphism `τ(v,w)=(v,w-v)` (blueprint: lem-pur-vector-translation-trace-unit-family). -/
def vectorTranslationLinearMap (S : Scheme.{u}) (M : S.Modules) :
    VectorTraceGeometry.sum S M M ⟶ VectorTraceGeometry.sum S M M :=
  biprod.lift (biprod.fst : VectorTraceGeometry.sum S M M ⟶ M)
    (-(biprod.fst : VectorTraceGeometry.sum S M M ⟶ M) + biprod.snd)

/-- The inverse linear map on `M ⊞ M`, sending `(v,w)` to `(v,w+v)`.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-orientation-from-the-diagonal/sk-prop-sp-orientation/
sk-prop-sp-orientation-vector-bundle.proof.md`, Step 1, the inverse of the
translation automorphism (blueprint: lem-pur-vector-translation-trace-unit-family). -/
def vectorTranslationLinearMapInv (S : Scheme.{u}) (M : S.Modules) :
    VectorTraceGeometry.sum S M M ⟶ VectorTraceGeometry.sum S M M :=
  biprod.lift (biprod.fst : VectorTraceGeometry.sum S M M ⟶ M)
    ((biprod.fst : VectorTraceGeometry.sum S M M ⟶ M) + biprod.snd)

/-- The canonical translation map on the pulled-back vector bundle.

It is conjugated from the displayed direct-sum linear map by the canonical
`VectorTraceGeometry.sumIso`; therefore its coordinates are exactly
`(v,w) ↦ (v,w-v)`: the bundle map is contravariant in the generators, and on points
`(w,v)` (fibre `w` from the first summand, base `v` from the second) it sends
`(w,v)` to `(w-v,v)`.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-orientation-from-the-diagonal/sk-prop-sp-orientation/
sk-prop-sp-orientation-vector-bundle.proof.md`, Step 1, the translation automorphism
(blueprint: lem-pur-vector-translation-trace-unit-family). -/
def vectorTranslationHom (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    VectorBundleZeroSection.scheme
        (VectorBundleZeroSection.scheme S d M) d
        ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S d M)).obj M) ⟶
      VectorBundleZeroSection.scheme
        (VectorBundleZeroSection.scheme S d M) d
        ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S d M)).obj M) :=
  let e := VectorTraceGeometry.sumIso S d d M M
  e.hom ≫
    WeilConjectures.PurityFiniteSetting.purityBundleMap S (d + d) (d + d)
      (VectorTraceGeometry.sum S M M) (VectorTraceGeometry.sum S M M)
      (vectorTranslationLinearMap S M) ≫ e.inv

/-- The inverse of `vectorTranslationHom` is obtained from the plus map.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-orientation-from-the-diagonal/sk-prop-sp-orientation/
sk-prop-sp-orientation-vector-bundle.proof.md`, Step 1, the translation
automorphism (blueprint: lem-pur-vector-translation-trace-unit-family). -/
def vectorTranslationHomInv (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    VectorBundleZeroSection.scheme
        (VectorBundleZeroSection.scheme S d M) d
        ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S d M)).obj M) ⟶
      VectorBundleZeroSection.scheme
        (VectorBundleZeroSection.scheme S d M) d
        ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S d M)).obj M) :=
  let e := VectorTraceGeometry.sumIso S d d M M
  e.hom ≫
    WeilConjectures.PurityFiniteSetting.purityBundleMap S (d + d) (d + d)
      (VectorTraceGeometry.sum S M M) (VectorTraceGeometry.sum S M M)
      (vectorTranslationLinearMapInv S M) ≫ e.inv

/-- The translation is invertible.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-orientation-from-the-diagonal/sk-prop-sp-orientation/
sk-prop-sp-orientation-vector-bundle.proof.md`, Step 1, "the automorphism τ"
(blueprint: lem-pur-vector-translation-trace-unit-family).
Proof: `vectorTranslationHomInv` is a two-sided inverse, because the plus and minus
linear maps compose to the identity of `M ⊞ M` and `purityBundleMap` is functorial. -/
theorem vectorTranslationHom_isIso (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    IsIso (vectorTranslationHom S d M) := by
  sorry

/-- The canonical automorphism `τ(v,w)=(v,w-v)` of the self-product bundle.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-orientation-from-the-diagonal/sk-prop-sp-orientation/
sk-prop-sp-orientation-vector-bundle.proof.md`, Step 1
(blueprint: lem-pur-vector-translation-trace-unit-family). -/
def vectorTranslation (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    VectorBundleZeroSection.scheme
        (VectorBundleZeroSection.scheme S d M) d
        ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S d M)).obj M) ≅
      VectorBundleZeroSection.scheme
        (VectorBundleZeroSection.scheme S d M) d
        ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S d M)).obj M) := by
  letI := vectorTranslationHom_isIso S d M
  exact asIso (vectorTranslationHom S d M)

/-- The translation is over the first projection.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-orientation-from-the-diagonal/sk-prop-sp-orientation/
sk-prop-sp-orientation-vector-bundle.proof.md`, Step 1, "τ of V×_S V over the first
factor" (blueprint: lem-pur-vector-translation-trace-unit-family).
Proof: the minus map is the identity on the second (base) summand, so composing with
`sumIso` and the base projection of `existsUnique_sumIso` gives the base projection. -/
theorem vectorTranslation_over (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    (vectorTranslation S d M).hom ≫ VectorBundleZeroSection.π
        (VectorBundleZeroSection.scheme S d M) d
        ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S d M)).obj M) =
      VectorBundleZeroSection.π (VectorBundleZeroSection.scheme S d M) d
        ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S d M)).obj M) := by
  sorry

/-- The Cartesian square `(τ,p₁,p₁,1_V)` used for compact-support finite-torsion exchange.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-orientation-from-the-diagonal/sk-prop-sp-orientation/
sk-prop-sp-orientation-vector-bundle.proof.md`, Step 1
(blueprint: lem-pur-vector-translation-trace-unit-family).
Proof: `τ` is an isomorphism over `V` (`vectorTranslation_over`), and a square with two
parallel isomorphisms is Cartesian (`IsPullback.of_horiz_isIso`). -/
theorem vectorTranslationSquare (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    IsPullback (vectorTranslation S d M).hom
      (VectorBundleZeroSection.π (VectorBundleZeroSection.scheme S d M) d
        ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S d M)).obj M))
      (VectorBundleZeroSection.π (VectorBundleZeroSection.scheme S d M) d
        ((Scheme.Modules.tensorPullback
          (VectorBundleZeroSection.π S d M)).obj M)) (𝟙 _) := by
  sorry

/-- The canonical Tate/shift identification `τ^*A_W(d)[2d] ≅ A_W(d)[2d]`: the coefficient
is the pullback of the base line along `p₁`, and `τ ≫ p₁ = p₁` gives the composition
isomorphism of derived inverse images.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-orientation-from-the-diagonal/sk-prop-sp-orientation/
sk-prop-sp-orientation-vector-bundle.proof.md`, Step 1
(blueprint: lem-pur-vector-translation-trace-unit-family). -/
def vectorTranslationCoefficientIso (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S]
    (d : ℕ) (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    (ordinaryFinitePullback A (vectorTranslation S d M).hom).obj
        (vectorIntegrationCoefficient A N hA
          (VectorBundleZeroSection.scheme S d M) d
          ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S d M)).obj M)) ≅
      vectorIntegrationCoefficient A N hA
        (VectorBundleZeroSection.scheme S d M) d
        ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S d M)).obj M) := by
  let V := VectorBundleZeroSection.scheme S d M
  let p := VectorBundleZeroSection.π S d M
  let G := (Scheme.Modules.tensorPullback p).obj M
  simpa only [vectorIntegrationCoefficient, ordinaryFinitePullback, Functor.comp_obj] using
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
      (vectorTranslation S d M).hom (VectorBundleZeroSection.π V d G)
      (VectorBundleZeroSection.π V d G) (vectorTranslation_over S d M).symm).symm.app
      (affineLinearBaseCoefficient A N hA V d))


/-- The compact-support exchange for the canonical translation square.

The first comparison is the identity-base pullback comparison, the middle map is the
finite-torsion Cartesian exchange for `(τ,p₁,p₁,1_V)`, and the final map is the
canonical coefficient Tate/shift identification.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-orientation-from-the-diagonal/sk-prop-sp-orientation/
sk-prop-sp-orientation-vector-bundle.proof.md`, Step 1, "its effect on the top compactly supported
direct image" (blueprint: lem-pur-vector-translation-trace-unit-family). -/
def vectorTranslationTraceExchange (N : ℕ) (_hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (_hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    vectorIntegrationSource A N hA (VectorBundleZeroSection.scheme S d M) d
      ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S d M)).obj M) ⟶
    vectorIntegrationSource A N hA (VectorBundleZeroSection.scheme S d M) d
      ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S d M)).obj M) := by
  let V := VectorBundleZeroSection.scheme S d M
  let p := VectorBundleZeroSection.π S d M
  let G := (Scheme.Modules.tensorPullback p).obj M
  let K := vectorIntegrationCoefficient A N hA V d G
  letI : IsNoetherian V := (vectorIntegration_geometry S d M).2.2
  letI := isIso_rightDerivedLowerShriekBaseChangeMap A (vectorTranslationSquare S d M)
  exact (affineLinearPullbackId A V).inv.app
      (vectorIntegrationSource A N hA V d G) ≫
    (rightDerivedLowerShriekBaseChangeMap A (vectorTranslationSquare S d M)).app K ≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (VectorBundleZeroSection.π V d G)).map
      (vectorTranslationCoefficientIso A N hA S d M).hom


/-- The degree-zero action obtained by the canonical integration transport:
`H^0(t)⁻¹ ≫ H^0(ρ_τ) ≫ H^0(t)`, with `ρ_τ = vectorTranslationTraceExchange` and the
canonical identification of `H^0` of a single complex, as an automorphism of the
constant trace line `A_V`.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-orientation-from-the-diagonal/sk-prop-sp-orientation/
sk-prop-sp-orientation-vector-bundle.proof.md`, Step 1, "identified with the constant sheaf
by integration"
(blueprint: lem-pur-vector-translation-trace-unit-family). -/
def vectorTranslationDegreeZeroAutomorphism (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    constantTraceLine (VectorBundleZeroSection.scheme S d M) A ≅
      constantTraceLine (VectorBundleZeroSection.scheme S d M) A := by
  let V := VectorBundleZeroSection.scheme S d M
  let p := VectorBundleZeroSection.π S d M
  let G := (Scheme.Modules.tensorPullback p).obj M
  letI : IsNoetherian V := (vectorIntegration_geometry S d M).2.2
  letI : G.IsFiniteLocallyFreeOfRank d :=
    AlgebraicGeometry.VectorTraceGeometry.tensorPullbackRank p d M
  let t := vectorBundleIntegration N hN A hA V
    (by simpa only [map_natCast] using hS.map p.appTop.hom) d G
  letI : IsIso t := (vectorBundleIntegration_concentration_and_isIso N hN A hA V
    (by simpa only [map_natCast] using hS.map p.appTop.hom) d G).2
  let e := asIso ((_root_.DerivedCategory.homologyFunctor _ 0).map t) ≪≫
    (_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app
      (ordinaryFiniteConstant A V)
  let K := vectorIntegrationCoefficient A N hA V d G
  letI : IsIso ((affineLinearPullbackId A V).inv.app
      (vectorIntegrationSource A N hA V d G)) := by infer_instance
  letI := isIso_rightDerivedLowerShriekBaseChangeMap A (vectorTranslationSquare S d M)
  letI : IsIso ((rightDerivedLowerShriekBaseChangeMap A
      (vectorTranslationSquare S d M)).app K) := by infer_instance
  letI : IsIso ((rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (VectorBundleZeroSection.π V d G)).map
      (vectorTranslationCoefficientIso A N hA S d M).hom) := by infer_instance
  letI : IsIso (vectorTranslationTraceExchange N hN A hA S hS d M) := by
    dsimp [vectorTranslationTraceExchange]
    infer_instance
  letI : IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      (vectorTranslationTraceExchange N hN A hA S hS d M)) := by infer_instance
  exact e.symm ≪≫
    asIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      (vectorTranslationTraceExchange N hN A hA S hS d M)) ≪≫ e


end AlgebraicGeometry.Etale
