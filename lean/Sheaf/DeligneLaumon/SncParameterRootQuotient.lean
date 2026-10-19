/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import WeilConjectures.AlgebraicGeometry.NormalScheme
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Basic

import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.RingTheory.Noetherian.Basic
import Sheaf.AlgebraicGeometry.EtaleNormalComponents
import Sheaf.AlgebraicGeometry.RegularBoundaryDivisorialChart
import WeilConjectures.AlgebraicGeometry.Morphisms.AffineFpIsoIndEtaleDescent
import WeilConjectures.AlgebraicGeometry.Morphisms.StrictLocalRootsOfUnity
import WeilConjectures.RingTheory.StrictHenselizationCotangentDimension
import WeilConjectures.RingTheory.StrictHenselizationRegular
import Sheaf.RingTheory.ColimitCategoryFpAlgebras
import Sheaf.RingTheory.EtaleColimitNormalLocalDomain
import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres
import WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct
import WeilConjectures.RingTheory.RegularRingSmoothAscent
import WeilConjectures.RingTheory.StrictHenselizationTriples
import Sheaf.AlgebraicGeometry.FinitePresentationOfFiniteLocallyNoetherian
import Sheaf.AlgebraicGeometry.SncRootPuncturedTorsorSplitting

/-!
# Etale-local parameter-root quotients of invertible-order torsors

Source: ILO, Travaux de Gabber, Exposé IX, Proposition 2.1, printed pp. 133--134,
with the exponent specialized as in IX 2.2 (blueprint: lem-per-snc-parameter-root-quotient).

The auxiliary definitions spell out the parameter equations, the displayed quotient algebra,
and the clauses of the pointed normal form. Invariants use Mathlib's algebra equalizers.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The displayed simultaneous-root algebra, with its quotient algebra structure.
Source: ILO IX 2.1, p. 133 (blueprint: lem-per-snc-parameter-root-quotient). -/
abbrev sncParameterRootRing (A : Type u) [CommRing A] (n r : ℕ) (t : Fin r → A) :=
  MvPolynomial (Fin r) A ⧸
    Ideal.span (Set.range (fun i ↦ MvPolynomial.X i ^ n - MvPolynomial.C (t i)))

/-- Parameter equations for exactly the boundary components through a selected point.
The zero schemes are integral and distinct; their union is the entire boundary on this
neighbourhood. Their germs extend to a full regular system of parameters.
Source: ILO IX 2.1, p. 133 (blueprint: lem-per-snc-parameter-root-quotient). -/
def IsSncParameterEquations (X : Scheme.{u}) [IsLocallyNoetherian X]
    (S : Set X) (x : X) (r : ℕ) (t : Fin r → Γ(X, ⊤)) : Prop :=
  (∀ i, IsIntegral (Scheme.IdealSheafData.ofIdealTop (Ideal.span {t i})).subscheme) ∧
  Function.Injective (fun i ↦
    (Scheme.IdealSheafData.ofIdealTop (Ideal.span {t i})).support) ∧
  S = ⋃ i, ((Scheme.IdealSheafData.ofIdealTop (Ideal.span {t i})).support : Set X) ∧
  (∀ i, X.presheaf.germ ⊤ x trivial (t i) ∈
    IsLocalRing.maximalIdeal (X.presheaf.stalk x)) ∧
  ∃ s : List (X.presheaf.stalk x),
    IsLocalRing.IsRegularSystemOfParameters
      (List.ofFn (fun i ↦ X.presheaf.germ ⊤ x trivial (t i)) ++ s)

/-- Equations for the boundary near a point, before removing components away from it.
The equality is required on some open neighbourhood; thus a prescribed neighbourhood need
not have removed the other components yet. The germs extend to a regular parameter system.
Source: ILO IX 2.1, p. 133 (blueprint: lem-per-snc-parameter-root-quotient). -/
def IsSncParameterGerms (X : Scheme.{u}) [IsLocallyNoetherian X]
    (S : Set X) (x : X) (r : ℕ) (t : Fin r → Γ(X, ⊤)) : Prop :=
  (∃ U : X.Opens, x ∈ U ∧ S ∩ U =
    (⋃ i, X.zeroLocus {t i}) ∩ U) ∧
  (∀ i, X.presheaf.germ ⊤ x trivial (t i) ∈
    IsLocalRing.maximalIdeal (X.presheaf.stalk x)) ∧
  ∃ s : List (X.presheaf.stalk x),
    IsLocalRing.IsRegularSystemOfParameters
      (List.ofFn (fun i ↦ X.presheaf.germ ⊤ x trivial (t i)) ++ s)

/-- All clauses of the pointed parameter-root quotient over the given affine neighbourhood.
The intersection of equalizers is precisely the fixed subalgebra: an element belongs to it
if and only if every `σ h` fixes it. The action is by algebra automorphisms, so fixes `A`.
Source: ILO IX 2.1, pp. 133--134 (blueprint: lem-per-snc-parameter-root-quotient). -/
def IsSncParameterRootQuotientAt
    {Y Z : Scheme.{u}} (T : Y.IdealSheafData) (b : Z ⟶ Y)
    {Ω : Type u} [Field Ω] (ybar : Spec (.of Ω) ⟶ Y) (zbar : Spec (.of Ω) ⟶ Z)
    (n r : ℕ) (A : CommRingCat.{u}) [IsNoetherianRing A]
    (uA : Spec A ⟶ Y) (uΩ : Spec (.of Ω) ⟶ Spec A) (t : Fin r → A) : Prop :=
  IsRegularRing A ∧ Etale uA ∧ uΩ ≫ uA = ybar ∧
  IsSncParameterEquations (Spec A) (uA ⁻¹' (T.support : Set Y))
    (Scheme.SpecToEquivOfField Ω (Spec A) uΩ).1 r
    (fun i ↦ (Scheme.ΓSpecIso A).inv (t i)) ∧
  uA ⁻¹ᵁ T.support.compl = PrimeSpectrum.basicOpen (∏ i, t i) ∧
  ∃ ζ : Aˣ, (ζ : A) ^ n = 1 ∧
    (∀ a : ℕ, 1 ≤ a → a < n → IsUnit (1 - (ζ : A) ^ a)) ∧
    ∃ (H : AddSubgroup (Fin r → ZMod n))
      (σ : H → sncParameterRootRing A n r t ≃ₐ[A] sncParameterRootRing A n r t),
      σ 0 = AlgEquiv.refl ∧
      (∀ h₁ h₂, σ (h₁ + h₂) = (σ h₂).trans (σ h₁)) ∧
      (∀ (h : H) (i : Fin r),
        σ h (Ideal.Quotient.mk _ (MvPolynomial.X i)) =
          algebraMap A (sncParameterRootRing A n r t) ((ζ : A) ^ (h.1 i).val) *
            Ideal.Quotient.mk _ (MvPolynomial.X i)) ∧
      ∃ (W : Scheme.{u}) (w : W ⟶ Z) (wU : W ⟶ Spec A)
        (wΩ : Spec (.of Ω) ⟶ W),
        Etale w ∧ IsNoetherian W ∧ wΩ ≫ w = zbar ∧ wΩ ≫ wU = uΩ ∧
        w ≫ b = wU ≫ uA ∧
        ∃ eW : W ≅ Spec (.of
          ((⨅ h, AlgHom.equalizer (σ h).toAlgHom
            (AlgHom.id A (sncParameterRootRing A n r t))) :
              Subalgebra A (sncParameterRootRing A n r t))),
          eW.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A
            ((⨅ h, AlgHom.equalizer (σ h).toAlgHom
              (AlgHom.id A (sncParameterRootRing A n r t))) :
                Subalgebra A (sncParameterRootRing A n r t)))) = wU

/-- The normalization of the torsor in its function-field extension, constructed using
relative normalization. The finite projection supplies quasi-compactness and separation.
Source: ILO IX 2.1, pp. 133--134 (blueprint: lem-per-snc-parameter-root-quotient). -/
abbrev sncTorsorNormalization {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (T : Y.IdealSheafData) {G : Type v} [Group G]
    (cover : Scheme.GaloisCoverAction G (Scheme.Opens.toScheme T.support.compl)) :=
  letI : IsFinite cover.π := cover.isFinite
  (cover.π ≫ Scheme.Opens.ι T.support.compl).normalization

/-- The canonical normalization map; it has precisely the data of relative normalization.
Source: ILO IX 2.1, pp. 133--134 (blueprint: lem-per-snc-parameter-root-quotient). -/
abbrev sncTorsorNormalizationMap {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (T : Y.IdealSheafData) {G : Type v} [Group G]
    (cover : Scheme.GaloisCoverAction G (Scheme.Opens.toScheme T.support.compl)) :
    sncTorsorNormalization T cover ⟶ Y :=
  letI : IsFinite cover.π := cover.isFinite
  (cover.π ≫ Scheme.Opens.ι T.support.compl).fromNormalization

/-- Etale-local parameter-root invariant-ring normal form, including prescribed equations.
Source: ILO IX 2.1, pp. 133--134, specialized as in IX 2.2
(blueprint: lem-per-snc-parameter-root-quotient).

Proof. (1) Choose an affine pointed neighbourhood, remove components not through the point,
and use the regular-boundary chart; smooth ascent and the strict-henselization cotangent
comparison preserve the chosen partial parameter system. (2) Normalize and base change to
the strict henselization. Normalization commutes with etale base change; finite presentation
and the henselian finite-algebra product theorem give the normal local factor selected by
`zbar`. Normality of this factor follows from etale-colimit normality. (3) Strict-local roots
of unity and the simultaneous-root algebra structure give the regular strictly henselian
root algebra and its Galois rotations. (4) Simultaneous-root punctured-torsor splitting embeds
the chosen field factor in its fraction field. (5) The fixed-field theorem gives the subgroup
fixing this factor. (6) Integral closure identifies its normalization with the fixed subring.
(7) Descend the root of unity, its inverse, the unit differences, and the idempotent selecting
the factor by finite-data descent. (8) Monic division gives the root-monomial basis; a
nontrivial character has unit difference from one, so invariants have exactly the invariant
monomial basis. This also proves the required base-change compatibility of invariants.
(9) Finite-presentation isomorphism descent gives the invariant-ring identification on a
pointed etale refinement. (10) The selected open-and-closed factor gives `W`, etale over the
normalization, and finite over the affine base, hence Noetherian. Equations have only been
pulled back, giving the refinement clause. With empty boundary there are no parameters,
the root algebra is canonically `A`, and the subgroup of the zero group is zero.

Here the normalization is the relative normalization of the torsor over `Y`. Since the
connected etale cover of the regular open is normal and integral, its integral closure
on each affine open is also the integral closure in its function field, so this is exactly
the normalization in `k(V')/k(Y)` of the node, using the published normalization construction.
-/
theorem exists_snc_parameter_root_quotient
    (Y : Scheme.{u}) [IsIntegral Y] [IsNoetherian Y]
    (_hYregular : IsRegularScheme Y)
    (T : Y.IdealSheafData) (_hT : IsStrictNormalCrossingsBoundary T)
    {G : Type v} [Group G] [Finite G]
    (_hn : IsUnit (Nat.card G : Γ(Y, ⊤)))
    (cover : Scheme.GaloisCoverAction G (Scheme.Opens.toScheme T.support.compl))
    [ConnectedSpace cover.Z]
    [_hfinite : IsFinite (sncTorsorNormalizationMap T cover)]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (ybar : Spec (.of Ω) ⟶ Y)
    (zbar : Spec (.of Ω) ⟶ sncTorsorNormalization T cover)
    (_hzbar : zbar ≫ (sncTorsorNormalizationMap T cover) = ybar) :
    (∃ (A : CommRingCat.{u}) (_ : IsNoetherianRing A)
      (uA : Spec A ⟶ Y) (uΩ : Spec (.of Ω) ⟶ Spec A) (r : ℕ) (t : Fin r → A),
      IsSncParameterRootQuotientAt T (sncTorsorNormalizationMap T cover)
        ybar zbar (Nat.card G) r A uA uΩ t) ∧
    (∀ (U₀ : Scheme.{u}) (u₀ : U₀ ⟶ Y) [Etale u₀]
      (u₀Ω : Spec (.of Ω) ⟶ U₀), u₀Ω ≫ u₀ = ybar →
      ∀ (r : ℕ) (t₀ : Fin r → Γ(U₀, ⊤)),
        @IsSncParameterGerms U₀ (LocallyOfFiniteType.isLocallyNoetherian u₀)
          (u₀ ⁻¹' (T.support : Set Y))
          (Scheme.SpecToEquivOfField Ω U₀ u₀Ω).1 r t₀ →
        ∃ (A : CommRingCat.{u}) (_ : IsNoetherianRing A)
          (uA : Spec A ⟶ Y) (uΩ : Spec (.of Ω) ⟶ Spec A)
          (q : Spec A ⟶ U₀) (t : Fin r → A),
          Etale q ∧ q ≫ u₀ = uA ∧ uΩ ≫ q = u₀Ω ∧
          (∀ i, (Scheme.ΓSpecIso A).inv (t i) = q.appTop (t₀ i)) ∧
          IsSncParameterRootQuotientAt T (sncTorsorNormalizationMap T cover)
            ybar zbar (Nat.card G) r A uA uΩ t) := by
  sorry

end AlgebraicGeometry
