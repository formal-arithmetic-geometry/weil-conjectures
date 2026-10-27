/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import WeilConjectures.AlgebraicGeometry.NormalScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import Sheaf.RingTheory.ParameterRootAlgebra
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Data.ZMod.Basic

import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.RingTheory.Noetherian.Basic
import Sheaf.AlgebraicGeometry.EtaleNormalComponents
import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres
import Sheaf.AlgebraicGeometry.FinitePresentationOfFiniteLocallyNoetherian
import Sheaf.RingTheory.ColimitCategoryFpAlgebras
import WeilConjectures.AlgebraicGeometry.Morphisms.AffineFpIsoIndEtaleDescent
import WeilConjectures.AlgebraicGeometry.Morphisms.StrictLocalRootsOfUnity
import WeilConjectures.RingTheory.EtaleColimitNormalLocalDomain
import WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct
import WeilConjectures.RingTheory.RegularRingSmoothAscent
import WeilConjectures.RingTheory.StrictHenselizationCotangentDimension
import WeilConjectures.RingTheory.StrictHenselizationRegular
import WeilConjectures.RingTheory.StrictHenselizationTriples

/-!
# Pointed parameter-root quotient neighbourhoods

Source: ILO, Travaux de Gabber, Expose IX, Proposition 2.1 proof, pp.133--134,
and IX 2.2 (blueprint: lem-per-snc-parameter-root-quotient).

The two structures spell out the prescribed parameter equations and the conclusion.
The root ring is the existing simultaneous polynomial quotient. Its action is specified
on every root and fixes the coefficient ring; the invariant algebra is an intersection
of Mathlib equalizer subalgebras, with its actual inclusion and coefficient map.
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- A pointed affine etale neighbourhood equipped with equations of the boundary branches
through its selected point. Other components may still be present away from this point:
the equation and integral-component conditions are required on an open neighbourhood `D`.
The ordered equations extend to a regular system of parameters in the local ring.
Source: ILO IX 2.1 proof, p.133, parameter reduction
(blueprint: lem-per-snc-parameter-root-quotient). -/
structure SNCParameterNeighborhood {Y : Scheme.{u}} (T : Y.IdealSheafData)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) where
  A : CommRingCat.{u}
  [noetherian : IsNoetherianRing A]
  u : Spec A ⟶ Y
  etale : Etale u
  point : Spec (.of Ω) ⟶ Spec A
  point_base : point ≫ u = y
  t : List A
  vanishing : ∀ a ∈ t, a ∈ (point (IsLocalRing.closedPoint Ω)).asIdeal
  parameters : ∃ p : List ((Spec A).presheaf.stalk (point (IsLocalRing.closedPoint Ω))),
    IsLocalRing.IsRegularSystemOfParameters p ∧
      (t.map (StructureSheaf.toStalk A (point (IsLocalRing.closedPoint Ω))).hom).Sublist p
  local_equations : ∃ D : (Spec A).Opens, point (IsLocalRing.closedPoint Ω) ∈ D ∧
    (T.comap u).comap D.ι =
      (Scheme.IdealSheafData.ofIdealTop
        (Ideal.span {(Scheme.ΓSpecIso A).inv t.prod})).comap D.ι ∧
    (∀ i : Fin t.length,
      IsIntegral (((Scheme.IdealSheafData.ofIdealTop
        (Ideal.span {(Scheme.ΓSpecIso A).inv (t.get i)})).comap D.ι).subscheme)) ∧
    Function.Injective (fun i : Fin t.length ↦
      ((Scheme.IdealSheafData.ofIdealTop
        (Ideal.span {(Scheme.ΓSpecIso A).inv (t.get i)})).comap D.ι).support)

attribute [instance] SNCParameterNeighborhood.noetherian

/-- The complete pointed quotient model. The additive subgroup is the subgroup of
`(Z/nZ)^r` in the source; `action` is an action by coefficient-algebra automorphisms,
pinned by the displayed coordinate formula. Thus it is the specified rotation action,
rather than an unspecified action or an arbitrary comparison map.
Source: ILO IX 2.1 proof, pp.133--134
(blueprint: lem-per-snc-parameter-root-quotient). -/
structure SNCParameterRootQuotient {Y Z : Scheme.{u}} (T : Y.IdealSheafData)
    (b : Z ⟶ Y) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (z : Spec (.of Ω) ⟶ Z) (n : ℕ)
    extends SNCParameterNeighborhood T y where
  regular : IsRegularRing A
  equations : T.comap u = Scheme.IdealSheafData.ofIdealTop
    (Ideal.span {(Scheme.ΓSpecIso A).inv t.prod})
  components : ∀ i : Fin t.length,
    IsIntegral ((Scheme.IdealSheafData.ofIdealTop
      (Ideal.span {(Scheme.ΓSpecIso A).inv (t.get i)})).subscheme)
  distinct_components : Function.Injective (fun i : Fin t.length ↦
    (Scheme.IdealSheafData.ofIdealTop
      (Ideal.span {(Scheme.ΓSpecIso A).inv (t.get i)})).support)
  complement : u ⁻¹ᵁ T.support.compl = PrimeSpectrum.basicOpen t.prod
  empty_boundary : T.support = ⊥ → t = []
  zeta : Aˣ
  zeta_pow : (zeta : A) ^ n = 1
  zeta_difference : ∀ a : ℕ, 1 ≤ a → a < n → IsUnit (1 - (zeta : A) ^ a)
  H : AddSubgroup (Fin t.length → ZMod n)
  action : H →+ Additive (Algebra.ParameterRoot.Ring t.get n ≃ₐ[A]
    Algebra.ParameterRoot.Ring t.get n)
  action_root : ∀ (h : H) (i : Fin t.length),
    (action h).toMul (Algebra.ParameterRoot.root t.get n i) =
      algebraMap A (Algebra.ParameterRoot.Ring t.get n) ((zeta : A) ^ (h.val i).val) *
        Algebra.ParameterRoot.root t.get n i
  W : Scheme.{u}
  affine : IsAffine W
  noetherian_W : IsNoetherian W
  w : W ⟶ Z
  etale_W : Etale w
  to_base : W ⟶ Spec A
  square : w ≫ b = to_base ≫ u
  lift : Spec (.of Ω) ⟶ W
  lift_z : lift ≫ w = z
  lift_base : lift ≫ to_base = point
  iso : W ≅ Spec (.of ↥(⨅ h : H,
    AlgHom.equalizer (action h).toMul.toAlgHom (AlgHom.id A _)))
  iso_over : iso.hom ≫ Spec.map (CommRingCat.ofHom
    (algebraMap A ↥(⨅ h : H,
      AlgHom.equalizer (action h).toMul.toAlgHom (AlgHom.id A _)))) = to_base

/-- A connected finite etale torsor of invertible order admits the parameter-root
invariant-ring normal form, through any selected geometric point of its finite
normalization. The second conjunct preserves any prescribed pointed parameter equations.
The existential integral and coefficient-algebra structures make the function field
and its canonical normalization available without assuming integrality of the cover.
Their generic-point square pins the field extension to the given morphism.

Source: ILO IX 2.1 proof, pp.133--134, specialized as in IX 2.2
(blueprint: lem-per-snc-parameter-root-quotient).

Proof:
1. Choose an affine pointed boundary chart, refining the prescribed chart when given,
   and remove the other components (lem-per-regular-boundary-divisorial-chart).
   Smooth ascent gives regularity. The pointed-neighbourhood colimit is the strict
   henselization; etale zero-dimensional fibres, its maximal ideal and its cotangent
   space preserve the given parameters
   (lem-weil-pbc-strict-henselization-triples, lem-sc-strict-henselization-regular,
   lem-sc-strict-henselization-cotangent-dimension,
   lem-weil-pbc-etale-smooth-zero-dimensional-fibres).
2. Normalization commutes with etale base change. Its finite algebra over the strict
   local ring splits into local factors; select the factor containing the chosen lift.
   Each factor is a normal domain, and its fraction field is a finite extension of
   the base fraction field (lem-sbc-relative-normalization-smooth-base-change,
   lem-weil-pbc-finite-over-henselian-local-product,
   lem-weil-pbc-etale-colimit-normal-local-domain, lem-fin-etale-normal-components).
3. Choose a primitive nth root with unit nontrivial differences. The simultaneous-root
   algebra is a regular strictly henselian local domain, free on bounded monomials;
   its fraction field is Galois with rotation group (Z/nZ)^r
   (lem-sbc-strict-local-roots-of-unity, lem-per-snc-root-algebra-structure).
4. The torsor splits after adjoining these roots. A projection of its generic scalar
   extension embeds the selected field factor into this Galois field
   (lem-per-snc-root-punctured-torsor-splitting).
5. Let H fix the embedded field. The fixed-field theorem identifies that field with
   the H-fixed field (lem-exc-etale-galois-fixed-field-subgroup); the selected component
   need not have degree n. Both normal finite rings are the respective integral closures,
   so the selected factor equals the H-invariant root algebra
   (def-fin-normalization-extension).
6. Descend the root of unity, its inverse, the unit-difference inverses, and the factor
   idempotent through the pointed-etale colimit, including all their equations
   (lem-weil-pbc-strict-henselization-triples, lem-weil-pbc-colimit-category-fp-algebras).
7. Monic division gives the bounded-monomial basis over any coefficient ring. Invariance
   forces exactly the noninvariant coefficients to vanish, since nontrivial character
   values have unit difference from 1. The remaining monomial basis shows that this
   invariant algebra commutes with the scalar extensions used here.
8. Finite algebras over the Noetherian neighbourhood are finitely presented. Descend the
   strict-local isomorphism to a pointed affine etale refinement
   (pqf-lem-finite-fp-locnoeth, lem-weil-pbc-regular-ring-smooth-ascent,
   lem-sbc-affine-fp-iso-ind-etale-descent).
9. Take W to be the descended open-and-closed factor in the normalization pullback.
   Its map to Z is etale by base change and open restriction, and it contains the
   selected lift. It is finite over A and hence Noetherian
   (lem-weil-pbc-etale-scheme-base-change, lem-weil-pbc-finite-algebra-noetherian).
10. The parameters are pulled back from the initial chart. For empty boundary their
    list is empty, the root algebra is A, and the subgroup is trivial. -/
theorem exists_sncParameterRootQuotient
    (Y : Scheme.{u}) [IsIntegral Y] [IsNoetherian Y] (_hY : IsRegularScheme Y)
    (T : Y.IdealSheafData) (_hT : IsStrictNormalCrossingsBoundary T)
    (G : Type v) [Group G] [Finite G]
    (_hn : ∀ x : Y, IsUnit (Nat.card G : Y.presheaf.stalk x))
    (P : Scheme.GaloisCoverAction G (Scheme.Opens.toScheme T.support.compl))
    [ConnectedSpace P.Z] :
    ∃ (_ : IsIntegral P.Z) (_ : Algebra Y.functionField P.Z.functionField),
      Y.fromSpecOfAlgebraFunctionField P.Z.functionField =
        P.Z.fromSpecFunctionField ≫ P.π ≫ Scheme.Opens.ι T.support.compl ∧
      (IsFinite (Y.fromNormalizationIn P.Z.functionField) →
        ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
          (y : Spec (.of Ω) ⟶ Y)
          (z : Spec (.of Ω) ⟶ Y.normalizationIn P.Z.functionField),
          z ≫ Y.fromNormalizationIn P.Z.functionField = y →
          Nonempty (SNCParameterRootQuotient T (Y.fromNormalizationIn P.Z.functionField)
            y z (Nat.card G)) ∧
          ∀ Q : SNCParameterNeighborhood T y,
            ∃ M : SNCParameterRootQuotient T (Y.fromNormalizationIn P.Z.functionField)
                y z (Nat.card G),
              ∃ f : Q.A ⟶ M.A,
                Etale (Spec.map f) ∧ Spec.map f ≫ Q.u = M.u ∧
                M.point ≫ Spec.map f = Q.point ∧ M.t = Q.t.map f.hom) := by
  sorry

end AlgebraicGeometry
