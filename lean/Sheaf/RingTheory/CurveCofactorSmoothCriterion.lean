/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Sheaf.RingTheory.AffineConormalJacobianRealization
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import Mathlib.Topology.KrullDimension
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.RingTheory.SingularIdeal
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import WeilConjectures.RingTheory.SmoothLocalizationConormalSplit
import WeilConjectures.LinearAlgebra.Matrix.LeftInverseMinors

/-! # Smoothness detected by the conormal cofactor of a curve

Source: Stacks Project, Duality, Tags 0E9Y and 0E9Z; Algebra, Tags 00T6, 00T7,
00T8 and 07DQ; Morphisms, Tags 01V6 and 02G1
(blueprint: lem-sfb-curve-cofactor-smooth-criterion).

The complex and the map are those of the recorded affine conormal realization.
A `Chart` merely supplies its canonical identifications, not a new polynomial
presentation or an assumed splitting. Smooth-open assertions range over every
open affine chart, including the identity and the empty affine.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Algebra.CotangentResolution
open scoped TensorProduct

namespace Algebra.AffineConormal

/-- The selected maximal minor, with equations indexing rows and the ordered
selected variables indexing columns. For no equations this is the empty determinant.
Source: Stacks, Algebra, Tag 00T8
(blueprint: lem-sfb-curve-cofactor-smooth-criterion). -/
def curveJacobianMinor {R : Type u} [CommRing R] {c : ℕ}
    (f : Fin c → PolynomialRing R c) (s : Fin c ↪ Fin (c + 1)) : PolynomialRing R c :=
  Matrix.det (fun i j : Fin c ↦ MvPolynomial.pderiv (s j) (f i))

/-- The explicit equations after adjoining the inverse variable `z`, which is
indexed last. The selected columns of the presentation put `z` after the selected
old variables, before the remaining old variable.
Source: Stacks, Algebra, Tag 00T8
(blueprint: lem-sfb-curve-cofactor-smooth-criterion). -/
def curveLocalizationEquations {R : Type u} [CommRing R] {c : ℕ}
    (f : Fin c → PolynomialRing R c) (s : Fin c ↪ Fin (c + 1)) :
    Fin (c + 1) → MvPolynomial (Fin (c + 2)) R :=
  Fin.snoc (α := fun _ ↦ MvPolynomial (Fin (c + 2)) R)
    (fun i ↦ MvPolynomial.rename Fin.castSucc (f i))
    (MvPolynomial.X (Fin.last (c + 1)) *
      MvPolynomial.rename Fin.castSucc (curveJacobianMinor f s) - 1)

/-- The selected columns in the enlarged Jacobian: the old selected variables,
then the inverse variable. Thus the last unselected variable follows these columns.
Source: Stacks, Algebra, Tag 00T8
(blueprint: lem-sfb-curve-cofactor-smooth-criterion). -/
def curveLocalizationColumns {c : ℕ} (s : Fin c ↪ Fin (c + 1)) :
    Fin (c + 1) → Fin (c + 2) :=
  Fin.snoc (α := fun _ ↦ Fin (c + 2)) (fun i ↦ (s i).castSucc) (Fin.last (c + 1))

/-- The actual geometric fibre over the chosen algebraic closure of the residue
field at `y`; this is the pullback in def-weil-geometric-fibre.
Source: Stacks, Morphisms, Tags 01K0 and 02G1
(blueprint: lem-sfb-curve-cofactor-smooth-criterion). -/
def curveGeometricFibre {R : Type u} [CommRing R] {c : ℕ}
    (f : Fin c → PolynomialRing R c) (y : Spec (CommRingCat.of R)) : Scheme.{u} :=
  pullback (Spec.map (CommRingCat.ofHom (algebraMap R (QuotientRing f))))
    (Spec.map (CommRingCat.ofHom
      (algebraMap ((Spec (CommRingCat.of R)).residueField y)
        (AlgebraicClosure ((Spec (CommRingCat.of R)).residueField y)))) ≫
      (Spec (CommRingCat.of R)).fromSpecResidueField y)

variable [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]

/-- The canonical map from ambient differentials to relative differentials, via
its recorded cokernel identification.
Source: Stacks, Duality, Tag 0E9Y
(blueprint: lem-sfb-curve-cofactor-smooth-criterion). -/
def Chart.curveProjection {R : Type u} [CommRing R] {c : ℕ}
    {f : Fin c → PolynomialRing R c} {C : Coherence.{u}} {κ : Naive.Comparison C}
    {A : CommRingCat.{u}} [Algebra R A] {φ : QuotientRing f →ₐ[R] A}
    (H : Chart f C κ A φ) : (chartComplex f A φ).zero →ₗ[A] Ω[A⁄R] :=
  H.omega.toLinearMap.comp (LinearMap.range (chartComplex f A φ).differential.hom).mkQ

/-- Exactness, splitting and the line property on an arbitrary smooth affine open.
The comparison is normalized on every conormal basis and every lift. A basis of
conormal vectors followed by a lifted differential generator is an ambient basis.
These formulas fix the relation-first sign to `+1`.
Source: Stacks, Duality, Tag 0E9Y; Smoothing Ring Maps, Tag 07EZ
(blueprint: lem-sfb-curve-cofactor-smooth-criterion). -/
def Chart.CurveSmoothSplitting {R : Type u} [CommRing R] {c : ℕ}
    {f : Fin c → PolynomialRing R c} {C : Coherence.{u}} {κ : Naive.Comparison C}
    {A : CommRingCat.{u}} [Algebra R A] {φ : QuotientRing f →ₐ[R] A}
    (H : Chart f C κ A φ) : Prop :=
  Function.Injective (chartComplex f A φ).differential.hom ∧
  Function.Surjective H.curveProjection ∧
  LinearMap.ker H.curveProjection = LinearMap.range (chartComplex f A φ).differential.hom ∧
  (∃ l : (chartComplex f A φ).zero →ₗ[A] (chartComplex f A φ).neg,
    l.comp (chartComplex f A φ).differential.hom = LinearMap.id) ∧
  (∃ t : Ω[A⁄R] →ₗ[A] (chartComplex f A φ).zero,
    H.curveProjection.comp t = LinearMap.id) ∧
  (∀ p : PrimeSpectrum A,
    Nonempty ((Localization.AtPrime p.asIdeal ⊗[A] Ω[A⁄R]) ≃ₗ[Localization.AtPrime p.asIdeal]
      Localization.AtPrime p.asIdeal)) ∧
  (∃ e : (chartComplex f A φ).cofactorLine c ≃ₗ[A] Ω[A⁄R],
    e.toLinearMap.comp H.w = LinearMap.id ∧
    ∀ (b : Module.Basis (Fin c) A (chartComplex f A φ).neg)
      (v : (chartComplex f A φ).zero),
      e (topDual b ⊗ₜ[A] exteriorPower.ιMulti A (c + 1)
        (Fin.snoc (α := fun _ ↦ (chartComplex f A φ).zero)
          (fun i ↦ (chartComplex f A φ).differential.hom (b i)) v)) =
        H.curveProjection v) ∧
  (∀ (b : Module.Basis (Fin c) A (chartComplex f A φ).neg)
    (a : Module.Basis (Fin 1) A Ω[A⁄R]) (v : (chartComplex f A φ).zero),
    H.curveProjection v = a 0 →
    ∃ d : Module.Basis (Fin (c + 1)) A (chartComplex f A φ).zero,
      (∀ j, d j = Fin.snoc (α := fun _ ↦ (chartComplex f A φ).zero)
        (fun i ↦ (chartComplex f A φ).differential.hom (b i)) v j) ∧
      H.w (a 0) = topDual b ⊗ₜ[A] exteriorPower.ιMulti A (c + 1) d)

/-- The cofactor criterion, the explicit `zh-1` standard smooth chart, and the
relation-first smooth comparison, including empty equations.
Source: Stacks, Duality, Tags 0E9Y and 0E9Z; Algebra, Tags 00T6--00T8 and 07DQ;
Morphisms, Tags 01V6 and 02G1
(blueprint: lem-sfb-curve-cofactor-smooth-criterion).

Proof:
1. Use lem-sfb-affine-conormal-jacobian-realization to identify the conormal and
ambient modules with their equation and coordinate bases. Expand the augmented
Jacobian along its last row: w(dx_j) = (-1)^(c+j) Delta_j times the oriented
line generator. These differentials generate Omega. In the local ring, their
images generate the line exactly when one maximal minor is a unit. A bijection
is surjective.
2. On a selected minor h, write the conormal matrix as (M;b). By
lem-weil-pbc-matrix-adjugate-identity, M has inverse h^(-1) adj(M). The selected
projection followed by this inverse is a left inverse. Subtracting its image
leaves only the remaining coordinate. Thus the sequence splits, its quotient
is a line, and w sends the remaining coordinate to a unit times the volume.
3. Adjoin z with zh-1. The selected columns are the selected old variables and z.
The Jacobian block has diagonal M,h, hence determinant h^2. This is precisely
a presentation in def-weil-pbc-standard-smooth-algebra. Apply
lem-weil-pbc-standard-smooth-is-smooth and
lem-weil-pbc-smooth-ring-map-iff-smooth-affine.
4. Conversely restrict a smooth neighbourhood to a principal one, using
lem-weil-pbc-smooth-restrict-open-subschemes and the affine comparison. Apply
lem-weil-pbc-smooth-localization-conormal-split to the original presentation.
Its left inverse, together with lem-weil-pbc-matrix-left-inverse-minors at f=1,
puts 1 in the maximal minor ideal. At a prime at least one minor is a unit.
5. These principal charts cover every smooth open. They give the exact locally
split sequence and the line quotient. On a smooth affine open the projective
quotient splits the sequence globally. Wedge a conormal basis before a lift of
a differential generator. Changing the lift adds a repeated relation vector;
changing the conormal basis cancels the determinant with its dual. Thus the
comparisons agree on overlaps and their inverse composed with w is the identity.
6. For c=0 the sole minor is 1, the inverse equation is z-1, and w(dx_0)=dx_0.
An empty geometric fibre has no irreducible components, so its purity condition
is vacuous. All assertions on an empty smooth affine open have their usual
zero-module interpretation. No Noetherian or characteristic assumption is used. -/
theorem curve_cofactor_smooth_criterion
    (R : Type u) [CommRing R] (c : ℕ) (f : Fin c → PolynomialRing R c)
    (_hr : RingTheory.Sequence.IsRegular (PolynomialRing R c) (List.ofFn f))
    [Module.Flat R (QuotientRing f)]
    (_hfib : ∀ (y : Spec (CommRingCat.of R)) (Z : Set (curveGeometricFibre f y)),
      Z ∈ irreducibleComponents (curveGeometricFibre f y) → topologicalKrullDim Z = 1)
    (C : Coherence.{u}) (κ : Naive.Comparison C)
    (H : Chart f C κ (CommRingCat.of (QuotientRing f)) (AlgHom.id R (QuotientRing f))) :
    (∀ p : PrimeSpectrum (QuotientRing f),
      (Function.Bijective (H.w.baseChange (Localization.AtPrime p.asIdeal)) ↔
        Function.Surjective (H.w.baseChange (Localization.AtPrime p.asIdeal))) ∧
      (Function.Surjective (H.w.baseChange (Localization.AtPrime p.asIdeal)) ↔
        ∃ s : Fin c ↪ Fin (c + 1), IsUnit (algebraMap (QuotientRing f)
          (Localization.AtPrime p.asIdeal) (Ideal.Quotient.mk (ideal f)
            (curveJacobianMinor f s)))) ∧
      ((∃ s : Fin c ↪ Fin (c + 1), IsUnit (algebraMap (QuotientRing f)
          (Localization.AtPrime p.asIdeal) (Ideal.Quotient.mk (ideal f)
            (curveJacobianMinor f s)))) ↔ IsSmoothAtPrime R p)) ∧
    (∀ (s : Fin c ↪ Fin (c + 1)) (p : PrimeSpectrum (QuotientRing f)),
      Ideal.Quotient.mk (ideal f) (curveJacobianMinor f s) ∉ p.asIdeal →
      ∃ P : SubmersivePresentation R
          (Localization.Away (Ideal.Quotient.mk (ideal f) (curveJacobianMinor f s)))
          (Fin (c + 2)) (Fin (c + 1)),
        P.relation = curveLocalizationEquations f s ∧
        P.map = curveLocalizationColumns s ∧
        (∀ j : Fin (c + 1), P.val j.castSucc = algebraMap (QuotientRing f)
          (Localization.Away (Ideal.Quotient.mk (ideal f) (curveJacobianMinor f s)))
            (Ideal.Quotient.mk (ideal f) (MvPolynomial.X j))) ∧
        P.val (Fin.last (c + 1)) =
          IsLocalization.Away.invSelf (Ideal.Quotient.mk (ideal f) (curveJacobianMinor f s)) ∧
        P.jacobian = (algebraMap (QuotientRing f)
          (Localization.Away (Ideal.Quotient.mk (ideal f) (curveJacobianMinor f s)))
            (Ideal.Quotient.mk (ideal f) (curveJacobianMinor f s))) ^ 2 ∧
        IsStandardSmooth R
          (Localization.Away (Ideal.Quotient.mk (ideal f) (curveJacobianMinor f s)))) ∧
    (∀ (A : CommRingCat.{u}) [Algebra R A] (φ : QuotientRing f →ₐ[R] A)
      (_ho : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom)))
      (H' : Chart f C κ A φ), Smooth R A → H'.CurveSmoothSplitting) ∧
    (c = 0 →
      (∀ s : Fin c ↪ Fin (c + 1), curveJacobianMinor f s = 1) ∧
      H.w (KaehlerDifferential.D R (QuotientRing f)
        (Ideal.Quotient.mk (ideal f) (MvPolynomial.X 0))) =
        topDual H.negBasis ⊗ₜ[QuotientRing f]
          exteriorPower.ιMulti (QuotientRing f) (c + 1) H.zeroBasis) := by
  sorry

end Algebra.AffineConormal
