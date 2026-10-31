/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RegularHilbertCoefficientDatum
public import WeilConjectures.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

import WeilConjectures.AlgebraicGeometry.Modules.Differentials
import WeilConjectures.AlgebraicGeometry.EtaleAtPointFromDifferentials
import WeilConjectures.RingTheory.FormallyEtaleAssociatedGraded
import WeilConjectures.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import WeilConjectures.AlgebraicGeometry.FlatUnramifiedFormallyEtale
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties

/-!
# Implicit transverse coordinates and regular Taylor coefficients

Source: ILO VIII 2.3.11 and 2.3.13; Bierstone--Milman, Invent. Math. 128 (1997),
Lemma 3.5 and Remarks 3.7, 9.9, 9.11. The algebraic nonclosed-point interpretation and
proof are the fifteen steps of the DAG node
(blueprint: lem-trf-implicit-taylor-coordinate-calculus).

All schemes and all their open subsets are allowed. The coordinate affine spaces are
written as polynomial spectra. `isTaylorMap` is the existing coordinate/residue
characterization: at a nonclosed point it retains every relative coordinate, and hence
characterizes completion after passage to the residue-field-valued diagonal point,
not completion of the original stalk. Substitution uses Mathlib's actual formal
substitution. The auxiliary structures specify conclusions; they choose no witnesses.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.HilbertCoefficient

/-- Restriction of the specified regular coordinate functions to an open subset.
Source: the affine-chart calculation in step 1
(blueprint: lem-trf-implicit-taylor-coordinate-calculus). -/
def implicitCoordinatesOnOpen {k : Type u} [Field k] {B : Scheme.{u}} {m r : ℕ}
    (c : MvPolynomial (Fin m ⊕ Fin r) k →+* Γ(B, ⊤)) (U : B.Opens) :
    MvPolynomial (Fin m ⊕ Fin r) k →+* Γ(B, U) :=
  (B.presheaf.map (homOfLE le_top).op).hom.comp c

/-- The same coordinates as germs at the specified point.
Source: the germ extension in steps 3 and 7
(blueprint: lem-trf-implicit-taylor-coordinate-calculus). -/
def implicitCoordinatesAt {k : Type u} [Field k] {B : Scheme.{u}} {m r : ℕ}
    (c : MvPolynomial (Fin m ⊕ Fin r) k →+* Γ(B, ⊤)) (x : B) :
    MvPolynomial (Fin m ⊕ Fin r) k →+* B.presheaf.stalk x :=
  (B.presheaf.germ ⊤ x (by trivial)).hom.comp c

/-- Regular coordinate derivations on every open, compatible with restriction.
The use of `ℤ`-derivations is unbundled: `scalar` says exactly that they kill `k`.
Source: the differential basis, universal property and commutator calculation, step 1
(blueprint: lem-trf-implicit-taylor-coordinate-calculus). -/
structure ImplicitCoordinateDerivations {k : Type u} [Field k]
    (B : Scheme.{u}) {m r : ℕ}
    (c : MvPolynomial (Fin m ⊕ Fin r) k →+* Γ(B, ⊤)) where
  deriv : ∀ U : B.Opens, (Fin m ⊕ Fin r) → Derivation ℤ Γ(B, U) Γ(B, U)
  scalar : ∀ (U : B.Opens) (i : Fin m ⊕ Fin r) (t : k),
    deriv U i (implicitCoordinatesOnOpen c U (MvPolynomial.C t)) = 0
  coordinate : ∀ (U : B.Opens) (i j : Fin m ⊕ Fin r),
    deriv U i (implicitCoordinatesOnOpen c U (MvPolynomial.X j)) = if i = j then 1 else 0
  restriction : ∀ (U V : B.Opens) (e : V ≤ U) (i : Fin m ⊕ Fin r) (f : Γ(B, U)),
    (B.presheaf.map (homOfLE e).op) (deriv U i f) =
      deriv V i ((B.presheaf.map (homOfLE e).op) f)
  commute : ∀ (U : B.Opens) (i j : Fin m ⊕ Fin r) (f : Γ(B, U)),
    deriv U i (deriv U j f) = deriv U j (deriv U i f)

/-- The actual transverse Jacobian determinant, a regular function on the original scheme.
Source: step 2 (blueprint: lem-trf-implicit-taylor-coordinate-calculus). -/
def implicitJacobian {k : Type u} [Field k] {B : Scheme.{u}} {m r : ℕ}
    {c : MvPolynomial (Fin m ⊕ Fin r) k →+* Γ(B, ⊤)}
    (D : ImplicitCoordinateDerivations B c) (h : Fin r → Γ(B, ⊤)) : Γ(B, ⊤) :=
  Matrix.det (fun i j : Fin r ↦ D.deriv ⊤ (Sum.inr j) (h i))

/-- The nonvanishing locus of the transverse Jacobian, with no chosen shrinking.
Source: step 2 (blueprint: lem-trf-implicit-taylor-coordinate-calculus). -/
def implicitJacobianOpen {k : Type u} [Field k] {B : Scheme.{u}} {m r : ℕ}
    {c : MvPolynomial (Fin m ⊕ Fin r) k →+* Γ(B, ⊤)}
    (D : ImplicitCoordinateDerivations B c) (h : Fin r → Γ(B, ⊤)) : B.Opens :=
  B.basicOpen (implicitJacobian D h)

/-- The ideal generated by the restricted equations on the Jacobian open.
This is a scheme-theoretic ideal, not the radical of the set of common zeros.
Source: steps 2 and 8 (blueprint: lem-trf-implicit-taylor-coordinate-calculus). -/
def implicitEquationIdeal {k : Type u} [Field k] {B : Scheme.{u}} {m r : ℕ}
    {c : MvPolynomial (Fin m ⊕ Fin r) k →+* Γ(B, ⊤)}
    (D : ImplicitCoordinateDerivations B c) (h : Fin r → Γ(B, ⊤)) :
    (implicitJacobianOpen D h).toScheme.IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop
    (Ideal.span (Set.range fun i : Fin r ↦ (implicitJacobianOpen D h).ι.appTop (h i)))

/-- The closed subscheme V(h) of the full Jacobian nonvanishing locus.
Source: step 2 (blueprint: lem-trf-implicit-taylor-coordinate-calculus). -/
def implicitZeroScheme {k : Type u} [Field k] {B : Scheme.{u}} {m r : ℕ}
    {c : MvPolynomial (Fin m ⊕ Fin r) k →+* Γ(B, ⊤)}
    (D : ImplicitCoordinateDerivations B c) (h : Fin r → Γ(B, ⊤)) : Scheme.{u} :=
  (implicitEquationIdeal D h).subscheme

/-- The canonical inclusion N -> B, through the Jacobian open.
Source: step 2 (blueprint: lem-trf-implicit-taylor-coordinate-calculus). -/
def implicitZeroInclusion {k : Type u} [Field k] {B : Scheme.{u}} {m r : ℕ}
    {c : MvPolynomial (Fin m ⊕ Fin r) k →+* Γ(B, ⊤)}
    (D : ImplicitCoordinateDerivations B c) (h : Fin r → Γ(B, ⊤)) :
    implicitZeroScheme D h ⟶ B :=
  (implicitEquationIdeal D h).subschemeι ≫ (implicitJacobianOpen D h).ι

/-- The morphism to the polynomial spectrum specified by a list of global coordinates.
Source: the coordinate morphisms in steps 1--3
(blueprint: lem-trf-implicit-taylor-coordinate-calculus). -/
def implicitCoordinateMorphism {σ : Type} {k : Type u} [Field k] {B : Scheme.{u}}
    (c : MvPolynomial σ k →+* Γ(B, ⊤)) : B ⟶ Spec (CommRingCat.of (MvPolynomial σ k)) :=
  B.toSpecΓ ≫ Spec.map (CommRingCat.ofHom c)

/-- The structure morphism to k determined by the given coordinates.
Source: step 1 (blueprint: lem-trf-implicit-taylor-coordinate-calculus). -/
def implicitStructureMorphism {σ : Type} {k : Type u} [Field k] {B : Scheme.{u}}
    (c : MvPolynomial σ k →+* Γ(B, ⊤)) : B ⟶ Spec (CommRingCat.of k) :=
  B.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (c.comp MvPolynomial.C))

/-- The given w coordinates on N, obtained by actual restriction.
Source: step 2 (blueprint: lem-trf-implicit-taylor-coordinate-calculus). -/
def implicitTangentialCoordinates {k : Type u} [Field k] {B : Scheme.{u}} {m r : ℕ}
    {c : MvPolynomial (Fin m ⊕ Fin r) k →+* Γ(B, ⊤)}
    (D : ImplicitCoordinateDerivations B c) (h : Fin r → Γ(B, ⊤)) :
    MvPolynomial (Fin m) k →+* Γ(implicitZeroScheme D h, ⊤) :=
  (implicitZeroInclusion D h).appTop.hom.comp
    (c.comp (MvPolynomial.rename Sum.inl).toRingHom)

/-- The genuine substitution Y = phi(W) + Z, fixing W.
Source: step 6 (blueprint: lem-trf-implicit-taylor-coordinate-calculus). -/
def implicitShiftVariables {m r : ℕ} {L : Type u} [Field L]
    (φ : Fin r → MvPowerSeries (Fin m) L) :
    (Fin m ⊕ Fin r) → MvPowerSeries (Fin m ⊕ Fin r) L :=
  Sum.elim (fun i ↦ MvPowerSeries.X (Sum.inl i))
    (fun j ↦ MvPowerSeries.rename Sum.inl (φ j) + MvPowerSeries.X (Sum.inr j))

/-- Substitution along the implicit graph, with values in L[[W]].
Source: steps 4--5 (blueprint: lem-trf-implicit-taylor-coordinate-calculus). -/
def implicitGraphVariables {m r : ℕ} {L : Type u} [Field L]
    (φ : Fin r → MvPowerSeries (Fin m) L) :
    (Fin m ⊕ Fin r) → MvPowerSeries (Fin m) L :=
  Sum.elim MvPowerSeries.X φ

/-- Extract the coefficient of Z^delta as a series in W.
Source: step 9 (blueprint: lem-trf-implicit-taylor-coordinate-calculus). -/
def implicitTransverseCoeff {m r : ℕ} {L : Type u} [Field L]
    (δ : Fin r →₀ ℕ) (f : MvPowerSeries (Fin m ⊕ Fin r) L) :
    MvPowerSeries (Fin m) L :=
  fun α ↦ MvPowerSeries.coeff
    (Finsupp.mapDomain Sum.inl α + Finsupp.mapDomain Sum.inr δ) f

/-- Iteration of the regular y-derivations, with the same list convention as iteratedPartial.
Source: steps 7 and 9 (blueprint: lem-trf-implicit-taylor-coordinate-calculus). -/
def implicitIteratedDerivative {m r : ℕ} {A : Type u} [CommRing A]
    (D : (Fin m ⊕ Fin r) → Derivation ℤ A A) (δ : Fin r →₀ ℕ) (f : A) : A :=
  (Finset.univ.toList.flatMap fun j : Fin r ↦ List.replicate (δ j) j).foldl
    (fun g j ↦ D (Sum.inr j) g) f

/-- Apply the straightening substitution coefficientwise to an arbitrary formal T-family.
This definition makes no finite-support assumption on the regular coefficients.
Source: step 10 (blueprint: lem-trf-implicit-taylor-coordinate-calculus). -/
def implicitShiftFamily {m r t : ℕ} {L : Type u} [Field L]
    (φ : Fin r → MvPowerSeries (Fin m) L)
    (F : MvPowerSeries (Fin t) (MvPowerSeries (Fin m ⊕ Fin r) L)) :
    MvPowerSeries (Fin t) (MvPowerSeries (Fin m ⊕ Fin r) L) :=
  fun γ ↦ MvPowerSeries.subst (implicitShiftVariables φ) (MvPowerSeries.coeff γ F)

/-- Pointwise conclusions at an arbitrary, possibly nonclosed, point of N.
The maps are uniquely characterized Taylor homomorphisms of the actual stalks.
Every displayed formula is about these maps and Mathlib's formal substitution.
Source: steps 3--14 (blueprint: lem-trf-implicit-taylor-coordinate-calculus). -/
structure ImplicitTaylorPoint {k : Type u} [Field k] [CharZero k]
    {B N : Scheme.{u}} {m r : ℕ}
    (c : MvPolynomial (Fin m ⊕ Fin r) k →+* Γ(B, ⊤))
    (h : Fin r → Γ(B, ⊤)) (D : ImplicitCoordinateDerivations B c)
    (j : N ⟶ B) (b : N) where
  deriv : (Fin m ⊕ Fin r) →
    Derivation ℤ (B.presheaf.stalk (j b)) (B.presheaf.stalk (j b))
  germ_partial : ∀ (U : B.Opens) (hb : j b ∈ U) (i : Fin m ⊕ Fin r) (f : Γ(B, U)),
    deriv i (B.presheaf.germ U (j b) hb f) =
      B.presheaf.germ U (j b) hb (D.deriv U i f)
  taylor : B.presheaf.stalk (j b) →+*
    MvPowerSeries (Fin m ⊕ Fin r) (N.residueField b)
  taylor_spec : isTaylorMap (implicitCoordinatesAt c (j b))
    ((j.stalkMap b) ≫ N.residue b).hom taylor
  taylor_unique : ∀ T : B.presheaf.stalk (j b) →+*
      MvPowerSeries (Fin m ⊕ Fin r) (N.residueField b),
    isTaylorMap (implicitCoordinatesAt c (j b)) ((j.stalkMap b) ≫ N.residue b).hom T →
      T = taylor
  taylorN : N.presheaf.stalk b →+* MvPowerSeries (Fin m) (N.residueField b)
  taylorN_spec : isTaylorMap
    ((j.stalkMap b).hom.comp
      ((implicitCoordinatesAt c (j b)).comp (MvPolynomial.rename Sum.inl).toRingHom))
    (N.residue b).hom taylorN
  taylorN_unique : ∀ T : N.presheaf.stalk b →+* MvPowerSeries (Fin m) (N.residueField b),
    isTaylorMap ((j.stalkMap b).hom.comp
      ((implicitCoordinatesAt c (j b)).comp (MvPolynomial.rename Sum.inl).toRingHom))
      (N.residue b).hom T → T = taylorN
  phi : Fin r → MvPowerSeries (Fin m) (N.residueField b)
  phi_zero : ∀ i : Fin r, MvPowerSeries.constantCoeff (phi i) = 0
  phi_value : ∀ i : Fin r,
    phi i = taylorN (j.stalkMap b (implicitCoordinatesAt c (j b)
      (MvPolynomial.X (Sum.inr i)))) - MvPowerSeries.C
        (((j.stalkMap b) ≫ N.residue b) (implicitCoordinatesAt c (j b)
          (MvPolynomial.X (Sum.inr i))))
  solution : ∀ i : Fin r,
    MvPowerSeries.subst (implicitGraphVariables phi)
      (taylor (B.presheaf.germ ⊤ (j b) (by trivial) (h i))) = 0
  unique_solution : ∀ ψ : Fin r → MvPowerSeries (Fin m) (N.residueField b),
    (∀ i : Fin r, MvPowerSeries.constantCoeff (ψ i) = 0) →
    (∀ i : Fin r, MvPowerSeries.subst (implicitGraphVariables ψ)
      (taylor (B.presheaf.germ ⊤ (j b) (by trivial) (h i))) = 0) → ψ = phi
  matrix : Matrix (Fin r) (Fin r) (MvPowerSeries (Fin m ⊕ Fin r) (N.residueField b))
  matrix_unit : IsUnit matrix
  factorization : ∀ i : Fin r,
    taylor (B.presheaf.germ ⊤ (j b) (by trivial) (h i)) =
      ∑ l : Fin r, matrix i l *
        (MvPowerSeries.X (Sum.inr l) - MvPowerSeries.rename Sum.inl (phi l))
  straight : MvPowerSeries (Fin m ⊕ Fin r) (N.residueField b) ≃ₐ[N.residueField b]
    MvPowerSeries (Fin m ⊕ Fin r) (N.residueField b)
  straight_apply : ∀ f : MvPowerSeries (Fin m ⊕ Fin r) (N.residueField b),
    straight f = MvPowerSeries.subst (implicitShiftVariables phi) f
  straight_inverse : ∀ f : MvPowerSeries (Fin m ⊕ Fin r) (N.residueField b),
    straight.symm f = MvPowerSeries.subst (implicitShiftVariables (-phi)) f
  continuous_straight : @Continuous _ _
    (@MvPowerSeries.WithPiTopology.instTopologicalSpace _ _ ⊥)
    (@MvPowerSeries.WithPiTopology.instTopologicalSpace _ _ ⊥) straight
  continuous_inverse : @Continuous _ _
    (@MvPowerSeries.WithPiTopology.instTopologicalSpace _ _ ⊥)
    (@MvPowerSeries.WithPiTopology.instTopologicalSpace _ _ ⊥) straight.symm
  ideal_of_N : RingHom.ker (j.stalkMap b).hom =
    Ideal.span (Set.range fun i : Fin r ↦ B.presheaf.germ ⊤ (j b) (by trivial) (h i))
  ideal_straight : Ideal.map straight.toRingEquiv.toRingHom
      (Ideal.map taylor (RingHom.ker (j.stalkMap b).hom)) =
    Ideal.span (Set.range fun i : Fin r ↦
      (MvPowerSeries.X (Sum.inr i) : MvPowerSeries (Fin m ⊕ Fin r) (N.residueField b)))
  restriction : ∀ f : B.presheaf.stalk (j b),
    MvPowerSeries.subst (implicitGraphVariables phi) (taylor f) =
      taylorN (j.stalkMap b f)
  derivative : ∀ (i : Fin m ⊕ Fin r) (f : B.presheaf.stalk (j b)),
    taylor (deriv i f) = MvPowerSeries.pderiv (N.residueField b) i (taylor f)
  coefficients : ∀ (t : ℕ) (f : (Fin t →₀ ℕ) → B.presheaf.stalk (j b))
      (γ : Fin t →₀ ℕ) (δ : Fin r →₀ ℕ),
    implicitTransverseCoeff δ
      (MvPowerSeries.coeff γ (implicitShiftFamily phi (fun η ↦ taylor (f η)))) =
    MvPowerSeries.C (((δ.prod fun _ n ↦ n.factorial : ℕ) : N.residueField b)⁻¹) *
      taylorN (j.stalkMap b (implicitIteratedDerivative deriv δ (f γ)))
  faithfullyFlat : taylor.FaithfullyFlat
  ideal_descent : ∀ I J : Ideal (B.presheaf.stalk (j b)), I.FG → J.FG →
    Ideal.map taylor I = Ideal.map taylor J → I = J
  /-- Every coefficient extension gives the unique ambient Taylor map over that field. -/
  extension_unique : ∀ (K : Type v) [Field K] (ι : N.residueField b →+* K)
      (T : B.presheaf.stalk (j b) →+* MvPowerSeries (Fin m ⊕ Fin r) K),
    (∀ f, MvPowerSeries.constantCoeff (T f) = ι (((j.stalkMap b) ≫ N.residue b) f)) →
    (∀ z : k, T (implicitCoordinatesAt c (j b) (MvPolynomial.C z)) =
      MvPowerSeries.C (ι (((j.stalkMap b) ≫ N.residue b)
        (implicitCoordinatesAt c (j b) (MvPolynomial.C z))))) →
    (∀ i : Fin m ⊕ Fin r, T (implicitCoordinatesAt c (j b) (MvPolynomial.X i)) =
      MvPowerSeries.C (ι (((j.stalkMap b) ≫ N.residue b)
        (implicitCoordinatesAt c (j b) (MvPolynomial.X i)))) + MvPowerSeries.X i) →
    T = (MvPowerSeries.map ι).comp taylor
  extension_taylorN_unique : ∀ (K : Type v) [Field K] (ι : N.residueField b →+* K)
      (T : N.presheaf.stalk b →+* MvPowerSeries (Fin m) K),
    (∀ f : N.presheaf.stalk b, MvPowerSeries.constantCoeff (T f) = ι (N.residue b f)) →
    (∀ z : k, T (j.stalkMap b (implicitCoordinatesAt c (j b) (MvPolynomial.C z))) =
      MvPowerSeries.C (ι (((j.stalkMap b) ≫ N.residue b)
        (implicitCoordinatesAt c (j b) (MvPolynomial.C z))))) →
    (∀ i : Fin m,
      T (j.stalkMap b (implicitCoordinatesAt c (j b) (MvPolynomial.X (Sum.inl i)))) =
        MvPowerSeries.C (ι (((j.stalkMap b) ≫ N.residue b)
          (implicitCoordinatesAt c (j b) (MvPolynomial.X (Sum.inl i))))) +
        MvPowerSeries.X i) →
    T = (MvPowerSeries.map ι).comp taylorN
  extension_matrix : ∀ (K : Type v) [Field K] (ι : N.residueField b →+* K),
    IsUnit (fun i l : Fin r ↦ MvPowerSeries.map ι (matrix i l) :
      Matrix (Fin r) (Fin r) (MvPowerSeries (Fin m ⊕ Fin r) K)) ∧
    ∀ i : Fin r,
      MvPowerSeries.map ι (taylor (B.presheaf.germ ⊤ (j b) (by trivial) (h i))) =
        ∑ l : Fin r, MvPowerSeries.map ι (matrix i l) *
          (MvPowerSeries.X (Sum.inr l) -
            MvPowerSeries.rename Sum.inl (MvPowerSeries.map ι (phi l)))
  extension_phi : ∀ (K : Type v) [Field K] (ι : N.residueField b →+* K),
    (∀ i : Fin r, MvPowerSeries.subst
      (implicitGraphVariables (fun l ↦ MvPowerSeries.map ι (phi l)))
      (MvPowerSeries.map ι (taylor (B.presheaf.germ ⊤ (j b) (by trivial) (h i)))) = 0) ∧
    (∀ ψ : Fin r → MvPowerSeries (Fin m) K,
      (∀ i : Fin r, MvPowerSeries.constantCoeff (ψ i) = 0) →
      (∀ i : Fin r, MvPowerSeries.subst (implicitGraphVariables ψ)
        (MvPowerSeries.map ι (taylor (B.presheaf.germ ⊤ (j b) (by trivial) (h i)))) = 0) →
      ψ = fun i ↦ MvPowerSeries.map ι (phi i))
  extension_substitution : ∀ (K : Type v) [Field K] (ι : N.residueField b →+* K)
      (f : MvPowerSeries (Fin m ⊕ Fin r) (N.residueField b)),
    MvPowerSeries.map ι (straight f) =
      MvPowerSeries.subst (implicitShiftVariables (fun i ↦ MvPowerSeries.map ι (phi i)))
        (MvPowerSeries.map ι f)
  extension_coefficients : ∀ (K : Type v) [Field K] (ι : N.residueField b →+* K)
      (f : B.presheaf.stalk (j b)) (δ : Fin r →₀ ℕ),
    implicitTransverseCoeff δ (MvPowerSeries.subst
      (implicitShiftVariables (fun i ↦ MvPowerSeries.map ι (phi i)))
      (MvPowerSeries.map ι (taylor f))) =
    MvPowerSeries.C (((δ.prod fun _ n ↦ n.factorial : ℕ) : K)⁻¹) *
      MvPowerSeries.map ι
        (taylorN (j.stalkMap b (implicitIteratedDerivative deriv δ f)))

/-- The full conclusions on the actual Jacobian open and its actual zero subscheme.
Source: steps 2--15 (blueprint: lem-trf-implicit-taylor-coordinate-calculus). -/
structure ImplicitTaylorCalculus {k : Type u} [Field k] [CharZero k]
    (B : Scheme.{u}) {m r : ℕ}
    (c : MvPolynomial (Fin m ⊕ Fin r) k →+* Γ(B, ⊤))
    (h : Fin r → Γ(B, ⊤)) (a : B) (D : ImplicitCoordinateDerivations B c) where
  center_in_open : a ∈ implicitJacobianOpen D h
  etale : Etale (implicitCoordinateMorphism (implicitTangentialCoordinates D h))
  smooth : Smooth (implicitZeroInclusion D h ≫ implicitStructureMorphism c)
  points : ∀ b : implicitZeroScheme D h,
    Nonempty (ImplicitTaylorPoint.{u, v} c h D (implicitZeroInclusion D h) b)
  coherent_ideal_neighbourhood : ∀ (I J : B.IdealSheafData) (x : B),
    Scheme.Modules.IsQuasiCoherentFiniteType I.toModules →
    Scheme.Modules.IsQuasiCoherentFiniteType J.toModules →
    (∀ f : B.presheaf.stalk x,
      (∃ (U : B.affineOpens) (hx : x ∈ U.1) (s : Γ(B, U.1)),
        s ∈ I.ideal U ∧ B.presheaf.germ U.1 x hx s = f) ↔
      (∃ (U : B.affineOpens) (hx : x ∈ U.1) (s : Γ(B, U.1)),
        s ∈ J.ideal U ∧ B.presheaf.germ U.1 x hx s = f)) →
    ∃ U : B.Opens, x ∈ U ∧ I.comap U.ι = J.comap U.ι

/-- Implicit transverse coordinates and the full regular coefficient calculus, on arbitrary
smooth finite-type schemes with specified etale coordinates in characteristic zero.

Source: ILO VIII 2.3.11 and 2.3.13; Bierstone--Milman, Invent. Math. 128 (1997),
Lemma 3.5 and Remarks 3.7, 9.9, 9.11
(blueprint: lem-trf-implicit-taylor-coordinate-calculus).

Proof (the fifteen DAG steps):
1. On each affine open, etaleness gives H_1=0 and relative Omega=0. Apply
[lem-trf-formally-etale-differentials-base-change] and the polynomial differential basis.
Dualize to regular coordinate derivations. Uniqueness glues them; their commutators vanish.
2. On the determinant open, (dw,dh) is a basis, by its invertible block triangular matrix.
The pointwise differential criterion [lem-pur-etale-at-point-from-differentials] makes (w,h)
etale. Its inverse image of A^m times zero is the defined N; base change makes w etale on N.
Affine space and etale morphisms are smooth, and smooth morphisms compose.
3. At b put L=kappa(b), C=A tensor_k L and J=ker(C -> L). The centered polynomial
chart gives P/(X)^n = C/J^n by [lem-sfb-augmented-etale-associated-graded]. Taking inverse
limits and localizing at J identifies the diagonal completion with L[[W,Y]]. This gives
the uniquely characterized Taylor maps on the stalks, including at nonclosed b.
4. Define phi as the centered Taylor expansion of y restricted to N. Unique square-zero
lifting through the successive (W)-power quotients identifies substitution with restriction.
5. Any other zero-constant solution factors through N. Unique lifting for the w chart of N,
followed by evaluation on the y coordinates, identifies it with phi at every truncation.
6. Substitution Y=phi+Z and its inverse Z=Y-phi fix W. Both preserve the variable ideal,
so define inverse continuous homomorphisms, as checked on every finite truncation.
7. Formal differentiation after Taylor expansion and regular differentiation before it are
derivations into the same module with the same coordinate values, hence equal. Iterate.
8. In h(W,phi+Z), allocate each nonzero monomial to its least positive Z index and divide
by that variable. This gives a matrix with constant term the invertible Jacobian. Its
geometric matrix series is an inverse. Undo substitution to obtain U and the ideal equality.
9. The binomial coefficient formula for the Z^delta coefficient is the derivative divided
by delta!. The order bound |alpha|+|beta|-|delta| makes every coefficient sum finite.
Steps 4 and 7 identify it with the Taylor expansion on N of the regular derivative.
10. Apply this separately to every T^gamma coefficient; substitution fixes T. Finitely many
variables make each bounded-degree truncation finite, without a finite-support assumption.
11. Infinitesimal lifting and its unique quotient maps commute with arbitrary field
extension. The monomial allocation, matrix inverse and binomial formulas do so coefficientwise.
12. The diagonal local map A_p -> (A tensor_k L)_J is flat and local, hence faithfully flat;
finite type over each field supplies Noetherianity. This includes nonclosed points.
13. The Noetherian local completion is faithfully flat. Compose with step 12 and the
coordinate identification in step 3 to obtain faithful flatness of the local Taylor map.
14. Faithfully flat ideal contraction reflects equality of extended finitely generated ideals.
15. Coherent ideals have finite generators locally. Equal stalks give one denominator for
each inclusion; their product gives a common open neighborhood of equality. Equivalently
apply [lem-weil-pbc-finite-type-module-support-closed] to the two quotient modules. -/
theorem implicitTaylorCoordinateCalculus {k : Type u} [Field k] [CharZero k]
    (B : Scheme.{u}) {m r : ℕ}
    (c : MvPolynomial (Fin m ⊕ Fin r) k →+* Γ(B, ⊤))
    (hc : Etale (implicitCoordinateMorphism c))
    (hs : Smooth (implicitStructureMorphism c))
    (hft : LocallyOfFiniteType (implicitStructureMorphism c) ∧
      QuasiCompact (implicitStructureMorphism c)) :
    ∃ D : ImplicitCoordinateDerivations B c,
      (∀ x : B, ∃ T : B.presheaf.stalk x →+*
          MvPowerSeries (Fin m ⊕ Fin r) (B.residueField x),
        isTaylorMap (implicitCoordinatesAt c x) (B.residue x).hom T ∧
        (∀ T' : B.presheaf.stalk x →+*
            MvPowerSeries (Fin m ⊕ Fin r) (B.residueField x),
          isTaylorMap (implicitCoordinatesAt c x) (B.residue x).hom T' → T' = T) ∧
        T.FaithfullyFlat ∧
        ∀ I J : Ideal (B.presheaf.stalk x), I.FG → J.FG →
          Ideal.map T I = Ideal.map T J → I = J) ∧
      ∀ (h : Fin r → Γ(B, ⊤)) (a : B),
        (∀ i : Fin r, B.Γevaluation a (h i) = 0) →
        B.Γevaluation a (implicitJacobian D h) ≠ 0 →
        Nonempty (ImplicitTaylorCalculus.{u, v} B c h a D) := by
  sorry

end AlgebraicGeometry.HilbertCoefficient
