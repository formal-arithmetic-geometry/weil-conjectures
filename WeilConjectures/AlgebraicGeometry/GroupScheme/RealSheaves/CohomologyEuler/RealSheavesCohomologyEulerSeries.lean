/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.RealSheaves.Setup.RealSheavesSetup
public import WeilConjectures.SmoothPurity.GlobalGeometricFrobenius.CondensedGlobalGeometricFrobenius
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ConstantWeil.CondensedConstantWeilTwist
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedDerived.CondensedScalarDerivedLocalFrobenius
public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.PointCount
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Trunc
import WeilConjectures.WeilObject.Sheaf.StalkFiniteFree
import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-! # Cohomology and the Euler series of constructible Weil complexes

Source: latest blueprint,
`sec-purity-real-sheaves/sk-prop-wrp-h1-no-fixed/d-real-cohom.md`
(blueprint: d-real-cohom). Cohomology reuses the recorded condensed coefficient functors.
The local determinant is computed on the actual cohomology-sheaf stalk, with its canonical
local Frobenius. The Euler series is constructed coefficient by coefficient using finite
sets of closed points of bounded degree. No convergence assumption is an input.
The constructions work for finite-type schemes; in this chapter they are applied to the
curves of RealSheaves.Setup.IsCurve. The chosen closure is represented by PadicAlgCl.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace RealSheaves.CohomologyEuler

open WeilConjectures WeilConjectures.NativeCondensedModule

/-- The chapter's chosen embedding on the standard model of its chosen algebraic closure.
The algebraic-closure equivalence is over Q_l and imposes no continuity condition.
Source: d-real-cohom, setup convention (blueprint: d-real-cohom). -/
def setupEmbedding (S : RealSheaves.Setup.{u, v}) : PadicAlgCl S.l →+* ℂ :=
  S.iota.comp (IsAlgClosure.equiv ℚ_[S.l] (PadicAlgCl S.l) S.Qbar).toRingHom

variable (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- The existing category of strict Weil complexes; derived Weil complexes enter via
weilComplexRealization. Source: d-real-cohom, Weil-complex clause (blueprint: d-real-cohom). -/
abbrev Complex := condensedStrictWeilComplex (Profinite.padicAlgClRingObj ell)
  (D.geometricFrobenius X₀).hom

/-- Ordinary abelian-sheaf cohomology is the recorded etale derived global-sections
functor on the sheaf placed in degree zero. Source: first sentence (blueprint: d-real-cohom). -/
abbrev abelianSheafCohomology (X : Scheme.{u})
    (A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (i : ℤ) :=
  (Etale.cohomology AddCommGrpCat.{u + 1} X i).obj
    ((DerivedCategory.singleFunctor _ 0).obj A)

/-- The existing ordinary or compact condensed coefficient complex.
Source: cohomology display (blueprint: d-real-cohom). -/
def coefficientComplex (c : Compactification (D.geometricFiber X₀).hom) (compact : Bool) :=
  if compact then condensedRingCompactCoefficientComplex (Profinite.padicAlgClRingObj ell) c
  else condensedRingOrdinaryCoefficientComplex (Profinite.padicAlgClRingObj ell)
    (D.geometricFiber X₀).hom

/-- The two cohomology groups with canonical scalar action, in every integer degree.
Exact restriction of scalars commutes with homology; at the point this is Fib_s.
Source: first display (blueprint: d-real-cohom). -/
def cohomology (c : Compactification (D.geometricFiber X₀).hom) (compact : Bool)
    (K : Complex D ell X₀) (i : ℤ) :
    ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl ell)) :=
  (ModuleCat.restrictScalars.{u + 1}
    ((Profinite.PadicAlgCl.constRingHom ell).comp
      (ULift.ringEquiv : ULift.{u + 1} (PadicAlgCl ell) ≃+* PadicAlgCl ell).toRingHom)).obj
    ((NativeCondensedDerived.cohomology (Profinite.padicAlgClRingObj ell) i).obj
      ((coefficientComplex D ell X₀ c compact).obj K.obj.carrier))

/-- Scalar restriction preserves a zero coefficient cohomology object.
Source: d-real-cohom, the exact scalar realization in the cohomology display
(blueprint: d-real-cohom).
Proof: apply the restriction-of-scalars functor to the zero object. -/
theorem cohomology_isZero (c : Compactification (D.geometricFiber X₀).hom)
    (compact : Bool) (K : Complex D ell X₀) (r : ℤ)
    (h : IsZero ((NativeCondensedDerived.cohomology (Profinite.padicAlgClRingObj ell) r).obj
      ((coefficientComplex D ell X₀ c compact).obj K.obj.carrier))) :
    IsZero (cohomology D ell X₀ c compact K r) :=
  (ModuleCat.restrictScalars _).map_isZero h

/-- The finite-dimensionality and bounded support asserted by the definition.
Source: d-real-cohom, finiteness sentence (blueprint: d-real-cohom).
Proof: the geometric structure map is separated of finite type; the algebraically closed
base has ell-cohomological dimension zero. Six-functor constructibility stability puts
both direct images in Dbc of the point. The exact point equivalence gives finite-dimensional
cohomology in a bounded interval, and scalar restriction along the scalar-ring isomorphism
preserves these assertions. This applies to complexes in arbitrary degrees, including zero. -/
theorem cohomology_finite [IsSeparated X₀.hom] (hEll : ell ≠ D.p)
    (c : Compactification (D.geometricFiber X₀).hom) (K : Complex D ell X₀) :
    (∀ (compact : Bool) (i : ℤ),
      FiniteDimensional (ULift.{u + 1} (PadicAlgCl ell))
        (cohomology D ell X₀ c compact K i)) ∧
    ∃ a b : ℤ, ∀ (compact : Bool) (i : ℤ), i < a ∨ b < i →
      IsZero (cohomology D ell X₀ c compact K i) := by
  sorry

/-- The existing global geometric Frobenius on the selected coefficient complex.
Source: d-real-cohom, Frobenius sentence (blueprint: d-real-cohom). -/
def frobenius [IsSeparated X₀.hom] (hEll : ell ≠ D.p)
    (c : Compactification (D.geometricFiber X₀).hom) (K : Complex D ell X₀)
    (compact : Bool) :
    End ((coefficientComplex D ell X₀ c compact).obj K.obj.carrier) := by
  let pair := GlobalGeometricFrobenius.globalGeometricFrobenius D ell hEll X₀ .qbar c K
  cases compact with
  | false => exact pair.1
  | true => exact pair.2

/-- Frobenius on each scalar-valued cohomology group, by homology and scalar restriction.
Source: d-real-cohom, Frobenius sentence (blueprint: d-real-cohom). -/
def frobeniusOnCohomology [IsSeparated X₀.hom] (hEll : ell ≠ D.p)
    (c : Compactification (D.geometricFiber X₀).hom) (K : Complex D ell X₀)
    (compact : Bool) (i : ℤ) :
    (cohomology D ell X₀ c compact K i ⟶ cohomology D ell X₀ c compact K i) :=
  (ModuleCat.restrictScalars.{u + 1}
    ((Profinite.PadicAlgCl.constRingHom ell).comp
      (ULift.ringEquiv : ULift.{u + 1} (PadicAlgCl ell) ≃+* PadicAlgCl ell).toRingHom)).map
    ((NativeCondensedDerived.cohomology (Profinite.padicAlgClRingObj ell) i).map
      (frobenius D ell X₀ hEll c K compact))

/-- The Tate line is the recorded constant Weil line with scalar q^(-n).
Source: d-real-cohom, Tate convention and sk-d-real-operations (blueprint: d-real-cohom). -/
def tateLine [IsSeparated X₀.hom] (hEll : ell ≠ D.p) (n : ℤ) :=
  ConstantWeil.line ell D X₀ hEll
    ((Units.mk0 (D.q : PadicAlgCl ell)
      (Nat.cast_ne_zero.mpr
        (D.cardinality_eq.symm ▸ pow_ne_zero D.a D.prime.ne_zero))) ^ (-n))

/-- The Weil structure on a cohomology sheaf uses the canonical exact-functor comparison.
Source: d-real-cohom, local-factor display (blueprint: d-real-cohom). -/
def cohomologyPair (K : Complex D ell X₀) (j : ℤ) :
    condensedWeilModules (Profinite.padicAlgClRingObj ell) (D.geometricFrobenius X₀).hom :=
  CategoryTheory.Endofunctor.IsoAlgebra.mk
    ((DerivedCategory.homologyFunctor _ j).obj K.obj.carrier)
    (((upperStar (Profinite.padicAlgClRingObj ell) (D.geometricFrobenius X₀).hom)
    |>.mapDerivedCategoryHomologyFunctorIso j).app K.obj.carrier ≪≫
        (DerivedCategory.homologyFunctor _ j).mapIso K.obj.str)

/-- The exact finite support of cohomology sheaves, independent of a choice of bounds.
Source: d-real-cohom, finite alternating product (blueprint: d-real-cohom).
Proof: K belongs to Dbc, so its cohomology vanishes outside a finite integer interval.
The displayed support is a subset of that interval and hence finite. -/
theorem finite_cohomology_support (K : Complex D ell X₀) :
    Set.Finite {j : ℤ | ¬ IsZero ((cohomologyPair D ell X₀ K j).carrier)} := by
  obtain ⟨⟨a, b, h⟩, _⟩ := (mem_boundedConstructible_iff _ _).mp K.property
  apply (Set.finite_Icc a b).subset
  intro j hj
  change a ≤ j ∧ j ≤ b
  by_contra hnot
  exact hj (h j (by omega))

/-- The finite set of precisely the nonzero cohomological degrees.
Source: d-real-cohom, finite alternating product (blueprint: d-real-cohom). -/
def cohomologySupport (K : Complex D ell X₀) : Finset ℤ :=
  (finite_cohomology_support D ell X₀ K).toFinset

/-- The actual scalar stalk of the j-th cohomology sheaf at a chosen geometric lift.
Source: d-real-cohom, H^j(K)_xbar (blueprint: d-real-cohom). -/
abbrev stalk (K : Complex D ell X₀) (j : ℤ)
    (x : closedPoints X₀.left) (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k) :=
  NativeCondensedModule.fibre ell D (cohomologyPair D ell X₀ K j).carrier
    (localClosedPoint D X₀ x i hi)

private theorem finiteDimensional_sections_of_free
    (R : Type u) [Field R] {C : Type v} [Category.{w} C] [Preadditive C]
    [HasFiniteBiproducts C] (F : C ⥤ ModuleCat.{u} R) [F.Additive]
    (U M : C) (hU : F.obj U ≅ ModuleCat.of R R) (r : ℕ)
    (e : M ≅ ⨁ fun _ : Fin r ↦ U) : FiniteDimensional R (F.obj M) := by
  let eq : F.obj M ≅ ModuleCat.of R (Fin r → R) :=
    F.mapIso e ≪≫ F.mapBiproduct _ ≪≫
      biproduct.mapIso (fun _ ↦ hU) ≪≫ ModuleCat.biproductIsoPi _
  exact LinearEquiv.finiteDimensional eq.toLinearEquiv.symm

private theorem finiteDimensional_constructible_sections
    (l : ℕ) [Fact l.Prime] (k : Type u) [Field k] [IsSepClosed k]
    {T : Scheme.{u}} (M : NativeCondensedModule.Modules l T)
    (hM : IsConstructibleModuleObject (condensedRingObj (Profinite.padicAlgClRingObj l) T) M)
    (z : Spec (.of k) ⟶ T) :
    FiniteDimensional (ULift.{u + 1} (PadicAlgCl l))
      ((NativeCondensedModule.pointSections l k).obj
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).obj M)) := by
  obtain ⟨n, m, f, ⟨e⟩⟩ :=
    CondensedRing.isFinitelyPresented_upperStar_of_isConstructibleModuleObject
      (Profinite.padicAlgClRingObj l) (Field.toIsField k)
      IsField.isSepClosed_toField hM z
  obtain ⟨r, ⟨er⟩⟩ := exists_iso_biproduct_cokernel
    (CondensedRing.isIso_of_ne_zero_end_tensorUnit l (Field.toIsField k)
      IsField.isSepClosed_toField) (Iso.refl _) (Iso.refl _) f
  let F := NativeCondensedModule.pointSections l k
  have : F.Additive := by
    dsimp [F, NativeCondensedModule.pointSections]
    infer_instance
  exact finiteDimensional_sections_of_free _ F _ _
    (NativeCondensedModule.pointSectionsUnitIso l k).symm r (e ≪≫ er)

/-- Constructible stalks are finite dimensional, in every degree and at every geometric lift.
Source: d-real-cohom, local-factor paragraph (blueprint: d-real-cohom).
Proof: pull back a finite constant local model of the constructible cohomology sheaf.
A cover of the algebraically closed point splits; exact scalar evaluation identifies the
stalk with its finite-dimensional constant fibre. The zero-rank model is included. -/
theorem stalk_finite (K : Complex D ell X₀) (j : ℤ)
    (x : closedPoints X₀.left) (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k) :
    FiniteDimensional (ULift.{u + 1} (PadicAlgCl ell)) (stalk D ell X₀ K j x i hi) := by
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  exact finiteDimensional_constructible_sections ell D.k
    (cohomologyPair D ell X₀ K j).carrier (K.property.2 j)
    (localClosedPoint D X₀ x i hi)

/-- The ordinary reverse characteristic polynomial of the canonical local return operator.
Source: d-real-cohom, local determinant convention (blueprint: d-real-cohom). -/
def localPolynomial (K : Complex D ell X₀) (j : ℤ)
    (x : closedPoints X₀.left) (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k) :
    Polynomial (ULift.{u + 1} (PadicAlgCl ell)) :=
  letI := stalk_finite D ell X₀ K j x i hi
  let M := cohomologyPair D ell X₀ K j
  (NativeCondensedModule.operator ell D (D.geometricFrobenius X₀).hom M.carrier M.str
    (localClosedPoint D X₀ x i hi) (localClosedPointDegree D X₀ x - 1)
    (localClosedPoint_return D X₀ x i hi)).hom.charpolyRev

/-- The local rational function, read as its regular formal series at zero. Negative
cohomological degrees use the same parity convention. Source: d-real-cohom, alternating
local-factor display (blueprint: d-real-cohom). -/
def localSeries (K : Complex D ell X₀) (ι : PadicAlgCl ell →+* ℂ)
    (x : closedPoints X₀.left) (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k) :
    PowerSeries ℂ :=
  ∏ j ∈ cohomologySupport D ell X₀ K,
    let P : PowerSeries ℂ := (localPolynomial D ell X₀ K j x i hi).map
      (ι.comp (ULift.ringEquiv : ULift.{u + 1} (PadicAlgCl ell) ≃+* PadicAlgCl ell).toRingHom)
    if Even j then P else P⁻¹

/-- The local factor is independent of the auxiliary residue-field embedding.
Source: d-real-cohom, P_x depends on x (blueprint: d-real-cohom).
Proof: two geometric lifts over x differ by a residue-field Galois transport. Naturality
of the Weil return isomorphism conjugates their operators. Reverse characteristic
polynomials are invariant under conjugacy, as is their finite alternating product. -/
theorem localSeries_independent (K : Complex D ell X₀) (ι : PadicAlgCl ell →+* ℂ)
    (x : closedPoints X₀.left) (i i' : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
    (hi' : i'.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k) :
    localSeries D ell X₀ K ι x i hi = localSeries D ell X₀ K ι x i' hi' := by
  sorry

/-- The alternating determinant is a rational function regular and equal to one at zero.
Source: d-real-cohom, rational-function clause (blueprint: d-real-cohom).
Proof: multiply the even-degree determinant polynomials into A and the odd-degree ones
into B. Both finite products have constant coefficient one. Each polynomial is a unit
in the power-series ring, so cancellation of their inverses gives localSeries * B = A. -/
theorem localSeries_rational (K : Complex D ell X₀) (ι : PadicAlgCl ell →+* ℂ)
    (x : closedPoints X₀.left) (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k) :
    ∃ A B : Polynomial ℂ, A.coeff 0 = 1 ∧ B.coeff 0 = 1 ∧
      localSeries D ell X₀ K ι x i hi * (B : PowerSeries ℂ) = (A : PowerSeries ℂ) := by
  classical
  let f : ℤ → Polynomial ℂ := fun j ↦ (localPolynomial D ell X₀ K j x i hi).map
    (ι.comp (ULift.ringEquiv : ULift.{u + 1} (PadicAlgCl ell) ≃+* PadicAlgCl ell).toRingHom)
  have hf (j : ℤ) : (f j).coeff 0 = 1 := by
    simp [f, localPolynomial]
  change ∃ A B : Polynomial ℂ, A.coeff 0 = 1 ∧ B.coeff 0 = 1 ∧
    (∏ j ∈ cohomologySupport D ell X₀ K,
      if Even j then (f j : PowerSeries ℂ) else (f j : PowerSeries ℂ)⁻¹) *
        (B : PowerSeries ℂ) = (A : PowerSeries ℂ)
  generalize cohomologySupport D ell X₀ K = s
  induction s using Finset.induction_on with
  | empty => exact ⟨1, 1, by simp⟩
  | @insert j s hj ih =>
    obtain ⟨A, B, hA, hB, hAB⟩ := ih
    by_cases he : Even j
    · refine ⟨f j * A, B, by simp [Polynomial.coeff_mul, hf, hA], hB, ?_⟩
      simp only [Finset.prod_insert hj, if_pos he, Polynomial.coe_mul]
      rw [mul_assoc, hAB]
    · refine ⟨A, f j * B, hA, by simp [Polynomial.coeff_mul, hf, hB], ?_⟩
      simp only [Finset.prod_insert hj, if_neg he, Polynomial.coe_mul]
      calc
        (f j : PowerSeries ℂ)⁻¹ *
            (∏ k ∈ s, if Even k then (f k : PowerSeries ℂ) else (f k : PowerSeries ℂ)⁻¹) *
            ((f j : PowerSeries ℂ) * (B : PowerSeries ℂ)) =
          ((f j : PowerSeries ℂ)⁻¹ * (f j : PowerSeries ℂ)) *
            ((∏ k ∈ s, if Even k then (f k : PowerSeries ℂ)
              else (f k : PowerSeries ℂ)⁻¹) * (B : PowerSeries ℂ)) := by ring
        _ = (A : PowerSeries ℂ) := by
          rw [PowerSeries.inv_mul_cancel _ (by simp [hf]), one_mul, hAB]

/-- For positive e, substitution U = T^e by coefficients; only multiples of e contribute.
Source: d-real-cohom, Euler-series display (blueprint: d-real-cohom). -/
def substituteDegree (P : PowerSeries ℂ) (e : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun m ↦ if e ∣ m then PowerSeries.coeff (m / e) P else 0

/-- The closed points of bounded degree form a finite set.
Source: d-real-cohom, locally finite product paragraph (blueprint: d-real-cohom).
Proof: finite residue fields are precisely closed points for a finite-type scheme over
F_q. The recorded bounded-degree point-count theorem gives finiteness of this subset. -/
theorem finite_bounded_points (m : ℕ) :
    Set.Finite {x : closedPoints X₀.left | localClosedPointDegree D X₀ x ≤ m} := by
  have h := X₀.hom.finite_setOf_degreeOver_le m
  rw [X₀.hom.finitePoints_eq_closedPoints] at h
  exact h

/-- The coefficientwise locally finite Euler product. All geometric lifts are explicit
choices, as in the recorded local Frobenius construction. Source: d-real-cohom, final
display and concrete coefficient formula (blueprint: d-real-cohom). -/
def eulerSeries (K : Complex D ell X₀) (ι : PadicAlgCl ell →+* ℂ)
    (i : ∀ x : closedPoints X₀.left, X₀.left.residueField x.val →+* D.k)
    (hi : ∀ x, (i x).comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k) :
    PowerSeries ℂ :=
  PowerSeries.mk fun m ↦ PowerSeries.coeff m
    (∏ x ∈ (finite_bounded_points D X₀ m).toFinset,
      (substituteDegree (localSeries D ell X₀ K ι x (i x) (hi x))
        (localClosedPointDegree D X₀ x))⁻¹)

/-- The local factor is a unit normalized at the origin, and the Euler product has
constant coefficient one. Source: d-real-cohom, normalization clauses
(blueprint: d-real-cohom).
Proof: each reverse characteristic polynomial has constant coefficient one. Inverting
and multiplying finitely many such series preserves one. Closed-point degrees are
positive, so substitution preserves the constant coefficient. The finite degree-zero
product defining the Euler coefficient therefore has constant coefficient one. -/
theorem constantCoefficients (K : Complex D ell X₀) (ι : PadicAlgCl ell →+* ℂ)
    (i : ∀ x : closedPoints X₀.left, X₀.left.residueField x.val →+* D.k)
    (hi : ∀ x, (i x).comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k) :
    (∀ x, PowerSeries.constantCoeff (localSeries D ell X₀ K ι x (i x) (hi x)) = 1) ∧
    PowerSeries.constantCoeff (eulerSeries D ell X₀ K ι i hi) = 1 := by
  classical
  have hlocal (x : closedPoints X₀.left) :
      PowerSeries.constantCoeff (localSeries D ell X₀ K ι x (i x) (hi x)) = 1 := by
    unfold localSeries
    rw [map_prod]
    apply Finset.prod_eq_one
    intro j _
    have hp : PowerSeries.constantCoeff
        (((localPolynomial D ell X₀ K j x (i x) (hi x)).map (ι.comp
          (ULift.ringEquiv : ULift.{u + 1} (PadicAlgCl ell) ≃+* PadicAlgCl ell).toRingHom)) :
          PowerSeries ℂ) = 1 := by
      rw [Polynomial.constantCoeff_coe, Polynomial.coeff_map]
      simp [localPolynomial]
    split_ifs <;> simp only [PowerSeries.constantCoeff_inv, hp, inv_one]
  refine ⟨hlocal, ?_⟩
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp only [eulerSeries, PowerSeries.coeff_mk, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    map_prod, PowerSeries.constantCoeff_inv]
  apply Finset.prod_eq_one
  intro x _
  simp [substituteDegree, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, hlocal]

/-- Enlarging the finite cutoff cannot change a coefficient already computed.
Source: d-real-cohom, final stability sentence (blueprint: d-real-cohom).
Proof: a local factor and its inverse are one modulo T^e. For e>m they cannot affect
coefficients through m. Separate the larger finite product into points of degree at
most m and those of larger degree; every extra factor is one modulo T^(m+1). -/
theorem coefficient_stable (K : Complex D ell X₀) (ι : PadicAlgCl ell →+* ℂ)
    (i : ∀ x : closedPoints X₀.left, X₀.left.residueField x.val →+* D.k)
    (hi : ∀ x, (i x).comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
    (m N : ℕ) (hmN : m ≤ N) :
    PowerSeries.coeff m (eulerSeries D ell X₀ K ι i hi) =
      PowerSeries.coeff m
        (∏ x ∈ (finite_bounded_points D X₀ N).toFinset,
          (substituteDegree (localSeries D ell X₀ K ι x (i x) (hi x))
            (localClosedPointDegree D X₀ x))⁻¹) := by
  classical
  let s := (finite_bounded_points D X₀ m).toFinset
  let t := (finite_bounded_points D X₀ N).toFinset
  let f : closedPoints X₀.left → PowerSeries ℂ := fun x ↦
    (substituteDegree (localSeries D ell X₀ K ι x (i x) (hi x))
      (localClosedPointDegree D X₀ x))⁻¹
  have hst : s ⊆ t := by
    intro x hx
    simp only [s, t, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hx ⊢
    exact hx.trans hmN
  have hfactor (x : closedPoints X₀.left) :
      PowerSeries.trunc (m + 1) (f x) =
        PowerSeries.trunc (m + 1) (if x ∈ s then f x else 1) := by
    by_cases hx : x ∈ s
    · rw [if_pos hx]
    rw [if_neg hx, PowerSeries.trunc_one]
    have hdegree : m < localClosedPointDegree D X₀ x := by
      simpa only [s, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_le] using hx
    let P := substituteDegree (localSeries D ell X₀ K ι x (i x) (hi x))
      (localClosedPointDegree D X₀ x)
    have hc : PowerSeries.constantCoeff P = 1 := by
      change PowerSeries.constantCoeff (PowerSeries.mk _) = 1
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
      simpa using (constantCoefficients D ell X₀ K ι i hi).1 x
    have hp : PowerSeries.trunc (m + 1) P = 1 := by
      ext r
      rw [PowerSeries.coeff_trunc]
      by_cases hr : r < m + 1
      · rw [if_pos hr]
        by_cases hzero : r = 0
        · subst r
          simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply,
            Polynomial.coeff_one_zero] using hc
        · have hdiv : ¬ localClosedPointDegree D X₀ x ∣ r := by
            intro hd
            have := Nat.le_of_dvd (Nat.pos_of_ne_zero hzero) hd
            omega
          simp [P, substituteDegree, hdiv, Polynomial.coeff_one, hzero]
      · simp only [if_neg hr, Polynomial.coeff_one]
        have : r ≠ 0 := by omega
        simp [this]
    have hinv := congrArg (PowerSeries.trunc (m + 1))
      (PowerSeries.mul_inv_cancel P (by rw [hc]; exact one_ne_zero))
    rw [← PowerSeries.trunc_trunc_mul, hp, Polynomial.coe_one, one_mul,
      PowerSeries.trunc_one] at hinv
    exact hinv
  have hprod (r : Finset (closedPoints X₀.left)) :
      PowerSeries.trunc (m + 1) (∏ x ∈ r, f x) =
        PowerSeries.trunc (m + 1) (∏ x ∈ r, if x ∈ s then f x else 1) := by
    induction r using Finset.induction_on with
    | empty => rfl
    | @insert x r hx ih =>
      simp only [Finset.prod_insert hx]
      rw [← PowerSeries.trunc_trunc_mul_trunc, hfactor, ih,
        PowerSeries.trunc_trunc_mul_trunc]
  have hfilter : (∏ x ∈ t, if x ∈ s then f x else 1) = ∏ x ∈ s, f x := by
    calc
      _ = ∏ x ∈ s, if x ∈ s then f x else 1 :=
        (Finset.prod_subset hst (fun x _ hx ↦ if_neg hx)).symm
      _ = _ := Finset.prod_congr rfl (fun x hx ↦ if_pos hx)
  have htrunc : PowerSeries.trunc (m + 1) (∏ x ∈ t, f x) =
      PowerSeries.trunc (m + 1) (∏ x ∈ s, f x) := by rw [hprod, hfilter]
  have hcoeff := congrArg (fun P : Polynomial ℂ ↦ P.coeff m) htrunc
  simp only [PowerSeries.coeff_trunc, Nat.lt_succ_self, if_true] at hcoeff
  simpa only [eulerSeries, PowerSeries.coeff_mk] using hcoeff.symm

end RealSheaves.CohomologyEuler
