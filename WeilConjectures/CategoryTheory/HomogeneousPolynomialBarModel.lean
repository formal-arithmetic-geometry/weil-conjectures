/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.PolynomialDerivedBarComparison
public import WeilConjectures.CategoryTheory.CondensedHomogeneousFunctionsInjective
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleIhom
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleDevissageSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageSingleBound
public import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageSingleConstructible
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

/-! # Homogeneous polynomial and function bar models

Source: latest blueprint, six-functors basics, direct-images proof paragraph (3),
agent-formulated polynomial evaluation sub-obligation
(blueprint: def-sfb-homogeneous-polynomial-bar-model).

These are specifications, with actual internal coproducts and internal Hom objects.
Every action and map is pinned on local generators or all slice evaluations.
No object is selected from an existence theorem. Natural-number complexes are
extended by zero to integer degrees by the standard embedding when used as K and R.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CondensedBar

namespace Profinite.CondensedAction.HomogeneousPolynomialBar

/-- Alternating deletion, as a finite integer polynomial substitution.
Source: direct-images paragraph (3), polynomial evaluation sub-obligation
(blueprint: def-sfb-homogeneous-polynomial-bar-model). -/
def deletionPolynomial (r n : ℕ) (q : MvPolynomial (Fin (n + 1) × Fin r) ℤ) :
    MvPolynomial (Fin (n + 2) × Fin r) ℤ :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
    MvPolynomial.rename (fun v ↦ (i.succAbove v.1, v.2)) q

/-- Consecutive differences in the homogeneous coordinates, with integer coefficients.
Source: direct-images paragraph (3), polynomial evaluation sub-obligation
(blueprint: def-sfb-homogeneous-polynomial-bar-model). -/
def differencePolynomial (r n : ℕ) (q : MvPolynomial (Fin n × Fin r) ℤ) :
    MvPolynomial (Fin (n + 1) × Fin r) ℤ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun v ↦ MvPolynomial.X (v.1.succ, v.2) - MvPolynomial.X (v.1.castSucc, v.2)) q

/-- Prefix sums starting at zero; the lattice's multiplication denotes addition.
Source: direct-images paragraph (3), polynomial evaluation sub-obligation
(blueprint: def-sfb-homogeneous-polynomial-bar-model). -/
def prefixTuple {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    {n : ℕ} {T : Profinite.{u}} (g : Fin n → C(T, G)) : Fin (n + 1) → C(T, G) :=
  fun i ↦ ∏ j ∈ Finset.univ.filter (fun j : Fin n ↦ j.val < i.val), g j

variable (ell : ℕ) [Fact ell.Prime] (F : Type u) [NormedField F]
  [NormedAlgebra ℚ_[ell] F] (r : ℕ)

/-- Translate every homogeneous block by the same varying lattice section.
Source: direct-images paragraph (3), polynomial evaluation sub-obligation
(blueprint: def-sfb-homogeneous-polynomial-bar-model). -/
def translatedMonomial (n : ℕ) (S : Profinite.{u})
    (g : C(S, LadicLattice.Lattice.{u} ell r)) (m : PolynomialBar.Monomial r (n + 1)) :
    MvPolynomial (Fin (n + 1) × Fin r) C(S, F) :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun v ↦ MvPolynomial.X v - MvPolynomial.C
      (⟨fun s ↦ algebraMap ℚ_[ell] F ((g s).toAdd.down v.2 : ℚ_[ell]),
        by fun_prop⟩ : C(S, F))) (MvPolynomial.monomial m 1)

/-- The actual monomial coproduct with its prescribed internal translation and deletion.
The section action is specified on every coefficient section, so locally finite sheaf
sections are retained. Source: direct-images paragraph (3), polynomial evaluation input
(blueprint: def-sfb-homogeneous-polynomial-bar-model). -/
structure PolynomialComplex where
  cochain : CochainComplex
    (CategoryTheory.CondensedBar.Equivariant (continuousScalarRing F)
      (LadicLattice.Lattice.{u} ell r)) ℕ
  ι : ∀ n : ℕ, PolynomialBar.Monomial r (n + 1) →
    (Mod.regular (continuousScalarRing F).X ⟶ (cochain.X n).module)
  isColimit : ∀ n : ℕ, IsColimit (Cofan.mk (cochain.X n).module (ι n))
  translation : ∀ (n : ℕ) (S : Profinite.{u})
    (g : C(S, LadicLattice.Lattice.{u} ell r)) (m : PolynomialBar.Monomial r (n + 1))
    (c : ULift.{u + 1} C(S, F)),
    (cochain.X n).act S g (((ι n m).hom.hom.app (op S)) c) =
      ∑ d ∈ (translatedMonomial ell F r n S g m).support,
        ((ι n d).hom.hom.app (op S))
          (ULift.up ((translatedMonomial ell F r n S g m).coeff d) * c)
  differential : ∀ (n : ℕ) (m : PolynomialBar.Monomial r (n + 1)),
    ι n m ≫ (cochain.d n (n + 1)).val =
      PolynomialBar.polynomialArrow (continuousScalarRing F) r (n + 2)
        (cochain.X (n + 1)).module (ι (n + 1))
        (deletionPolynomial r n (MvPolynomial.monomial m 1))

/-- The underlying internal-module complex of the homogeneous polynomial action complex.
Source: direct-images paragraph (3), polynomial evaluation sub-obligation
(blueprint: def-sfb-homogeneous-polynomial-bar-model). -/
def PolynomialComplex.underlying (K : PolynomialComplex ell F r) :=
  (Profinite.CondensedAction.forgetAction.mapHomologicalComplex (.up ℕ)).obj K.cochain

/-- Read the recorded homogeneous internal-Hom model on every profinite slice.
Source: direct-images paragraph (3), polynomial evaluation sub-obligation
(blueprint: def-sfb-homogeneous-polynomial-bar-model). -/
def evaluateModel (n : ℕ)
    (H : HomogeneousFunctions (continuousScalarRing F).toMon
      (LadicLattice.Lattice.{u} ell r) (PolynomialBar.trivialScalar ell F r) n)
    (S : Profinite.{u}) (c : sections (continuousScalarRing F) H.object.module S)
    (T : Profinite.{u}) (f : T ⟶ S)
    (x : Fin (n + 1) → C(T, LadicLattice.Lattice.{u} ell r)) :=
  homogeneousEvaluate (continuousScalarRing F).toMon (LadicLattice.Lattice.{u} ell r)
    (PolynomialBar.trivialScalar ell F r) n S ((H.internalHom.hom.val.app (op S)).hom c)
    T f x

/-- A homogeneous function complex uses exactly the recorded internal Hom and action.
Its differential is specified on every slice by alternating coordinate deletion.
Source: direct-images paragraph (3), polynomial evaluation sub-obligation
(blueprint: def-sfb-homogeneous-polynomial-bar-model). -/
structure FunctionComplex where
  cochain : CochainComplex
    (CategoryTheory.CondensedBar.Equivariant (continuousScalarRing F)
      (LadicLattice.Lattice.{u} ell r)) ℕ
  model : ∀ n : ℕ, HomogeneousFunctions (continuousScalarRing F).toMon
    (LadicLattice.Lattice.{u} ell r) (PolynomialBar.trivialScalar ell F r) n
  term : ∀ n : ℕ, cochain.X n ≅ (model n).object
  differential : ∀ (n : ℕ) (S : Profinite.{u})
    (c : sections (continuousScalarRing F) (cochain.X n).module S)
    (T : Profinite.{u}) (f : T ⟶ S)
    (x : Fin (n + 2) → C(T, LadicLattice.Lattice.{u} ell r)),
    evaluateModel ell F r (n + 1) (model (n + 1)) S
      ((((cochain.d n (n + 1) ≫ (term (n + 1)).hom).val).hom.hom.app (op S)) c) T f x =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        evaluateModel ell F r n (model n) S
          (((term n).hom.val.hom.hom.app (op S)) c) T f (fun j ↦ x (i.succAbove j))

/-- Underlying homogeneous function complex, retaining the same differentials.
Source: direct-images paragraph (3), polynomial evaluation sub-obligation
(blueprint: def-sfb-homogeneous-polynomial-bar-model). -/
def FunctionComplex.underlying (R : FunctionComplex ell F r) :=
  (Profinite.CondensedAction.forgetAction.mapHomologicalComplex (.up ℕ)).obj R.cochain

/-- Evaluation of a homogeneous function-complex section on a generalized tuple.
Source: direct-images paragraph (3), polynomial evaluation sub-obligation
(blueprint: def-sfb-homogeneous-polynomial-bar-model). -/
def FunctionComplex.evaluate (R : FunctionComplex ell F r) (n : ℕ) (S : Profinite.{u})
    (c : sections (continuousScalarRing F) (R.cochain.X n).module S)
    (T : Profinite.{u}) (f : T ⟶ S)
    (x : Fin (n + 1) → C(T, LadicLattice.Lattice.{u} ell r)) :=
  evaluateModel ell F r n (R.model n) S
    (((R.term n).hom.val.hom.hom.app (op S)) c) T f x

/-- A fixed subcomplex is identified sectionwise with exactly the fully fixed sections,
including every further profinite base change. This is a specification of the subsheaf,
not a choice of an invariants functor.
Source: direct-images paragraph (3), polynomial evaluation sub-obligation
(blueprint: def-sfb-homogeneous-polynomial-bar-model). -/
structure FixedComplex (C : CochainComplex
    (CategoryTheory.CondensedBar.Equivariant (continuousScalarRing F)
      (LadicLattice.Lattice.{u} ell r)) ℕ) where
  cochain : CochainComplex (CategoryTheory.CondensedBar.Modules (continuousScalarRing F)) ℕ
  inclusion : cochain ⟶
    (Profinite.CondensedAction.forgetAction.mapHomologicalComplex (.up ℕ)).obj C
  injective : ∀ (n : ℕ) (S : Profinite.{u}),
    Function.Injective ((inclusion.f n).hom.hom.app (op S))
  image : ∀ (n : ℕ) (S : Profinite.{u})
    (c : sections (continuousScalarRing F) (C.X n).module S),
    (∃ x : sections (continuousScalarRing F) (cochain.X n) S,
      ((inclusion.f n).hom.hom.app (op S)) x = c) ↔ FixedAll (C.X n) S c

/-- Compatible augmented evaluation and normalization data. All maps are internal
linear cochain maps, the homogeneous ones equivariant. The generator, fixed-image,
difference and prefix equations determine the stated maps; their existence is a theorem.
Source: direct-images paragraph (3), polynomial evaluation sub-obligation
(blueprint: def-sfb-homogeneous-polynomial-bar-model). -/
structure Data where
  K : PolynomialComplex ell F r
  R : FunctionComplex ell F r
  P : PolynomialBar.Complex (continuousScalarRing F) r
  functions : InternalFunctions (continuousScalarRing F)
  bar : BarDiagram (G := LadicLattice.Lattice.{u} ell r) functions
  a : PolynomialBar.trivialScalar ell F r ⟶ K.cochain.X 0
  a_zero : a.val = K.ι 0 0
  a_cocycle : a ≫ K.cochain.d 0 1 = 0
  b : PolynomialBar.trivialScalar ell F r ⟶ R.cochain.X 0
  b_cocycle : b ≫ R.cochain.d 0 1 = 0
  b_constant : ∀ (S : Profinite.{u}) (c : ULift.{u + 1} C(S, F))
    (T : Profinite.{u}) (f : T ⟶ S)
    (x : Fin 1 → C(T, LadicLattice.Lattice.{u} ell r)) (t : T),
    (R.evaluate ell F r 0 S ((b.val.hom.hom.app (op S)) c) T f x).down t =
      c.down (f.hom.hom t)
  e : K.cochain ⟶ R.cochain
  augmentation : a ≫ e.f 0 = b
  monomial : ∀ (n : ℕ) (m : PolynomialBar.Monomial r (n + 1))
    (S : Profinite.{u}) (c : ULift.{u + 1} C(S, F)) (T : Profinite.{u}) (f : T ⟶ S)
    (x : Fin (n + 1) → C(T, LadicLattice.Lattice.{u} ell r)) (t : T),
    (R.evaluate ell F r n S
      (((K.ι n m ≫ (e.f n).val).hom.hom.app (op S)) c) T f x).down t =
      c.down (f.hom.hom t) * ∏ v : Fin (n + 1) × Fin r,
        (algebraMap ℚ_[ell] F ((x v.1 t).toAdd.down v.2 : ℚ_[ell])) ^ m v
  fixedK : FixedComplex ell F r K.cochain
  fixedR : FixedComplex ell F r R.cochain
  phi : P.cochain ≅ fixedK.cochain
  phi_monomial : ∀ (n : ℕ) (m : PolynomialBar.Monomial r n),
    P.ι n m ≫ phi.hom.f n ≫ fixedK.inclusion.f n =
      PolynomialBar.polynomialArrow (continuousScalarRing F) r (n + 1)
        (K.cochain.X n).module (K.ι n)
        (differencePolynomial r n (MvPolynomial.monomial m 1))
  chi : fixedR.cochain ≅ (cochains bar).obj (PolynomialBar.trivialScalar ell F r)
  chi_prefix : ∀ (n : ℕ) (S : Profinite.{u})
    (c : sections (continuousScalarRing F) (fixedR.cochain.X n) S)
    (T : Profinite.{u}) (f : T ⟶ S)
    (g : Fin n → C(T, LadicLattice.Lattice.{u} ell r)),
    (functions.evaluate (power (LadicLattice.Lattice.{u} ell r) n) S
      (Mod.regular (continuousScalarRing F).X)
      (((chi.hom.f n ≫ (bar.term (PolynomialBar.trivialScalar ell F r) n).hom).hom.hom.app
        (op S)) c)).val T f (tupleMap g) =
      R.evaluate ell F r n S (((fixedR.inclusion.f n).hom.hom.app (op S)) c) T f
        (prefixTuple g)
  fixedEvaluation : fixedK.cochain ⟶ fixedR.cochain
  fixed_square : fixedEvaluation ≫ fixedR.inclusion =
    fixedK.inclusion ≫
      (Profinite.CondensedAction.forgetAction.mapHomologicalComplex (.up ℕ)).map e
  rho : PolynomialBar.Evaluation ell F r P functions bar
  normalization : rho.map = phi.hom ≫ fixedEvaluation ≫ chi.hom

end Profinite.CondensedAction.HomogeneousPolynomialBar
