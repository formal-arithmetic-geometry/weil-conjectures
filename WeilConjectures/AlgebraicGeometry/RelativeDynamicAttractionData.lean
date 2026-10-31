/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.SplitTorusOverRing
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.LinearGroupSchemes

/-! # Relative dynamic attraction

Source: Conrad, Reductive group schemes, Definition 4.1.6 and Theorem 4.1.7,
pp.111–114 (blueprint: def-sfb-relative-dynamic-attraction-data).

These are functor-of-points definitions over arbitrary commutative rings.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory Opposite
open scoped MonObj CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.RelativeDynamic

/-- The affine line over an arbitrary ring. Source: Conrad, p.112
(blueprint: def-sfb-relative-dynamic-attraction-data). -/
def affineLine (R : Type u) [CommRing R] : Over (Spec (.of R)) :=
  (Spec (.of (Polynomial R))).asOver (Spec (.of R))

/-- The usual inclusion G_m into A^1, induced by R[t] into R[t,t^-1].
Source: Conrad, p.112 (blueprint: def-sfb-relative-dynamic-attraction-data). -/
def puncturedLine (R : Type u) [CommRing R] :
    (RingGroupSchemes.multiplicative R).X ⟶ affineLine R :=
  (Spec.map (CommRingCat.ofHom (Polynomial.toLaurentAlg (R := R)).toRingHom)).asOver _

/-- The zero section of A^1. Source: Conrad, p.112
(blueprint: def-sfb-relative-dynamic-attraction-data). -/
def zeroSection (R : Type u) [CommRing R] :
    𝟙_ (Over (Spec (.of R))) ⟶ affineLine R :=
  letI := braidedAlgSpec (R := .of R)
  Functor.LaxMonoidal.ε (algSpec (.of R)) ≫
    (algSpec (.of R)).map (CommAlgCat.ofHom (Polynomial.aeval (0 : R))).op

/-- The integer characters as regular functions on G_m. Source: Conrad, p.113
(blueprint: def-sfb-relative-dynamic-attraction-data). -/
def characters (R : Type u) [CommRing R] (n : ℤ) :
    Γ((RingGroupSchemes.multiplicative R).X.left, ⊤) :=
  (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv (LaurentPolynomial.T n)

section OrbitData

variable {S : Scheme.{u}} (T : Grp (Over S)) (L : Over S)
  (j : T.X ⟶ L) (G : Grp (Over S)) (act : T.X ⊗ G.X ⟶ G.X)

/-- An extension of the orbit to the affine line over the test scheme.
The same formula applies to pulled-back tori and affine lines.
Source: Conrad, p.112 (blueprint: def-sfb-relative-dynamic-attraction-data). -/
def IsOrbitExtension (W : Over S) (g : W ⟶ G.X) (p : W ⊗ L ⟶ G.X) : Prop :=
  (𝟙 W ⊗ₘ j) ≫ p = lift (snd W T.X) (fst W T.X ≫ g) ≫ act

end OrbitData

section WeightData

variable {R : Type u} [CommRing R] (T G : Grp (Over (Spec (.of R))))
  (chi : ℤ → Γ(T.X.left, ⊤)) (act : T.X ⊗ G.X ⟶ G.X)

/-- Homogeneous regular functions, tested on the universal action morphism:
f(a(t,g)) = t^n f(g). Source: Conrad, proof of Theorem 4.1.7, p.113
(blueprint: def-sfb-relative-dynamic-attraction-data). -/
def homogeneous (n : ℤ) : Set Γ(G.X.left, ⊤) :=
  {f | act.left.appTop f =
    (fst T.X G.X).left.appTop (chi n) * (snd T.X G.X).left.appTop f}

/-- Evaluation of an infinitesimal vector on a regular function, taking its epsilon part.
Source: Conrad, p.114, dual-number calculation
(blueprint: def-sfb-relative-dynamic-attraction-data). -/
def tangentCoefficient (v : GrpObj.Lie G.X) (f : Γ(G.X.left, ⊤)) : R :=
  TrivSqZeroExt.snd ((Scheme.ΓSpecIso (.of (DualNumber R))).hom
    ((GrpObj.tangentPoint v).left.appTop f))

/-- A character-n tangent vector annihilates every homogeneous function of degree different
from n. This uses the full character, not its differential in the residue characteristic.
The span equals this linear eigenspace for an action by group automorphisms.
Source: Conrad, Theorem 4.1.7(4), pp.113--114
(blueprint: def-sfb-relative-dynamic-attraction-data). -/
def weightSpace (n : ℤ) : Submodule R (GrpObj.Lie G.X) :=
  Submodule.span R {v | ∀ (m : ℤ), m ≠ n →
    ∀ f ∈ homogeneous T G chi act m, tangentCoefficient G v f = 0}

end WeightData

/-- The canonical map R[epsilon] to B[epsilon], fixing epsilon and applying R to B to
coefficients. Source: Conrad, p.114 (blueprint: def-sfb-relative-dynamic-attraction-data). -/
def dualBaseMap (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] :
    DualNumber R →ₐ[R] DualNumber B :=
  DualNumber.lift ⟨(Algebra.ofId R (DualNumber B), DualNumber.eps),
    DualNumber.eps_mul_eps, fun _ ↦ Commute.all _ _⟩

/-- The canonical tangent comparison is characterized on pure tensors by its actual
map on dual-number points. This characterization determines a linear map uniquely.
Source: Conrad, dual-number calculation and base-change paragraph, p.114
(blueprint: def-sfb-relative-dynamic-attraction-data). -/
def IsTangentComparison {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (H : Grp (Over (Spec (.of R))))
    (e : B ⊗[R] GrpObj.Lie H.X ≃ₗ[B]
      GrpObj.Lie ((Over.pullback (Spec.map
        (CommRingCat.ofHom (algebraMap R B)))).mapGrp.obj H).X) : Prop :=
  ∀ v : GrpObj.Lie H.X,
    (GrpObj.tangentPoint (e (1 ⊗ₜ[R] v))).left ≫
        pullback.fst H.X.hom (Spec.map (CommRingCat.ofHom (algebraMap R B))) =
      Spec.map (CommRingCat.ofHom (dualBaseMap R B).toRingHom) ≫
        (GrpObj.tangentPoint v).left

/-- Affine test schemes over a ring. Source: Conrad §4.1
(blueprint: def-sfb-relative-dynamic-attraction-data). -/
def affine (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B] :
    Over (Spec (.of A)) := (algSpec (.of A)).obj (op (CommAlgCat.of A B))

/-- Contravariant coordinate maps. Source: Conrad §4.1
(blueprint: def-sfb-relative-dynamic-attraction-data). -/
def map {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] (f : B →ₐ[A] C) : affine A C ⟶ affine A B :=
  (algSpec (.of A)).map (CommAlgCat.ofHom f).op

/-- Evaluation at zero or one. Source: Conrad Definition 4.1.6
(blueprint: def-sfb-relative-dynamic-attraction-data). -/
def linePoint (A : Type u) [CommRing A] (c : A) :
    𝟙_ (Over (Spec (.of A))) ⟶ affineLine A :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom c)))
    (by
      change Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom c)) ≫
        Spec.map (CommRingCat.ofHom Polynomial.C) = 𝟙 _
      rw [← Spec.map_comp]
      convert Spec.map_id (.of A) using 1
      congr 1
      ext x
      exact Polynomial.eval_C)

/-- The action preserves multiplication on every test scheme; inverse elements in Gm
then give automorphisms. Source: Conrad Definition 4.1.6
(blueprint: def-sfb-relative-dynamic-attraction-data). -/
def ActsByAutomorphisms {A : Type u} [CommRing A]
    (H : Grp (Over (Spec (.of A)))) [ModObj ((RingGroupSchemes.multiplicative A).X) H.X] : Prop :=
  ∀ (T : Over (Spec (.of A))) (s : T ⟶ (RingGroupSchemes.multiplicative A).X) (x y : T ⟶ H.X),
    s • (x * y) = (s • x) * (s • y)

/-- An orbit extension with value the group identity at zero. Source: Conrad
Definition 4.1.6 (blueprint: def-sfb-relative-dynamic-attraction-data). -/
def IsContractingOrbitExtension {A : Type u} [CommRing A]
    (H : Grp (Over (Spec (.of A)))) [ModObj ((RingGroupSchemes.multiplicative A).X) H.X]
    {T : Over (Spec (.of A))} (h : T ⟶ H.X) (extension : affineLine A ⊗ T ⟶ H.X) : Prop :=
  IsOrbitExtension (RingGroupSchemes.multiplicative A) (affineLine A)
    (puncturedLine A) H
    (ModObj.smul (M := (RingGroupSchemes.multiplicative A).X) (X := H.X)) T h
    ((β_ T (affineLine A)).hom ≫ extension) ∧
    lift (toUnit T ≫ zeroSection A) (𝟙 T) ≫ extension = 1

/-- The attracting subfunctor, tested on arbitrary schemes over the base. Source:
Conrad Definition 4.1.6 (blueprint: def-sfb-relative-dynamic-attraction-data). -/
def Attracts {A : Type u} [CommRing A]
    (H : Grp (Over (Spec (.of A)))) [ModObj ((RingGroupSchemes.multiplicative A).X) H.X]
    {T : Over (Spec (.of A))} (h : T ⟶ H.X) : Prop :=
  ∃ extension : affineLine A ⊗ T ⟶ H.X, IsContractingOrbitExtension H h extension

/-- Representability as a subfunctor, including its specified inclusion. Source:
Conrad Theorem 4.1.7 (blueprint: def-sfb-relative-dynamic-attraction-data). -/
def Represents {A : Type u} [CommRing A]
    (H : Grp (Over (Spec (.of A)))) [ModObj ((RingGroupSchemes.multiplicative A).X) H.X]
    (U : Grp (Over (Spec (.of A)))) (i : U ⟶ H) : Prop :=
  ∀ (T : Over (Spec (.of A))) (h : T ⟶ H.X),
    Attracts H h ↔ ∃! x : T ⟶ U.X, x ≫ i.hom.hom = h

/-- The positive part of the coaction weight decomposition, as a submodule.
Source: Conrad Theorem 4.1.7(4) (blueprint: def-sfb-relative-dynamic-attraction-data). -/
def positiveWeights {A : Type u} [CommRing A]
    (H : Grp (Over (Spec (.of A)))) [ModObj ((RingGroupSchemes.multiplicative A).X) H.X] :
    Submodule A (GrpObj.Lie H.X) :=
  ⨆ (j : ℤ) (_ : 0 < j), weightSpace (RingGroupSchemes.multiplicative A) H (characters A)
    (ModObj.smul (M := (RingGroupSchemes.multiplicative A).X) (X := H.X)) j

/-- Unipotence of geometric fibres via a faithful representation of each fibre.
Testing every algebraically closed field mapping to the base includes the algebraic
closures of all residue fields. Source: Conrad Theorem 4.1.7(4)
(blueprint: def-sfb-relative-dynamic-attraction-data). -/
def HasUnipotentGeometricFibres {A : Type u} [CommRing A]
    (U : Grp (Over (Spec (.of A)))) : Prop :=
  ∀ (F : Type u) [Field F] [IsAlgClosed F] [Algebra A F],
    ∃ (n : ℕ) (r : ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap A F)))).obj U.X) ⟶
        GeneralLinearGroup (ULift.{u} (Fin n)) F),
      IsClosedImmersion r.left ∧
      (∀ (B : Type u) [CommRing B] [Algebra F B]
        (x y : affine F B ⟶
          (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap A F)))).obj U.X),
        (x * y) ≫ r = (x ≫ r) * (y ≫ r)) ∧
      ∀ x : affine F F ⟶
          (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap A F)))).obj U.X,
        IsNilpotent ((GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) F F (x ≫ r)).val - 1)

/-- Pullback of a group scheme along a ring homomorphism, with its canonical
transported group structure. Source: Conrad, paragraph before Proposition 4.1.10
(blueprint: def-sfb-relative-dynamic-attraction-data). -/
def baseChange {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    Grp (Over (Spec (.of A))) ⥤ Grp (Over (Spec (.of B))) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom f))).mapGrp

/-- Forgetting the base extension of a test point, using the canonical pullback
adjunction. Source: Conrad, paragraph before Proposition 4.1.10
(blueprint: def-sfb-relative-dynamic-attraction-data). -/
def forgetPoint {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (H : Grp (Over (Spec (.of A)))) (T : Over (Spec (.of B)))
    (x : T ⟶ ((baseChange f).obj H).X) :
    (Over.map (Spec.map (CommRingCat.ofHom f))).obj T ⟶ H.X :=
  ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom f))).homEquiv T H.X).symm x

/-- The tangent inclusion as actual infinitesimal points in the ambient group.
Source: Conrad Theorem 4.1.7(4) (blueprint: def-sfb-relative-dynamic-attraction-data). -/
def TangentImage {A : Type u} [CommRing A]
    {H U : Grp (Over (Spec (.of A)))} (i : U ⟶ H) (v : GrpObj.Lie H.X) : Prop :=
  ∃ w : GrpObj.Lie U.X, GrpObj.tangentPoint w ≫ i.hom.hom = GrpObj.tangentPoint v

/-- The tangent map, in the existing Lie module, obtained from the actual map on
infinitesimal points. Source: Conrad Proposition 4.1.10(2)
(blueprint: def-sfb-relative-dynamic-attraction-data). -/
def tangentMap {S : Scheme.{u}} {H U : Grp (Over S)} (i : U ⟶ H)
    (v : GrpObj.Lie U.X) : GrpObj.Lie H.X :=
  GrpObj.lieEquiv H.X (GrpObj.infPointsMap i.hom.hom ((GrpObj.lieEquiv U.X).symm v))

/-- Base-change representability of the attracting functor. The right side uses
the pullback inclusion; the left side uses exactly the same orbit maps, viewed over
the original base by the pullback adjunction. Source: Conrad, paragraph before
Proposition 4.1.10 (blueprint: def-sfb-relative-dynamic-attraction-data). -/
def RepresentsAfterBaseChange {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (H : Grp (Over (Spec (.of A))))
    [ModObj ((RingGroupSchemes.multiplicative A).X) H.X]
    {U : Grp (Over (Spec (.of A)))} (i : U ⟶ H) : Prop :=
  ∀ (T : Over (Spec (.of B))) (h : T ⟶ ((baseChange f).obj H).X),
    Attracts H (forgetPoint f H T h) ↔
      ∃! x : T ⟶ ((baseChange f).obj U).X,
        x ≫ ((baseChange f).map i).hom.hom = h

end AlgebraicGeometry.RelativeDynamic
