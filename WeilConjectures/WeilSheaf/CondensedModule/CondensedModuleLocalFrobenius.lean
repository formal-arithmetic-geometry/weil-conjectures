/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.LocalFrobeniusLarge.LocalFrobeniusLargeCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.StalkLowerStarProj
public import WeilConjectures.TraceFormula.PointFiberFunctor

/-! # Local Frobenius on ordinary condensed modules

Source: Deligne, Weil II (1.1.7)--(1.1.10); latest blueprint local-return convention
(blueprint: def-weil-local-frobenius-trace).

The recorded common-stage derived operators are reexported. This adds their degree-zero
formula directly on the ordinary module category: evaluate exact geometric pullback by
pointSections, reparametrize Spec(k), apply the pullback composition comparisons, and
apply the iterated Weil isomorphism. No finite-stage presentation is required as input.
The scalar field uses the standard universe lift of the fixed PadicAlgCl closure.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.CondensedModule

/-- The existing module category for the pulled-back condensed Qbar coefficient ring.
Source: Stacks 03QP, condensed refinement
(blueprint: def-weil-local-frobenius-trace). -/
abbrev Modules (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (padicAlgClRingObj T l)

/-- Sections of the actual geometric-point pullback, with the standard scalar lift.
Source: blueprint first paragraph, vector-space-fibre convention
(blueprint: def-weil-local-frobenius-trace). -/
def fibre (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {T : Scheme.{u}} (M : Modules l T) (z : Spec (.of D.k) ⟶ T) :=
  (CondensedRing.pointSections l D.k).obj
    ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).obj M)

/-- Compose an indexed chain without unfolding the concrete module category in the recursor.
Source: the successive canonical pullback compositors in the local-return construction
(blueprint: def-weil-local-frobenius-trace). -/
def isoChain {C : Type v} [Category.{w} C] (P : ℕ → C) (M : C)
    (initial : P 0 ≅ M) (step : ∀ n : ℕ, P (n + 1) ≅ P n) : ∀ n : ℕ, P n ≅ M :=
  Nat.rec initial (fun n previous ↦ step n ≪≫ previous)

/-- Evaluate one pullback-composition step in an abstract category.
Source: the pullback compositor followed by the pullback of the Weil isomorphism
(blueprint: def-weil-local-frobenius-trace). -/
def evaluateStep {C : Type v} [Category.{w} C] (F G H : C ⥤ C)
    (c : H ≅ G ⋙ F) (M : C) (θ : G.obj M ≅ M) : H.obj M ≅ F.obj M :=
  c.app M ≪≫ F.mapIso θ

/-- Evaluate the initial functor comparison before the given Weil isomorphism.
Source: the initial positive-power identification in the local-return construction
(blueprint: def-weil-local-frobenius-trace). -/
def evaluateInitial {C : Type v} [Category.{w} C] (F G : C ⥤ C)
    (c : F ≅ G) (M : C) (θ : G.obj M ≅ M) : F.obj M ≅ M :=
  c.app M ≪≫ θ

/-- One positive Weil-iteration step, with its canonical pullback compositor.
Source: blueprint theta iteration, def-weil-local-frobenius-trace
(blueprint: def-weil-local-frobenius-trace). -/
@[irreducible] def iterateStep (l : ℕ) [Fact l.Prime] {T : Scheme.{u}} (a : T ⟶ T)
    (M : Modules l T)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M) (n : ℕ) :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (localPositivePower a (n + 1))).obj M ≅
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (localPositivePower a n)).obj M :=
  evaluateStep
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (localPositivePower a n))
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a)
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (localPositivePower a (n + 1)))
    (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) (localPositivePower a n) a)
    M θ

/-- The iterated Weil isomorphism, indexed by exponent n+1 as in localPositivePower.
Source: blueprint local-return clause; def-weil-local-frobenius-trace
(blueprint: def-weil-local-frobenius-trace). -/
@[irreducible] def iterate (l : ℕ) [Fact l.Prime] {T : Scheme.{u}} (a : T ⟶ T)
    (M : Modules l T)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M) :
    (n : ℕ) →
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (localPositivePower a n)).obj M ≅ M :=
  isoChain (fun n ↦ (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
    (localPositivePower a n)).obj M) M
    (evaluateInitial
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (localPositivePower a 0))
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a)
      (CondensedRing.upperStarCongr (Profinite.padicAlgClRingObj l)
        (show localPositivePower a 0 = a from Eq.refl a)) M θ)
    (iterateStep l a M θ)

/-- Canonical semilinear transport from the next summand to the present summand.
Source: blueprint Frobenius cycle and geometric-point reparametrization
(blueprint: def-weil-local-frobenius-trace). -/
def transport (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {T : Scheme.{u}} (a : T ⟶ T) (M : Modules l T)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M)
    (z z' : Spec (.of D.k) ⟶ T) (n : ℕ)
    (h : z ≫ localPositivePower a n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z') :
    fibre l D M z' ≅ fibre l D M z :=
  (CondensedRing.pointSections l D.k).mapIso
    ((CondensedRing.pointComparison (Profinite.padicAlgClRingObj l)
      (CondensedRing.upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj l)
        (localPositivePower (frobeniusPointIso D).hom n))
      (localPositivePower a n) h).app M ≪≫
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).mapIso
        (iterate l a M θ n))

/-- The local geometric-Frobenius operator for a module in degree zero, with exponent n+1.
The hypothesis is precisely the semilinear return z Phi^(n+1)=Spec(gamma)^(n+1) z.
Source: Deligne, Weil II (1.1.7)--(1.1.10), blueprint local-return convention
(blueprint: def-weil-local-frobenius-trace). -/
def operator (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {T : Scheme.{u}} (a : T ⟶ T) (M : Modules l T)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M)
    (z : Spec (.of D.k) ⟶ T) (n : ℕ)
    (h : z ≫ localPositivePower a n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z) :
    End (fibre l D M z) :=
  (transport l D a M θ z z n h).hom

end WeilConjectures.CondensedModule
