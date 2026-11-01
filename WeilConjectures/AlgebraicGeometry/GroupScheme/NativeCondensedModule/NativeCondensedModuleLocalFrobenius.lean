/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ZetaSeries
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.StalkLowerStarProj
public import WeilConjectures.WeilObject.Sheaf.Stalk
public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEndBijective
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.PadicAlgClGlobalSections
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import WeilConjectures.PointCount
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedPoint
import WeilConjectures.AlgebraicGeometry.Closed.ClosedPointField

/-! # Native degree-zero local Frobenius for condensed coefficients

Source: latest blueprint, def-weil-local-frobenius-trace, closed-point and semilinear
return paragraphs; Deligne, Weil II (1.1.7)--(1.1.10)
(blueprint: def-weil-local-frobenius-trace).

This companion exposes the degree-zero part without importing the older derived
coefficient interfaces. All data are module inverse image, its composition comparisons,
and actual sections on Spec k. Scalars use the standard universe lift.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.NativeCondensedModule

/-- Positive powers, indexed by exponent n+1.
Source: latest blueprint, local-return convention
(blueprint: def-weil-local-frobenius-trace). -/
def localPositivePower {X : Scheme.{u}} (g : X ⟶ X) : ℕ → (X ⟶ X)
  | 0 => g
  | n + 1 => localPositivePower g n ≫ g

/-- Spec of inverse q-power Frobenius on the algebraic closure.
Source: latest blueprint, g_s in the semilinear return
(blueprint: def-weil-local-frobenius-trace). -/
def frobeniusPointIso (D : FiniteFieldDatum.{u}) : Spec (.of D.k) ≅ Spec (.of D.k) :=
  letI : Fintype D.k₀ := Fintype.ofFinite D.k₀
  Scheme.Spec.mapIso
    (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k).toRingEquiv.toCommRingCatIso.op

/-- The existing module category for the pulled-back condensed Qbar coefficient ring.
Source: Stacks 03QP, condensed refinement
(blueprint: def-weil-local-frobenius-trace). -/
abbrev Modules (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
    (condensedRingObj (Profinite.padicAlgClRingObj l) T)

/-- The coefficient field acts on the regular module by constant sections.
Source: latest blueprint, condensed coefficient and vector-space fibre paragraphs
(blueprint: def-weil-local-frobenius-trace). -/
def pointUnitEndRingHom (l : ℕ) [Fact l.Prime] (k : Type u) [Field k] :
    PadicAlgCl l →+* End (𝟙_ (Modules l (Spec (.of k)))) :=
  letI : (upperStarFromPoint (Spec (.of k))).Additive :=
    haveI : PreservesColimits (upperStarFromPoint (Spec (.of k))) :=
      (pointUpperStarLowerStarAdjunction.comp
        (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1}
          (toSpecZ (Spec (.of k))))).leftAdjoint_preservesColimits
    haveI : PreservesBinaryBiproducts (upperStarFromPoint (Spec (.of k))) :=
      preservesBinaryBiproducts_of_preservesBinaryCoproducts _
    Functor.additive_of_preservesBinaryBiproducts _
  Mod.regularEndRingHom.comp
    ((Γ.mapFunctor (upperStarFromPoint (Spec (.of k)))).comp
      (Profinite.PadicAlgCl.constRingHom l))

/-- Scalar restriction for global sections, with the conventional universe lift.
Source: latest blueprint, actual vector-space-fibre convention
(blueprint: def-weil-local-frobenius-trace). -/
def pointScalarsOp (l : ℕ) [Fact l.Prime] (k : Type u) [Field k] :
    ULift.{u + 1} (PadicAlgCl l) →+*
      (End (𝟙_ (Modules l (Spec (.of k)))))ᵐᵒᵖ :=
  ((pointUnitEndRingHom l k).toOpposite fun x y ↦ by
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]).comp
      ULift.ringEquiv.toRingHom

/-- Actual module global sections, as Hom from the coefficient unit, with constant scalars.
Source: latest blueprint, M_z = Gamma(Spec k,z^* M)
(blueprint: def-weil-local-frobenius-trace). -/
def pointSections (l : ℕ) [Fact l.Prime] (k : Type u) [Field k] :
    Modules l (Spec (.of k)) ⥤ ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl l)) :=
  preadditiveCoyonedaObj (𝟙_ (Modules l (Spec (.of k)))) ⋙
    ModuleCat.restrictScalars (pointScalarsOp l k)

/-- Sections of the actual geometric-point pullback, with the standard scalar lift.
Source: blueprint first paragraph, vector-space-fibre convention
(blueprint: def-weil-local-frobenius-trace). -/
def fibre (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {T : Scheme.{u}} (M : Modules l T) (z : Spec (.of D.k) ⟶ T) :=
  (pointSections l D.k).obj
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
  letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  (pointSections l D.k).mapIso
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


variable (D : FiniteFieldDatum.{u})
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

/-- The residue degree of the chosen closed point.
Source: latest blueprint, r = [kappa(y) : k_0]
(blueprint: def-weil-local-frobenius-trace). -/
def localClosedPointDegree (y : {y : Y₀.left // y ∈ closedPoints Y₀.left}) : ℕ :=
  letI := (Y₀.hom.residueFieldAlgebraMap y.val).toAlgebra
  Module.finrank D.k₀ (Y₀.left.residueField y.val)

/-- Compatibility needed for the canonical pullback lift of the residue embedding.
Source: latest blueprint, chosen k_0-embedding of the residue field
(blueprint: def-weil-local-frobenius-trace).
Proof: the structure composite of fromSpecResidueField is Spec of the residue-field
algebra map. Compose with Spec of iota and its given base-field compatibility. -/
theorem localClosedPoint_compatible
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (iota : Y₀.left.residueField y.val →+* D.k)
    (hiota : iota.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k) :
    (Spec.map (CommRingCat.ofHom iota) ≫ Y₀.left.fromSpecResidueField y.val) ≫ Y₀.hom =
      (𝟙 (Spec (.of D.k))) ≫ Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)) := by
  rw [Category.assoc, ← Y₀.hom.specMap_residueFieldAlgebraMap,
    Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hiota]

/-- The canonical compatible geometric lift of the closed point.
Source: latest blueprint, chosen geometric point bar y
(blueprint: def-weil-local-frobenius-trace). -/
def localClosedPoint (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (iota : Y₀.left.residueField y.val →+* D.k)
    (hiota : iota.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k) :
    Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left :=
  pullback.lift (Spec.map (CommRingCat.ofHom iota) ≫ Y₀.left.fromSpecResidueField y.val) (𝟙 _)
    (localClosedPoint_compatible D Y₀ y iota hiota)

/-- The degree-fold geometric Frobenius satisfies the semilinear return.
Source: latest blueprint, local-return paragraph
(blueprint: def-weil-local-frobenius-trace).
Proof: the closed residue field is finite over k_0 and its dimension d is positive.
Its cardinality is q^d, so the d-th inverse q-power Frobenius fixes every element of
its embedded image. For the pullback lift, the first projection is consequently
unchanged, while the second projection is exactly Spec of that d-th field Frobenius.
Pullback uniqueness proves the equality. Positivity gives (d-1)+1 = d. -/
theorem localClosedPoint_return
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (iota : Y₀.left.residueField y.val →+* D.k)
    (hiota : iota.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k) :
    localClosedPoint D Y₀ y iota hiota ≫
        localPositivePower (D.geometricFrobenius Y₀).hom
          (localClosedPointDegree D Y₀ y - 1) =
      localPositivePower (frobeniusPointIso D).hom (localClosedPointDegree D Y₀ y - 1) ≫
        localClosedPoint D Y₀ y iota hiota := by
  let := Fintype.ofFinite D.k₀
  let := (Y₀.hom.residueFieldAlgebraMap y.val).toAlgebra
  have := (closedPoint_iff_residueField_trdeg_zero_and_finite Y₀.hom y.val).2.1.mp y.prop
  have : Finite (Y₀.left.residueField y.val) := Module.finite_of_finite D.k₀
  have hc : Nat.card (Y₀.left.residueField y.val) =
      Fintype.card D.k₀ ^ localClosedPointDegree D Y₀ y := by
    simpa only [Nat.card_eq_fintype_card, localClosedPointDegree] using
      (Module.natCard_eq_pow_finrank (K := D.k₀) (V := Y₀.left.residueField y.val))
  have hdeg : 1 ≤ localClosedPointDegree D Y₀ y := by
    exact Module.finrank_pos
  apply localLift_return D Y₀ (localClosedPointDegree D Y₀ y - 1)
  rw [← Category.assoc]
  suffices h :
      localPositivePower (frobeniusPointIso D).hom (localClosedPointDegree D Y₀ y - 1) ≫
        Spec.map (CommRingCat.ofHom iota) =
        Spec.map (CommRingCat.ofHom iota) by rw [h]
  rw [localPointPower_eq]
  simp only [Nat.sub_add_cancel hdeg]
  rw [← Spec.map_comp]
  congr 1
  ext a
  exact FiniteField.geometricFrobeniusAlgEquivOfAlgebraic_pow_apply_of_card_eq
    D.k₀ D.k (localClosedPointDegree D Y₀ y) hc iota a

end WeilConjectures.NativeCondensedModule
