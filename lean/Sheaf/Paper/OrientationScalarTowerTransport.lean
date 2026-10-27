/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.SecSmoothPurity.FiniteGeneralRing
public import Sheaf.Paper.CohomologicalSmoothnessFiniteComparison
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.Paper.SmoothPurityTowerGamma
public import Sheaf.Paper.SmoothPurityCoefficientTowersAbelian
public import Sheaf.Paper.SmoothPurityTowerExceptionalBaseChange
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations
public import Sheaf.Paper.EtaleProEtaleScalarMate
import Sheaf.Paper.TateScalarPullbackCoherence
import Sheaf.Paper.PulledOrderedLineSingle
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Transport of orientation equations through scalars and towers

Source: latest blueprint, sec-smooth-purity/sk-prop-sp-purity-bc/
sk-prop-sp-purity-bc-factors.proof.md, paragraph (1), and Stacks Tag 06XS
(blueprint: lem-sp-orientation-scalar-tower-transport).

Finite dualizing objects are written in their canonical etale-origin coordinates
inside the ordinary pro-etale derived category. Every comparison below is constructed
from the published counit mate, site comparison, or normalized Tate comparison.
Tower indices n denote positive exponents n+1, including ramified coefficients.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false

universe u t v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme WeilConjectures
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.OrientationTransport
open Etale.FiniteSmoothPurity

/-- The actual relative dualizing object in the canonical comparison coordinates.
Source: paragraph (1), omega (blueprint: lem-sp-orientation-scalar-tower-transport). -/
abbrev omega (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :=
  (comparison A X).obj (Etale.dualizingComplex (ModuleCat.{u + 1} A) f)

/-- The actual Tate line, with the ordered tensor model of its even shift.
Source: paragraph (1), L (blueprint: lem-sp-orientation-scalar-tower-transport). -/
abbrev tate (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (T : Scheme.{u}) (d : ℕ) := (comparison A T).obj (line A N hA T d)

/-- The transpose of inverse compact-support exchange and the pulled-back counit,
transported by the canonical site/pullback isomorphism.
Source: paragraph (1), e (blueprint: lem-sp-orientation-scalar-tower-transport). -/
def exchange (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {v' : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {u' : X' ⟶ X}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback u' f' f v') :
    (proPullback A u').obj (omega A f) ⟶ omega A f' :=
  (sitePullbackIso A u').hom.app (Etale.dualizingComplex (ModuleCat.{u + 1} A) f) ≫
    (comparison A X').map (Etale.dualizingComplexBaseChangeMap A sq)

/-- The exceptional scalar counit mate at the coefficient unit, with the actual
site/scalar comparison. No underived scalar tensor or flatness assumption is used.
Source: paragraph (1), c_f (blueprint: lem-sp-orientation-scalar-tower-transport). -/
def scalarComparison {R A : Type (u + 1)} [CommRing R] [CommRing A] [Finite R] [Finite A]
    (φ : R →+* A) {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :
    (proScalar φ X).obj (omega R f) ⟶ omega A f :=
  (pbcComparisonReduction X φ).hom.app (Etale.dualizingComplex (ModuleCat.{u + 1} R) f) ≫
    (comparison A X).map (Etale.ExceptionalCoefficients.dualizingScalarMap φ f)

/-- Canonical pullback of the Tate line: site comparison, then normalized
root, tensor, and shift comparisons, including the constant unit when d=0.
Source: paragraph (1), Tate identifications
(blueprint: lem-sp-orientation-scalar-tower-transport). -/
def tatePullback (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (tw : Etale.OrdinaryFiniteTwistTransport A N hA)
    {X X' : Scheme.{u}} (u' : X' ⟶ X) (hX : IsUnit (N : Γ(X, ⊤))) (d : ℕ) :
    (proPullback A u').obj (tate A N hA X d) ≅ tate A N hA X' d :=
  (sitePullbackIso A u').app (line A N hA X d) ≪≫
    (comparison A X').mapIso
      (Etale.vectorIntegrationBaseCoefficientPullback A N hA tw u' hX d)

/-- Finite scalar transport of an orientation square and its inverse equation.
The supplied root transports and coefficient-line comparisons carry their published
root-inclusion and pure-tensor normalizations, so they denote canonical comparisons.
Source: latest blueprint, purity-bc-factors proof (1), finite scalar passage
(blueprint: lem-sp-orientation-scalar-tower-transport).

Proof:
1. Precompose the proposed equation by pullback of c_f. Use the mixed square,
then the primed orientation normalization, to replace it by scalar extension of
Pi_f' e_R. The assumed R equation replaces this by scalar extension of u_R* Pi_f.
2. Naturality of the canonical scalar/pullback comparison identifies this with
u_A* of scalar extension of Pi_f. Normalization at f and the canonical Tate
comparisons give u_A* Pi_f,A followed by u_A* c_f. Cancel the latter isomorphism.
3. Compose with pullback of Pi_f,A inverse; functoriality and cancellation give
the inverse orientation equation. No flatness of R to A is used.
-/
theorem finite_scalar_transport
    (k : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hne : ell ≠ k.p)
    (r : ℕ) (hr : 1 ≤ r)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : ((ell ^ r : ℕ) : A) = 0)
    (φ : coefficient ell r →+* A)
    (X Y X' Y' : Over (Spec (.of k.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
    [IsSeparated Y'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
    (f : X ⟶ Y) (v' : Y' ⟶ Y) (u' : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback u'.left f'.left f.left v'.left)
    (d : ℕ) [SmoothOfRelativeDimension d f.left]
    [HasCompactification f.left] [HasCompactification f'.left] [QuasiCompact f'.left]
    (twR : Etale.OrdinaryFiniteTwistTransport (coefficient ell r) (ell ^ r)
      (CharP.cast_eq_zero _ _))
    (twA : Etale.OrdinaryFiniteTwistTransport A (ell ^ r) hA)
    (sX : CoefficientLineComparison φ (ell ^ r) (ell ^ r)
      (CharP.cast_eq_zero _ _) hA X.left)
    (sX' : CoefficientLineComparison φ (ell ^ r) (ell ^ r)
      (CharP.cast_eq_zero _ _) hA X'.left)
    (piR : omega (coefficient ell r) f.left ≅
      tate (coefficient ell r) (ell ^ r) (CharP.cast_eq_zero _ _) X.left d)
    (piR' : omega (coefficient ell r) f'.left ≅
      tate (coefficient ell r) (ell ^ r) (CharP.cast_eq_zero _ _) X'.left d)
    (piA : omega A f.left ≅ tate A (ell ^ r) hA X.left d)
    (piA' : omega A f'.left ≅ tate A (ell ^ r) hA X'.left d)
    (_hc : IsIso (scalarComparison φ f.left))
    (_hc' : IsIso (scalarComparison φ f'.left))
    (_norm : scalarComparison φ f.left ≫ piA.hom =
      (proScalar φ X.left).map piR.hom ≫ proTwistMap d sX)
    (_norm' : scalarComparison φ f'.left ≫ piA'.hom =
      (proScalar φ X'.left).map piR'.hom ≫ proTwistMap d sX')
    (_mixed : (proPullback A u'.left).map
        (scalarComparison φ f.left) ≫ exchange A sq =
      (scalarPullbackProEtaleIso φ u'.left).hom.app (omega (coefficient ell r) f.left) ≫
        (proScalar φ X'.left).map (exchange (coefficient ell r) sq) ≫
          scalarComparison φ f'.left)
    (_orientationR : exchange (coefficient ell r) sq ≫ piR'.hom =
      (proPullback (coefficient ell r) u'.left).map piR.hom ≫
        (tatePullback (coefficient ell r) (ell ^ r) (CharP.cast_eq_zero _ _) twR
          u'.left
          ((finiteGeneralRingPrimeSetting k ell hne r hr).diagonalExponent_isUnit X.hom) d).hom) :
    (exchange A sq ≫ piA'.hom =
      (proPullback A u'.left).map piA.hom ≫
        (tatePullback A (ell ^ r) hA twA u'.left
          ((finiteGeneralRingPrimeSetting k ell hne r hr).diagonalExponent_isUnit X.hom) d).hom) ∧
    ((proPullback A u'.left).map piA.inv ≫ exchange A sq =
      (tatePullback A (ell ^ r) hA twA u'.left
        ((finiteGeneralRingPrimeSetting k ell hne r hr).diagonalExponent_isUnit X.hom) d).hom ≫
        piA'.inv) := by
  let := _hc
  let P := proPullback A u'.left
  let S := proScalar φ X'.left
  let lam := scalarPullbackProEtaleIso φ u'.left
  let hX :=
    (finiteGeneralRingPrimeSetting k ell hne r hr).diagonalExponent_isUnit X.hom
  let tR := (tatePullback (coefficient ell r) (ell ^ r) (CharP.cast_eq_zero _ _)
    twR u'.left hX d).hom
  let tA := (tatePullback A (ell ^ r) hA twA u'.left hX d).hom
  have ht : P.map (proTwistMap d sX) ≫ tA =
      lam.hom.app (tate (coefficient ell r) (ell ^ r)
        (CharP.cast_eq_zero _ _) X.left d) ≫ S.map tR ≫ proTwistMap d sX' :=
    tate_scalar_pullback_coherence φ (ell ^ r) (pow_pos (Fact.out : ell.Prime).pos r)
      (CharP.cast_eq_zero _ _) hA twR twA u'.left hX d sX sX'
  have hor : exchange A sq ≫ piA'.hom = P.map piA.hom ≫ tA := by
    apply (cancel_epi (P.map (scalarComparison φ f.left))).mp
    calc
      P.map (scalarComparison φ f.left) ≫ (exchange A sq ≫ piA'.hom) =
          lam.hom.app (omega (coefficient ell r) f.left) ≫
            S.map (exchange (coefficient ell r) sq) ≫
              scalarComparison φ f'.left ≫ piA'.hom := by
        rw [← Category.assoc, _mixed]
        simp only [P, S, lam, Category.assoc]
      _ = lam.hom.app (omega (coefficient ell r) f.left) ≫
          S.map (exchange (coefficient ell r) sq ≫ piR'.hom) ≫ proTwistMap d sX' := by
        rw [_norm', S.map_comp]
        simp only [S, lam, Category.assoc]
      _ = lam.hom.app (omega (coefficient ell r) f.left) ≫
          S.map ((proPullback (coefficient ell r) u'.left).map piR.hom) ≫
            S.map tR ≫ proTwistMap d sX' := by
        rw [_orientationR, S.map_comp]
        simp only [S, lam, tR, Category.assoc]
      _ = P.map ((proScalar φ X.left).map piR.hom) ≫
          lam.hom.app (tate (coefficient ell r) (ell ^ r)
            (CharP.cast_eq_zero _ _) X.left d) ≫ S.map tR ≫ proTwistMap d sX' := by
        simpa only [P, S, lam, proScalar, proPullback,
          Functor.comp_map, Category.assoc] using
          congrArg (fun t ↦ t ≫ S.map tR ≫ proTwistMap d sX')
            (lam.hom.naturality piR.hom).symm
      _ = P.map ((proScalar φ X.left).map piR.hom) ≫
          P.map (proTwistMap d sX) ≫ tA := by rw [ht]
      _ = P.map (scalarComparison φ f.left) ≫ (P.map piA.hom ≫ tA) := by
        rw [← P.map_comp_assoc, ← _norm, P.map_comp]
        simp only [P, Category.assoc]
  refine ⟨hor, ?_⟩
  apply (cancel_mono piA'.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hor, ← P.map_comp_assoc, piA.inv_hom_id, P.map_id,
    Category.id_comp]

/-- Exact level evaluation in the ordinary derived model supplied by the abelian
tower datum. This merely abbreviates derived sectionwise evaluation and keeps the
scheme universe t independent of the coefficient-field universe v.
Source: coefficient-tower abelianness, clause (2), and latest purity-bc-factors proof (1)
(blueprint: lem-sp-orientation-scalar-tower-transport). -/
abbrev towerEvaluation
    (ell : ℕ) [Fact ell.Prime] (E : Type v) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E] (T : Scheme.{t})
    (B : SpCoefficientTowersAbelian ell E T) (n : ℕ) :=
  letI := B.hasDerived
  letI := B.equivalenceAdditive
  letI := B.evaluationLimits n
  letI := B.evaluationColimits n
  (spCoefficientEvaluation ell E T B.equivalence n).mapDerivedCategory

section

attribute [-instance]
  CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Exact level evaluations detect maps between any two equally shifted sheaf towers.
Source: latest blueprint, purity-bc-factors proof (1); Stacks Tag 06XS
(blueprint: lem-sp-orientation-scalar-tower-transport).

Proof:
1. Full faithfulness of the degree-zero single embedding, followed by the shift
equivalence, writes each map uniquely as the shifted single of a tower sheaf map.
2. Exact evaluation commutes with singles and shifts. Faithfulness of the finite
single embedding identifies the evaluated underlying sheaf maps.
3. A tower map is its compatible family of level maps. Their equality gives the
original tower map equality, hence the derived equality. Normalization is unused.
-/
theorem shifted_tower_evaluation_injective
    (ell : ℕ) [Fact ell.Prime] (E : Type v) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E] (T : Scheme.{t})
    (B : SpCoefficientTowersAbelian ell E T)
    (F G : spCoefficientTowers ell E T) (s : ℤ)
    (a b : ((@DerivedCategory.singleFunctor _ _ _ B.hasDerived 0).obj F)⟦s⟧ ⟶
      ((@DerivedCategory.singleFunctor _ _ _ B.hasDerived 0).obj G)⟦s⟧)
    (_hab : ∀ n : ℕ,
      (towerEvaluation ell E T B n).map a =
        (towerEvaluation ell E T B n).map b) : a = b := by
  let := B.hasDerived
  let := B.equivalenceAdditive
  let := B.evaluationLimits
  let := B.evaluationColimits
  let S := DerivedCategory.singleFunctor (spCoefficientTowers ell E T) 0
  let J := S ⋙ shiftFunctor _ s
  let f := J.preimage a
  let g := J.preimage b
  have hab : J.map f = J.map g := by
    congr 1
    apply B.equivalence.functor.map_injective
    apply SheafOfModules.strictRingSystem_hom_ext (spCoefficientCommRings ell E T)
    intro n
    let V := spCoefficientEvaluation ell E T B.equivalence n
    let K := DerivedCategory.singleFunctor
      (SheafOfModules.systemLevel.{t + 1, t, max v (t + 1)}
        (spCoefficientCommRings ell E T) n) 0 ⋙ shiftFunctor _ s
    let e : J ⋙ V.mapDerivedCategory ≅ V ⋙ K :=
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft S (V.mapDerivedCategory.commShiftIso s) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (V.mapDerivedCategorySingleFunctor 0) _ ≪≫
        Functor.associator _ _ _
    apply K.map_injective
    apply (cancel_epi (e.hom.app F)).mp
    have heq : V.mapDerivedCategory.map (J.map f) =
        V.mapDerivedCategory.map (J.map g) := by
      simpa only [f, g, Functor.map_preimage] using _hab n
    exact (e.hom.naturality f).symm.trans
      ((congrArg (fun h ↦ h ≫ e.hom.app G) heq).trans (e.hom.naturality g))
  simpa only [f, g, Functor.map_preimage] using hab

end

/-- Levelwise orientation equations imply the actual tower equation, including the
endomorphism h identity. The line is given in the full subcategory with its actual
ordered Tate-line presentation; pullback of this line supplies the primed Tate line.
Source: latest blueprint, purity-bc-factors proof (1), tower passage
(blueprint: lem-sp-orientation-scalar-tower-transport).

Proof:
1. Form h=a_f' inverse e u*a_f using the actual tower mate and the actual
orientations. The line presentation identifies its source with A_X'(d)[2d].
2. This is a shifted sheaf tower: the unshifted Tate factors are locally free
sheaves, their ordinary tensors compute derived tensor, and exact tower pullback
preserves single sheaf complexes and commutes with the common even shift.
3. Every evaluation of h is the identity by the assumed finite equations.
Apply shifted_tower_evaluation_injective to h and the identity, transporting
through the single-degree line presentation. Thus h is the identity.
4. Compose with a_f' to get the orientation equation. Fullness gives the same
equality in the uniform constructible finite-Tor subcategory. No normalization
or unramifiedness assumption occurs. If ell=epsilon*pi^e, its n-th power ideal
is (pi^(en)); therefore these same levels include every ramified E.
-/
theorem tower_orientation_transport
    (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    (b : SpTowerShriek.Base ell E) (o : SpTowerShriek.Operations ell E b)
    (q : SpTowerCalculus.Coordinates ell E b)
    (k : FiniteFieldDatum.{u}) (_hne : ell ≠ k.p)
    (X Y X' Y' : Over (Spec (.of k.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
    [IsSeparated Y'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
    (f : X ⟶ Y) (v' : Y' ⟶ Y) (u' : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback u'.left f'.left f.left v'.left)
    (d : ℕ) [SmoothOfRelativeDimension d f.left] (c : Compactification f.left)
    (m : SpTowerMate.Data ell E b o q sq c)
    (x : SpTowerShriek.OpenExchange ell E b o)
    (hb : IsIso (SpTowerMate.beta ell E b o q m x))
    (hU : spConstructibleTorTowers ell E Y.left (q.abelian Y.left)
      (SpTowerGamma.originalUnit ell E b q Y.left))
    (w : SpChartAdmissibility.Twists ell E X.left)
    (L : SpTowerCalculus.C ell E b q X.left)
    (_line : (SpTowerCalculus.realization ell E b X.left (q.abelian X.left)).functor.obj
        L.obj ≅ SpTowerGamma.orderedLine ell E b X.left w d)
    (a : L ≅ m.right.obj ⟨SpTowerGamma.originalUnit ell E b q Y.left, hU⟩)
    (a' : (SpTowerMate.U ell E b o q m).obj L ≅
      m.right'.obj ((SpTowerMate.V ell E b o q m).obj
        ⟨SpTowerGamma.originalUnit ell E b q Y.left, hU⟩))
    (_levels : ∀ n : ℕ,
      (spDerivedCoefficientEvaluation ell E X'.left (q.abelian X'.left) n).map
          (((SpTowerMate.U ell E b o q m).map a.hom ≫
            (SpTowerMate.mate ell E b o q m x hb).app
              ⟨SpTowerGamma.originalUnit ell E b q Y.left, hU⟩).hom) =
        (spDerivedCoefficientEvaluation ell E X'.left (q.abelian X'.left) n).map a'.hom.hom) :
    ((SpTowerMate.U ell E b o q m).map a.hom ≫
        (SpTowerMate.mate ell E b o q m x hb).app
          ⟨SpTowerGamma.originalUnit ell E b q Y.left, hU⟩ = a'.hom) ∧
    ((SpTowerMate.U ell E b o q m).map a.hom ≫
        (SpTowerMate.mate ell E b o q m x hb).app
          ⟨SpTowerGamma.originalUnit ell E b q Y.left, hU⟩ ≫ a'.inv = 𝟙 _) := by
  let B := q.abelian X'.left
  let := B.hasDerived
  let U := SpTowerMate.U ell E b o q m
  let z := (SpTowerMate.mate ell E b o q m x hb).app
    ⟨SpTowerGamma.originalUnit ell E b q Y.left, hU⟩
  let h : U.obj L ⟶ U.obj L := (U.map a.hom ≫ z) ≫ a'.inv
  obtain ⟨F, ⟨i₀⟩⟩ := pulled_ordered_line_single ell E b o q u'.left
    (by simpa only [WeilConjectures.PurityFiniteSetting.diagonalExponent,
      finiteGeneralRingPrimeSetting, pow_one] using
      (finiteGeneralRingPrimeSetting k ell _hne 1 (by omega)).diagonalExponent_isUnit X.hom)
    w d L.obj _line
  let i : (U.obj L).obj ≅
      ((@DerivedCategory.singleFunctor _ _ _ B.hasDerived 0).obj F)⟦2 * (d : ℤ)⟧ := i₀
  have hh : i.inv ≫ h.hom ≫ i.hom = 𝟙 _ := by
    apply shifted_tower_evaluation_injective ell E X'.left B F F (2 * (d : ℤ))
    intro n
    let V := spDerivedCoefficientEvaluation ell E X'.left B n
    have hn : V.map h.hom = 𝟙 _ := by
      change V.map ((U.map a.hom ≫ z).hom ≫ a'.inv.hom) = _
      rw [V.map_comp, _levels n, ← V.map_comp, ← ObjectProperty.FullSubcategory.comp_hom,
        a'.hom_inv_id, ObjectProperty.FullSubcategory.id_hom, V.map_id]
    change V.map (i.inv ≫ h.hom ≫ i.hom) = V.map (𝟙 _)
    rw [V.map_comp, V.map_comp, hn, Category.id_comp, ← V.map_comp,
      i.inv_hom_id, V.map_id]
  have hid : h.hom = 𝟙 _ := by
    apply (cancel_epi i.inv).mp
    apply (cancel_mono i.hom).mp
    simpa only [Category.assoc, Category.comp_id, Category.id_comp, i.inv_hom_id] using hh
  have hfull : h = 𝟙 _ := by
    apply ObjectProperty.hom_ext
    exact hid
  have hor : U.map a.hom ≫ z = a'.hom := by
    apply (cancel_mono a'.inv).mp
    simpa only [h, Category.assoc, a'.hom_inv_id] using hfull
  exact ⟨hor, by simpa only [h, Category.assoc] using hfull⟩

/-- Ramified coefficient levels use the same ideals, with the ramification index
measured by the order of ell in the recorded DVR. Consequently the identity on O_E
identifies O_E/ell^(n+1) with A_(E,e(n+1)); no unramifiedness is imposed.
Source: latest blueprint, purity-bc-factors proof (1), coefficient convention
(blueprint: lem-sp-orientation-scalar-tower-transport).

Proof: the recorded extending valuation makes O_E a DVR and its chosen uniformizer
irreducible. Ell is nonzero and has positive valuation, so uniquely ell=epsilon*pi^e
with epsilon a unit and e positive. This e is its emultiplicity. Taking the (n+1)-th
power and discarding the unit gives equality of the two principal ideals. Rewriting
powers of principal ideals gives the displayed equality and the identity-induced
quotient identification, including all ramification indices. -/
theorem ramified_coefficient_level
    (ell : ℕ) [Fact ell.Prime] (E : Type v) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E] (n : ℕ) :
    spEllIdeal ell E ^ (n + 1) = Padic.coefficientExtensionIdeal ell E
      ((emultiplicity (Padic.coefficientExtensionUniformizer ell E)
        (ell : Padic.coefficientExtensionIntegers ell E)).toNat * (n + 1)) := by
  let O := Padic.coefficientExtensionIntegers ell E
  let π := Padic.coefficientExtensionUniformizer ell E
  have h := (Padic.extension_integers_dvr ell E
    (Padic.coefficientExtensionAbsoluteValue ell E)
    (spectralNorm_extends (K := Padic ell) (L := E))).choose_spec.choose_spec
  let : IsDiscreteValuationRing O := h.2.2.2.2.2.2.2.1
  have hgen : Ideal.span ({π} : Set O) =
      Padic.coefficientExtensionMaximalIdeal ell E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hm : Padic.coefficientExtensionMaximalIdeal ell E = IsLocalRing.maximalIdeal O :=
    IsLocalRing.eq_maximalIdeal h.2.2.2.2.1
  have hπ : Irreducible π :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).2 (hm.symm.trans hgen.symm)
  have hell : (ell : O) ≠ 0 := by
    intro heq
    have heq' : (ell : E) = 0 := congrArg (fun x : O ↦ (x : E)) heq
    have hq : (ell : Padic ell) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ell.Prime).ne_zero
    exact hq ((algebraMap (Padic ell) E).injective (by
      simpa only [map_natCast, map_zero] using heq'))
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.associated_pow_irreducible hell hπ
  have he' : (emultiplicity π (ell : O)).toNat = e := by
    rw [emultiplicity_eq_of_associated_right he,
      emultiplicity_pow_self_of_prime (irreducible_iff_prime.mp hπ)]
    rfl
  change Ideal.span ({(ell : O)} : Set O) ^ (n + 1) =
    Ideal.span ({π} : Set O) ^ ((emultiplicity π (ell : O)).toNat * (n + 1))
  rw [he', Ideal.span_singleton_eq_span_singleton.mpr he,
    ← Ideal.span_singleton_pow, ← pow_mul]

end AlgebraicGeometry.ProEtale.OrientationTransport
