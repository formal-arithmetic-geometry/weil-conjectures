/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralAdjunctionBijection
public import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.IntegralOrientationShiftedSheafModels

/-! # Finite reductions detect integral smooth orientation maps

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-gamma.proof.md, clause (1)
(blueprint: lem-pur-integral-orientation-reduction-injectivity).

All natural indices denote the positive exponent n+1. The unit and orientation line
are allowed their full-subcategory representatives, with explicit identifications of
the underlying completed-coefficient derived objects. The comparisons are constructed
from the specified realized adjunction, never chosen from finite component maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpIntegralOrientation

private theorem shifted_single_hom_ext
    {l : ℕ} [Fact l.Prime] {E : Type u} [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] {X : Scheme.{u}}
    (A : SpCoefficientTowersAbelian l E X)
    (L W : spCoefficientTowers l E X) (s : ℤ)
    (f g : ((@DerivedCategory.singleFunctor _ _ _ A.hasDerived 0).obj L)⟦s⟧ ⟶
      ((@DerivedCategory.singleFunctor _ _ _ A.hasDerived 0).obj W)⟦s⟧)
    (h : ∀ n : ℕ, (spDerivedCoefficientEvaluation l E X A n).map f =
      (spDerivedCoefficientEvaluation l E X A n).map g) : f = g := by
  let := A.hasDerived
  let := A.equivalenceAdditive
  let := A.evaluationLimits
  let := A.evaluationColimits
  let S := DerivedCategory.singleFunctor (spCoefficientTowers l E X) 0
  let F := S ⋙ shiftFunctor _ s
  let x : L ⟶ W := F.preimage f
  let y : L ⟶ W := F.preimage g
  have hx : F.map x = f := F.map_preimage f
  have hy : F.map y = g := F.map_preimage g
  have hxy : x = y := by
    apply A.equivalence.functor.map_injective
    apply SheafOfModules.strictRingSystem_hom_ext
    intro n
    let ev := spCoefficientEvaluation l E X A.equivalence n
    have : ev.Additive := Functor.additive_of_preserves_binary_products _
    let e : F ⋙ ev.mapDerivedCategory ≅
        ev ⋙ DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ s :=
      Functor.associator S (shiftFunctor _ s) ev.mapDerivedCategory ≪≫
        Functor.isoWhiskerLeft S (ev.mapDerivedCategory.commShiftIso s) ≪≫
        (Functor.associator S ev.mapDerivedCategory (shiftFunctor _ s)).symm ≪≫
        Functor.isoWhiskerRight (ev.mapDerivedCategorySingleFunctor 0) (shiftFunctor _ s) ≪≫
        Functor.associator ev (DerivedCategory.singleFunctor _ 0) (shiftFunctor _ s)
    change ev.map x = ev.map y
    apply (DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ s).map_injective
    apply (cancel_epi (e.hom.app L)).1
    have hn : ev.mapDerivedCategory.map (F.map x) =
        ev.mapDerivedCategory.map (F.map y) := by
      rw [hx, hy]
      exact h n
    exact (e.hom.naturality x).symm.trans
      ((congrArg (fun z ↦ z ≫ e.hom.app W) hn).trans (e.hom.naturality y))
  rw [← hx, ← hy, hxy]

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {X Z Y : Scheme.{u}}
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)
  (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
  [QuasiCompact (j ≫ p)] [HasCompactification (j ≫ p)]
  (d : ℕ) (w : SpChartAdmissibility.Twists l E X)
  (RX : SpReductionTower l E X (q.abelian X))
  (NX : SpNormalizedEquivalence l E X (q.abelian X) RX)
  (RY : SpReductionTower l E Y (q.abelian Y))
  (NY : SpNormalizedEquivalence l E Y (q.abelian Y) RY)
  (hF : ∀ M : SpTowerCalculus.C l E b q X,
    spConstructibleTorTowers l E Y (q.abelian Y)
      ((SpTowerCalculus.F l E b o q (SpTowerGamma.factorization j p)).obj M.obj))
  (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
  (a : SpTowerGluing.support l E b o q (SpTowerGamma.factorization j p) hF ⊣ G)
  (lv : SpTowerGluing.Levels l E b o q (SpTowerGamma.factorization j p) hF G a)
  (R : SpIntegralAdjunction.Realization l E b o q j p d w RX NX RY NY hF G a lv)

/-- H is the already constructed derived-limit right adjoint with its constructible typing.
Source: integral-adjunction-bijection, Normalization
(blueprint: lem-pur-integral-orientation-reduction-injectivity). -/
abbrev realizedRight :=
  SpIntegralAdjunction.right l E b q RX NX RY R.reductionY G R.closed

/-- The natural integral-to-entire-tower Hom bijection in the displayed orientation.
Source: integral-adjunction-bijection, Bijections
(blueprint: lem-pur-integral-orientation-reduction-injectivity). -/
def beta (M : sfIntegralConstructibleCategory l E X)
    (K : sfIntegralConstructibleCategory l E Y) :
    (M ⟶ (realizedRight l E b o q j p d w RX NX RY NY hF G a lv R).obj K) ≃
      ((SpIntegralAdjunction.reduce l E X (q.abelian X) RX R.reductionX).obj M ⟶
        G.obj ((SpIntegralAdjunction.reduce l E Y (q.abelian Y) RY R.reductionY).obj K)) :=
  R.fullyFaithfulX.homEquiv.trans
    (Iso.homCongr (Iso.refl _) (R.rightComparison.app K))

/-- The counit-preserving comparison from H to any specified integral exceptional adjoint.
Source: unique-right-adjoint, counit equation
(blueprint: lem-pur-integral-orientation-reduction-injectivity). -/
def delta
    (J : sfIntegralConstructibleCategory l E Y ⥤ sfIntegralConstructibleCategory l E X)
    (adjJ : SpIntegralAdjunction.support l E (SpTowerGamma.factorization j p)
      R.support_closed ⊣ J) :
    realizedRight l E b o q j p d w RX NX RY NY hF G a lv R ≅ J :=
  R.adjunction.rightAdjointUniq adjJ

/-- Lambda is beta applied to the identity, including its prescribed whole-tower target.
Source: integral Hom comparison, definition of lambda
(blueprint: lem-pur-integral-orientation-reduction-injectivity). -/
def targetComparison (K : sfIntegralConstructibleCategory l E Y) :=
  beta l E b o q j p d w RX NX RY NY hF G a lv R
    ((realizedRight l E b o q j p d w RX NX RY NY hF G a lv R).obj K) K (𝟙 _)

/-- Ordinary derived reduction, then the fixed H reduction and finite exceptional comparison.
The integral map is arbitrary. Source: definition of rho_n in the node, with the target
identifications from integral-adjunction-bijection
(blueprint: lem-pur-integral-orientation-reduction-injectivity). -/
def rho
    (J : sfIntegralConstructibleCategory l E Y ⥤ sfIntegralConstructibleCategory l E X)
    (adjJ : SpIntegralAdjunction.support l E (SpTowerGamma.factorization j p)
      R.support_closed ⊣ J)
    (M : sfIntegralConstructibleCategory l E X)
    (K : sfIntegralConstructibleCategory l E Y) (h : M ⟶ J.obj K) (n : ℕ) :=
  (spDerivedCoefficientEvaluation l E X (q.abelian X) n).map
      ((SpIntegralAdjunction.reduce l E X (q.abelian X) RX R.reductionX).map
        (h ≫ (delta l E b o q j p d w RX NX RY NY hF G a lv R J adjJ).inv.app K)).hom ≫
    (spDerivedCoefficientEvaluation l E X (q.abelian X) n).map
      (R.rightComparison.hom.app K).hom ≫
    ((lv.comparison n).hom.app
      ((SpIntegralAdjunction.reduce l E Y (q.abelian Y) RY R.reductionY).obj K)).hom

/-- The naturality and evaluation identities for beta, and joint injectivity of all
finite reductions on maps from the shifted integral Tate line to the dualizing object.
Source: latest blueprint tower-geometric gamma proof, clause (1), rank-one uniqueness
(blueprint: lem-pur-integral-orientation-reduction-injectivity).

Proof:
1. Twisted-pullback-reduction-tower at the coefficient unit identifies r_X T with the
entire Tate tower shifted by 2d, including every quotient transition. Tower-gamma (1)
identifies that shifted line with the tower exceptional image of the unit.
2. Naturality in M of integral-adjunction-bijection gives beta(u) = r_X(u) followed by
beta(identity). Exact level evaluation (coefficient-towers-abelian (2)) takes this to
ordinary derived reduction followed by the specified H and finite-adjoint comparisons.
These are exactly rho, including the counit-preserving delta inverse.
3. For maps h,h' with equal rho, use step 2 and cancel the finite target isomorphisms.
Conjugate their tower images by the entire source comparison and diagonal orientation.
Inverse shift by -2d gives endomorphisms of the degree-zero Tate tower with equal levels.
4. The tower category is abelian. Derived-single-fully-faithful lifts both endomorphisms
uniquely to tower sheaf maps; the same result at each finite level makes all components
equal. A strict tower morphism is its family of components, so the tower maps agree.
5. Shift back and cancel the fixed source and orientation isomorphisms. Injectivity of
beta gives equality after delta inverse, and delta gives h=h'. No inverse of h or h'
is used. Empty schemes and d=0 require no separate nonemptiness assumption. -/
theorem reduction_injectivity
    (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (_iE : E →ₐ[Padic l] Ω)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [(j ≫ p).IsOver (Spec (.of D.k))] [SmoothOfRelativeDimension d (j ≫ p)]
    (J : sfIntegralConstructibleCategory l E Y ⥤ sfIntegralConstructibleCategory l E X)
    (adjJ : SpIntegralAdjunction.support l E (SpTowerGamma.factorization j p)
      R.support_closed ⊣ J)
    (T : sfIntegralConstructibleCategory l E X)
    (U : sfIntegralConstructibleCategory l E Y)
    (_hT : T.obj ≅ ((DerivedCategory.singleFunctor _ 0).obj
      (integralTwistLine l E X (d : ℤ)))⟦2 * (d : ℤ)⟧)
    (_hU : U.obj ≅ (DerivedCategory.singleFunctor _ 0).obj
      (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y))) :
    (∀ h : T ⟶ J.obj U,
      beta l E b o q j p d w RX NX RY NY hF G a lv R T U
          (h ≫ (delta l E b o q j p d w RX NX RY NY hF G a lv R J adjJ).inv.app U) =
        (SpIntegralAdjunction.reduce l E X (q.abelian X) RX R.reductionX).map
            (h ≫ (delta l E b o q j p d w RX NX RY NY hF G a lv R J adjJ).inv.app U) ≫
          targetComparison l E b o q j p d w RX NX RY NY hF G a lv R U) ∧
    (∀ (h : T ⟶ J.obj U) (n : ℕ),
      (spDerivedCoefficientEvaluation l E X (q.abelian X) n).map
          (beta l E b o q j p d w RX NX RY NY hF G a lv R T U
            (h ≫ (delta l E b o q j p d w RX NX RY NY hF G a lv R J adjJ).inv.app U)).hom ≫
        ((lv.comparison n).hom.app
          ((SpIntegralAdjunction.reduce l E Y (q.abelian Y) RY R.reductionY).obj U)).hom =
        rho l E b o q j p d w RX NX RY NY hF G a lv R J adjJ T U h n) ∧
    Function.Injective (fun h : T ⟶ J.obj U ↦
      fun n : ℕ ↦ rho l E b o q j p d w RX NX RY NY hF G a lv R J adjJ T U h n) := by
  have hb (M : sfIntegralConstructibleCategory l E X)
      (K : sfIntegralConstructibleCategory l E Y)
      (v : M ⟶ (realizedRight l E b o q j p d w RX NX RY NY hF G a lv R).obj K) :
      beta l E b o q j p d w RX NX RY NY hF G a lv R M K v =
        (SpIntegralAdjunction.reduce l E X (q.abelian X) RX R.reductionX).map v ≫
          R.rightComparison.hom.app K := by
    simp only [beta, Equiv.trans_apply, Functor.FullyFaithful.homEquiv_apply,
      Iso.homCongr_apply, Iso.refl_inv, Iso.app_hom, Category.id_comp]
  have heval (h : T ⟶ J.obj U) (n : ℕ) :
      (spDerivedCoefficientEvaluation l E X (q.abelian X) n).map
          (beta l E b o q j p d w RX NX RY NY hF G a lv R T U
            (h ≫ (delta l E b o q j p d w RX NX RY NY hF G a lv R J adjJ).inv.app U)).hom ≫
        ((lv.comparison n).hom.app
          ((SpIntegralAdjunction.reduce l E Y (q.abelian Y) RY R.reductionY).obj U)).hom =
        rho l E b o q j p d w RX NX RY NY hF G a lv R J adjJ T U h n := by
    rw [hb]
    dsimp only [rho]
    rw [ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp, Category.assoc]
  refine ⟨?_, heval, ?_⟩
  · intro h
    rw [hb]
    dsimp only [targetComparison]
    rw [hb, CategoryTheory.Functor.map_id, Category.id_comp]
  · obtain ⟨L, W, ⟨eT⟩, ⟨eV⟩⟩ := shifted_sheaf_models
      l E b o q j p d w RX NX RY NY hF G a lv R D _hl Ω _iE T U _hT _hU
    intro h h' he
    apply (cancel_mono
      ((delta l E b o q j p d w RX NX RY NY hF G a lv R J adjJ).inv.app U)).1
    apply (beta l E b o q j p d w RX NX RY NY hF G a lv R T U).injective
    apply ObjectProperty.hom_ext
    apply (cancel_epi eT.inv).1
    apply (cancel_mono eV.hom).1
    apply shifted_single_hom_ext (q.abelian X) L W (2 * (d : ℤ))
    intro n
    have hv :
        (spDerivedCoefficientEvaluation l E X (q.abelian X) n).map
            (beta l E b o q j p d w RX NX RY NY hF G a lv R T U
              (h ≫ (delta l E b o q j p d w RX NX RY NY hF G a lv R J adjJ).inv.app U)).hom =
          (spDerivedCoefficientEvaluation l E X (q.abelian X) n).map
            (beta l E b o q j p d w RX NX RY NY hF G a lv R T U
              (h' ≫ (delta l E b o q j p d w RX NX RY NY hF G a lv R J adjJ).inv.app U)).hom := by
      apply (cancel_mono (((lv.comparison n).hom.app
        ((SpIntegralAdjunction.reduce l E Y (q.abelian Y) RY R.reductionY).obj U)).hom)).1
      exact (heval h n).trans ((congrFun he n).trans (heval h' n).symm)
    simp only [Functor.map_comp]
    rw [hv]

end AlgebraicGeometry.ProEtale.SpIntegralOrientation
