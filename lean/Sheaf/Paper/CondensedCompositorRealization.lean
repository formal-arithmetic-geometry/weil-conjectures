/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.CompactSupportCondensedRealization
public import Sheaf.Paper.CompactSupportRealizationFactorization
public import Sheaf.Paper.TowerAdjointCompositorRealization
public import Sheaf.Paper.EtaleProEtaleCoefficientCompatibility
public import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
public import Sheaf.Paper.FiniteAdjointCompositorTransposes
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import Sheaf.Paper.CondensedERealization
import all Sheaf.Paper.SystemProperOpenInvertibility
import all Sheaf.Paper.ProEtaleConstantModuleConstructibility
import Sheaf.Paper.ProEtaleFiniteModelLocalConstancy
import Sheaf.Paper.ProEtaleFiniteModelStalks

/-! # Condensed realization of the specified compact-support compositor

Source: latest blueprint, smooth-purity composition, Towers and coefficient transport;
the agent comparison supplement in the DAG proof.
(blueprint: lem-pur-condensed-compositor-realization).

All system maps are maps in the ordinary derived category of the ringed sequence site.
The integral compositor inserts the actual reduction/limit counit. The condensed
compositor is the archived one, conjugated by the canonical compactification comparisons.

## Main definitions and statement

- `integralCompositor`: the specified five-arrow integral composite.
- `comparison`: rational realization followed by the original Omega projection.
- `condensedCompositor`: the transported inverse archived compositor.
- `condensedCompositorRealization`: the composition square and its coherence laws.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
attribute [local irreducible] HasDerivedCategory.standard
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Mod.monoidalCategory
  CategoryTheory.Sheaf.monoidalCategory

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open scoped CategoryTheory.Obj
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open WeilConjectures.CompactSupportCondensedRealization

namespace WeilConjectures.CondensedCompositorRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]

/-- The existing integral uniform finite-Tor predicate in the published completed
coefficient coordinates. Its constructibility part contains one common cohomology
window, and its Tor interval tests every degree-zero module sheaf at every level.
Source: blueprint composition, Towers; finite-Tor amplitude, order 1464
(blueprint: lem-pur-condensed-compositor-realization). -/
def Uniform (X : CondensedERealization.Base k)
    (K : CondensedERealization.Integral l E X.scheme) : Prop :=
  finiteTorConstructibleIntegral l E X.scheme
    ((purCoefficientModel l E X.scheme).functor.obj K.obj)

/-- The already recorded total-limit compact-support functor, with its actual model.
Source: blueprint transport, Steps 2--3
(blueprint: lem-pur-condensed-compositor-realization). -/
abbrev P (A : CoefficientData l E k) (X Y : CondensedERealization.Base k)
    (f : X.scheme ⟶ Y.scheme) [f.IsOver (Spec (.of k))] (c : Compactification f) :=
  integralSupport l E c A.reduction (A.atCompactification X Y f c).integral

/-- The specified reduction/limit adjunct of beta, in completed coefficient coordinates.
Source: the displayed definition of delta in the item's statement
(blueprint: lem-pur-condensed-compositor-realization). -/
def delta (A : CoefficientData l E k) (X Y : CondensedERealization.Base k)
    (f : X.scheme ⟶ Y.scheme) [f.IsOver (Spec (.of k))] (c : Compactification f)
    (K : CondensedERealization.Integral l E X.scheme) :=
  (A.reduction Y.scheme).adjunction.unit.app
      ((purCoefficientModel l E Y.scheme).functor.obj ((P l E k A X Y f c).obj K).obj) ≫
    (coefficientSequenceLimit l E Y.scheme).map
      ((alpha l E c A.reduction (A.atCompactification X Y f c).integral).app K)

private theorem unit_map_counit
    {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C}
    (a : F ⊣ G) {V : C} {W : D} (v : V ⟶ G.obj W) :
    a.unit.app V ≫ G.map (F.map v ≫ a.counit.app W) = v := by
  rw [Functor.map_comp, ← Category.assoc, a.unit_naturality v,
    Category.assoc, a.right_triangle_components W, Category.comp_id]

/-- Delta is invertible on the integral category.
Source: the item's proof, Steps 2--3
(blueprint: lem-pur-condensed-compositor-realization).
Proof: beta is the actual reduction/limit counit after the limit-presentation iso.
The adjunction triangle cancels the unit followed by the limit of that counit;
the remaining map is exactly limitPresentation, hence invertible. -/
theorem delta_isIso (A : CoefficientData l E k) (X Y : CondensedERealization.Base k)
    (f : X.scheme ⟶ Y.scheme) [f.IsOver (Spec (.of k))] (c : Compactification f)
    (K : CondensedERealization.Integral l E X.scheme) :
    IsIso (delta l E k A X Y f c K) := by
  have h : delta l E k A X Y f c K =
      (limitPresentation l E c A.reduction
        (A.atCompactification X Y f c).integral).hom.app K := by
    unfold delta alpha
    dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    exact unit_map_counit (A.reduction Y.scheme).adjunction
      ((limitPresentation l E c A.reduction
        (A.atCompactification X Y f c).integral).hom.app K)
  rw [h]
  infer_instance

/-- A compatible compactification tower gives its literal composite compactification.
Source: blueprint composition, Towers; Compactification.overComp
(blueprint: lem-pur-condensed-compositor-realization). -/
abbrev composite (X Y Z : CondensedERealization.Base k)
    (f : X.scheme ⟶ Y.scheme) (g : Y.scheme ⟶ Z.scheme)
    [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
    (cf : Compactification f) (cg : Compactification g)
    (d : Compactification (cf.g ≫ cg.i)) : Compactification (f ≫ g) :=
  Compactification.overComp (f := CondensedERealization.Base.map X Y f)
    (g := CondensedERealization.Base.map Y Z g) cf cg d

/-- The actual strict-system proper/open word for a compatible tower. Its interchange
is the intrinsic mate gamma; its other factors are the open and proper compositors.
Source: blueprint composition, Towers; the item's proof, Step 3
(blueprint: lem-pur-condensed-compositor-realization). -/
def systemTower (X Y Z : CondensedERealization.Base k)
    (f : X.scheme ⟶ Y.scheme) (g : Y.scheme ⟶ Z.scheme)
    [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
    (cf : Compactification f) (cg : Compactification g)
    (d : Compactification (cf.g ≫ cg.i)) :
    systemSupport l E cf ⋙ systemSupport l E cg ⟶
      systemSupport l E (composite k X Y Z f g cf cg d) :=
  letI := compactification_open_quasiCompact k X Y f cf
  letI := compactification_open_quasiCompact k Y Z g cg
  letI : IsNoetherian d.Z := base_noetherian k ⟨d.Z⟩
  letI : QuasiCompact d.i := inferInstance
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (Functor.associator _ _ _).inv ≫
    Functor.whiskerLeft _
      (Functor.whiskerRight
        (SemilinearProperOpen.gamma (quotientRings l E) (quotientMaps l E)
          d.i cf.g d.g cg.i d.comm.symm) _) ≫
    Functor.whiskerLeft _ (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _
      (Functor.whiskerLeft _
        (SemilinearProperOpen.sComp (quotientRings l E) (quotientMaps l E) d.g cg.g).hom) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (SemilinearProperOpen.jComp (quotientRings l E) (quotientMaps l E) cf.i d.i).hom _

attribute [local irreducible] systemTower systemRefinement

/-- An isomorphism presenting the specified whole-system refinement component.
Source: the item's proof, Step 3 (blueprint: lem-pur-condensed-compositor-realization).
The hom equality pins all the data: Iso.ext identifies any two such isomorphisms.
This record keeps that large equality out of the type of the inverse operation. -/
structure RefinementIso (A : CoefficientData l E k) (X Y : CondensedERealization.Base k)
    (f : X.scheme ⟶ Y.scheme) [f.IsOver (Spec (.of k))]
    {c d : Compactification f} (r : c.Refinement d)
    (K : CondensedERealization.Integral l E X.scheme) where
  iso :
    (systemSupport l E d).obj
        ((integralReduction l E k X (A.reduction X.scheme)).obj K) ≅
      (systemSupport l E c).obj
        ((integralReduction l E k X (A.reduction X.scheme)).obj K)
  hom_eq : iso.hom = (systemRefinement l E k X Y f r).app
    ((integralReduction l E k X (A.reduction X.scheme)).obj K)

/-- A normalized refinement paste preserves invertibility of its mate component.
Source: the parent's Step 3 (blueprint: lem-pur-condensed-compositor-realization).
Proof: apply the outside functor to the invertible component and compose with
the functor associator and the component of the given proper compositor. -/
private theorem pasteRefinement_component_isIso
    {C D S T : Type*} [Category C] [Category D] [Category S] [Category T]
    (jd : C ⥤ S) (jc : C ⥤ D) (r : D ⥤ S) (g : S ⥤ T) (h : D ⥤ T)
    (F : C ⥤ C) (e : F ≅ 𝟭 C) (a : F ⋙ jd ⟶ jc ⋙ r)
    (b : r ⋙ g ≅ h) (M : C) (ha : IsIso (a.app M)) :
    IsIso ((pasteRefinement jd jc r g h
      ((Functor.leftUnitor jd).inv ≫ Functor.whiskerRight e.inv jd ≫ a) b).app M) := by
  let := ha
  dsimp only [pasteRefinement, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  infer_instance

/-- Uniform integral reductions have bounded-below finite etale origins after the
constant-diagram presentation used by semilinear proper/open calculus.
Source: Stacks 09AL, lemma-compare-constructible-derived; the parent's Step 3
(blueprint: lem-pur-condensed-compositor-realization).
Proof: the constructibility clause gives bounded constructible cohomology for every
actual scalar reduction. The reductionEvaluation isomorphism identifies evaluation
of the supplied reduction functor with that scalar extension. The finite-ring
constructible derived origin theorem supplies a bounded etale complex and its
comparison isomorphism. Lift the quotient ring to the site universe and restrict
scalars along the canonical constant-section map to obtain ScalarEtaleOrigin.
Evaluation of the constant diagram at any index is the original finite complex,
so transport the same witness through the exact derived composition comparisons.
Only existence of origins is asserted; no equality of system maps is detected by
finite evaluation. Empty schemes and zero complexes use their zero etale origin. -/
private theorem uniformReduction_etaleOrigins (l : ℕ) [Fact l.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (M : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (_hM : finiteTorConstructibleIntegral l E X M) (n q : ℕ) :
    Nonempty (ProEtale.StrictTower.ScalarEtaleOrigin (quotientRings l E n) X
      ((ProEtale.StrictTower.ev (quotientRings l E n) X q).obj
        ((ProEtale.SemilinearProperOpen.E (quotientRings l E) (quotientMaps l E) n X).obj
          (S.reduction.obj M)))) := by
  classical
  let A := Padic.coefficientExtensionRing l E (n + 1)
  have : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  let Q := (scalarReductionDerivedExtension.{u, u} l E X n).obj M
  obtain ⟨a, b, hab, hlevels⟩ := _hM.1.2
  have hc (i : ℤ) : IsConstructibleProEtaleFixedModuleSheaf X
      (ULift.{u + 1, u} A) ((proEtaleModuleRestriction X A).obj
        ((DerivedCategory.homologyFunctor _ i).obj Q)) := by
    have h := (proEtaleModuleRestriction_constructible_iff X A _).mp
      ((hlevels n).1.2 i)
    obtain ⟨S, hn, hS⟩ := positive_stratification X (ULift.{u + 1, u} A) _ h
    refine ⟨S, hn, S.isConstructible_stratum, fun j ↦ ?_⟩
    obtain ⟨I, U, f, hf, hmodels⟩ := ProEtale.finiteModels_over _ _ (hS j)
    refine ⟨⟨I, U, f, hf, fun t ↦ ?_⟩, ?_⟩
    · obtain ⟨N, _, hN⟩ := hmodels t
      exact ⟨N, hN⟩
    · intro Ω _ _ x
      exact ProEtale.finite_geometricStalk_of_finite_models _ _ (hS j) Ω x
  have hz (i : ℤ) (hi : i < a ∨ b < i) :
      CategoryTheory.Limits.IsZero ((DerivedCategory.homologyFunctor _ i).obj Q) := by
    by_contra hn
    have hbound := (hlevels n).2 hn
    rcases hi with hi | hi
    · exact (not_lt_of_ge hbound.1) hi
    · exact (not_lt_of_ge hbound.2) hi
  obtain ⟨w, _, _⟩ := ProEtale.SemilinearProperOpen.scalar_origin X A Q hc
    ⟨a, b, hab, hz⟩
  let := coefficientSequenceEvaluation_additiveInstance.{u, u} l E X n
  let := coefficientSequenceEvaluation_limits.{u, u} l E X n
  let := coefficientSequenceEvaluation_colimits.{u, u} l E X n
  let ev := ProEtale.SemilinearProperOpen.levelTower (quotientRings l E) (quotientMaps l E) n X
  let d : ProEtale.SemilinearProperOpen.E (quotientRings l E) (quotientMaps l E) n X ⋙
      ProEtale.StrictTower.ev (quotientRings l E n) X q ≅
        coefficientSequenceDerivedEvaluation l E X n :=
    (Functor.mapDerivedCategoryCompIso ev
      ((CategoryTheory.evaluation ℕᵒᵖ (ProEtale.StrictTower.Modules (quotientRings l E n) X)).obj
        (Opposite.op q))).symm ≪≫ Functor.mapDerivedCategoryNatIso (Iso.refl _)
  let e : (ProEtale.StrictTower.ev (quotientRings l E n) X q).obj
      ((ProEtale.SemilinearProperOpen.E (quotientRings l E) (quotientMaps l E) n X).obj
        (S.reduction.obj M)) ≅ Q :=
    d.app (S.reduction.obj M) ≪≫ (S.reductionEvaluation n).app M
  exact ⟨{ w with iso := w.iso ≪≫ e.symm }⟩

/-- The actual semilinear mate is invertible on finite etale-origin inputs.
Source: Stacks 0F7B; the parent's Step 3
(blueprint: lem-pur-condensed-compositor-realization).
Proof: gamma_evaluation compares each evaluated mate with the strict-tower mate,
and both intervening direct-image and open comparisons are isomorphisms.
Strict-tower invertibility and joint detection of isomorphisms give the result. -/
private theorem semilinear_gamma_isIso
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
    {V W S T : Scheme.{u}} (j : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion j] [IsOpenImmersion i]
    [QuasiCompact j] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : j ≫ p = r ≫ i) (M : SemilinearProperOpen.Derived C τ V)
    (hM : ∀ n q : ℕ, Nonempty (StrictTower.ScalarEtaleOrigin (C n) V
      ((StrictTower.ev (C n) V q).obj ((SemilinearProperOpen.E C τ n V).obj M)))) :
    IsIso ((SemilinearProperOpen.gamma C τ j r p i h).app M) := by
  apply SemilinearProperOpen.system_isIso_of_evaluations C τ T
  intro n
  let := SemilinearProperOpen.evalR_isIso C τ n p
  let := SemilinearProperOpen.evalR_isIso C τ n r
  let := StrictTower.gamma_isIso (C n) j r p i h
    ((SemilinearProperOpen.E C τ n V).obj M) (hM n)
  have he := SemilinearProperOpen.gamma_evaluation C τ n j r p i h M
  have hi : IsIso ((SemilinearProperOpen.E C τ n T).map
      ((SemilinearProperOpen.gamma C τ j r p i h).app M) ≫
      (SemilinearProperOpen.evalR C τ n p).app ((SemilinearProperOpen.J C τ j).obj M) ≫
      (StrictTower.R (C n) p).map ((SemilinearProperOpen.evalJ C τ n j).hom.app M)) := by
    rw [he]
    infer_instance
  have hi' : IsIso ((SemilinearProperOpen.E C τ n T).map
      ((SemilinearProperOpen.gamma C τ j r p i h).app M)) :=
    IsIso.of_isIso_comp_right _
      ((SemilinearProperOpen.evalR C τ n p).app ((SemilinearProperOpen.J C τ j).obj M) ≫
        (StrictTower.R (C n) p).map ((SemilinearProperOpen.evalJ C τ n j).hom.app M))
  change IsIso ((StrictTower.ev (C n) T 0).map
    ((SemilinearProperOpen.E C τ n T).map
      ((SemilinearProperOpen.gamma C τ j r p i h).app M)))
  infer_instance

/-- Apply the origin criterion to the specified reduction functor.
Source: the parent's Step 3 (blueprint: lem-pur-condensed-compositor-realization).
Proof: the preceding origin witnesses satisfy the generic semilinear mate criterion. -/
private theorem reduction_gamma_isIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {V W S T : Scheme.{u}}
    (j : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion j] [IsOpenImmersion i] [QuasiCompact j] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : j ≫ p = r ≫ i)
    (R : CoefficientDerivedSystemCalculus.{u, u} l E V)
    (M : DerivedCategory (scalarReductionSource.{u, u} l E V))
    (hM : finiteTorConstructibleIntegral l E V M) :
    IsIso ((SemilinearProperOpen.gamma (quotientRings l E) (quotientMaps l E)
      j r p i h).app (R.reduction.obj M)) := by
  exact semilinear_gamma_isIso (quotientRings l E) (quotientMaps l E)
    j r p i h (R.reduction.obj M) (uniformReduction_etaleOrigins l E V R M hM)

omit [Fact (ringChar k ≠ l)] in
/-- Unfold the specified refinement as its normalized proper/open paste.
Source: the parent's Step 3 (blueprint: lem-pur-condensed-compositor-realization).
Proof: this is the defining formula of systemRefinement. -/
private theorem systemRefinement_eq (X Y : CondensedERealization.Base k)
    (f : X.scheme ⟶ Y.scheme) [f.IsOver (Spec (.of k))]
    {c d : Compactification f} (r : c.Refinement d)
    [QuasiCompact c.i] [QuasiCompact d.i] :
    systemRefinement l E k X Y f r =
      (pasteRefinement
        (SemilinearProperOpen.J (quotientRings l E) (quotientMaps l E) d.i)
        (SemilinearProperOpen.J (quotientRings l E) (quotientMaps l E) c.i)
        (SemilinearProperOpen.R (quotientRings l E) (quotientMaps l E) r.hom)
        (SemilinearProperOpen.R (quotientRings l E) (quotientMaps l E) d.g)
        (SemilinearProperOpen.R (quotientRings l E) (quotientMaps l E) c.g)
        ((Functor.leftUnitor _).inv ≫
          Functor.whiskerRight
            (SemilinearProperOpen.sId (quotientRings l E) (quotientMaps l E) X.scheme).inv
            (SemilinearProperOpen.J (quotientRings l E) (quotientMaps l E) d.i) ≫
          SemilinearProperOpen.gamma (quotientRings l E) (quotientMaps l E)
            c.i (𝟙 X.scheme) r.hom d.i (r.i_hom.trans (Category.id_comp _).symm))
        (SemilinearProperOpen.sComp (quotientRings l E) (quotientMaps l E) r.hom d.g ≪≫
          eqToIso (congrArg (SemilinearProperOpen.R (quotientRings l E) (quotientMaps l E))
            r.hom_g))) := by
  unfold systemRefinement
  dsimp only [id]

omit [Fact (ringChar k ≠ l)] in
/-- The normalized refinement is invertible whenever its mate component is.
Source: the parent's Step 3 (blueprint: lem-pur-condensed-compositor-realization).
Proof: its other factors are identity, proper-composition and equality isomorphisms. -/
private theorem systemRefinement_component_isIso (X Y : CondensedERealization.Base k)
    (f : X.scheme ⟶ Y.scheme) [f.IsOver (Spec (.of k))]
    {c d : Compactification f} (r : c.Refinement d)
    (M : coefficientSequenceDerived.{u, u} l E X.scheme)
    [QuasiCompact c.i] [QuasiCompact d.i]
    (hM : IsIso ((SemilinearProperOpen.gamma (quotientRings l E) (quotientMaps l E)
      c.i (𝟙 X.scheme) r.hom d.i (r.i_hom.trans (Category.id_comp _).symm)).app M)) :
    IsIso ((systemRefinement l E k X Y f r).app M) := by
  rw [systemRefinement_eq l E k X Y f r]
  exact pasteRefinement_component_isIso
    (SemilinearProperOpen.J (quotientRings l E) (quotientMaps l E) d.i)
    (SemilinearProperOpen.J (quotientRings l E) (quotientMaps l E) c.i)
    (SemilinearProperOpen.R (quotientRings l E) (quotientMaps l E) r.hom)
    (SemilinearProperOpen.R (quotientRings l E) (quotientMaps l E) d.g)
    (SemilinearProperOpen.R (quotientRings l E) (quotientMaps l E) c.g)
    (SemilinearProperOpen.R (quotientRings l E) (quotientMaps l E) (𝟙 X.scheme))
    (SemilinearProperOpen.sId (quotientRings l E) (quotientMaps l E) X.scheme)
    (SemilinearProperOpen.gamma (quotientRings l E) (quotientMaps l E)
      c.i (𝟙 X.scheme) r.hom d.i (r.i_hom.trans (Category.id_comp _).symm))
    (SemilinearProperOpen.sComp (quotientRings l E) (quotientMaps l E) r.hom d.g ≪≫
      eqToIso (congrArg (SemilinearProperOpen.R (quotientRings l E) (quotientMaps l E))
        r.hom_g)) M hM

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)] in
/-- Evaluate the specified three-factor integral reduction at an integral object.
Source: the parent's Step 3 (blueprint: lem-pur-condensed-compositor-realization).
Proof: unfold integralReduction and the composite functor's object map. -/
private theorem integralReduction_obj_eq (X : CondensedERealization.Base k)
    (R : CoefficientDerivedSystemCalculus.{u, u} l E X.scheme)
    (K : CondensedERealization.Integral l E X.scheme) :
    (integralReduction l E k X R).obj K =
      R.reduction.obj ((purCoefficientModel l E X.scheme).functor.obj K.obj) := by
  unfold integralReduction
  rfl

/-- Normalize the integral reduction object before applying the mate criterion.
Source: the parent's Step 3 (blueprint: lem-pur-condensed-compositor-realization).
Proof: unfold the three-factor integral reduction and apply reduction_gamma_isIso. -/
private theorem integral_reduction_gamma_isIso (A : CoefficientData l E k)
    (X Y : CondensedERealization.Base k) (f : X.scheme ⟶ Y.scheme)
    [f.IsOver (Spec (.of k))] {c d : Compactification f} (r : c.Refinement d)
    [QuasiCompact c.i] [QuasiCompact d.i]
    (K : CondensedERealization.Integral l E X.scheme) (hK : Uniform l E k X K) :
    IsIso ((SemilinearProperOpen.gamma (quotientRings l E) (quotientMaps l E)
      c.i (𝟙 X.scheme) r.hom d.i (r.i_hom.trans (Category.id_comp _).symm)).app
        ((integralReduction l E k X (A.reduction X.scheme)).obj K)) := by
  rw [integralReduction_obj_eq l E k X (A.reduction X.scheme) K]
  unfold Uniform at hK
  exact reduction_gamma_isIso l E c.i (𝟙 X.scheme) r.hom d.i
    (r.i_hom.trans (Category.id_comp _).symm) (A.reduction X.scheme)
    ((purCoefficientModel l E X.scheme).functor.obj K.obj) hK

/-- Package an invertible specified refinement component, preserving its hom.
Source: the parent's Step 3 (blueprint: lem-pur-condensed-compositor-realization).
Proof: use asIso and its definitional hom equation. -/
private theorem refinementIso_of_isIso (A : CoefficientData l E k)
    (X Y : CondensedERealization.Base k) (f : X.scheme ⟶ Y.scheme)
    [f.IsOver (Spec (.of k))] {c d : Compactification f} (r : c.Refinement d)
    (K : CondensedERealization.Integral l E X.scheme)
    (hi : IsIso ((systemRefinement l E k X Y f r).app
      ((integralReduction l E k X (A.reduction X.scheme)).obj K))) :
    Nonempty (RefinementIso l E k A X Y f r K) := by
  exact ⟨⟨asIso ((systemRefinement l E k X Y f r).app
    ((integralReduction l E k X (A.reduction X.scheme)).obj K)), rfl⟩⟩

/-- A normalized whole-system refinement is invertible on the uniform reductions.
Source: the item's proof, Step 3
(blueprint: lem-pur-condensed-compositor-realization).
Proof: uniform constructibility gives bounded constructible finite reductions.
Their scalar etale origins transfer through reductionEvaluation and the exact
derived constant-diagram comparison. The gamma_evaluation identity then compares
the intrinsic refinement mate with the constant finite-ring tower mate.
Strict-tower proper/open calculus makes its evaluations invertible. Evaluations
detect isomorphisms in the ordinary derived system category. This uses detection
of isomorphisms, never faithfulness of evaluations on derived morphisms.
Package the resulting isomorphism with its hom equal to the specified refinement
component. Iso.ext makes this package unique, including its inverse. -/
theorem refinementIso_exists (A : CoefficientData l E k) (X Y : CondensedERealization.Base k)
    (f : X.scheme ⟶ Y.scheme) [f.IsOver (Spec (.of k))]
    {c d : Compactification f} (r : c.Refinement d)
    (K : CondensedERealization.Integral l E X.scheme) (_hK : Uniform l E k X K) :
    Nonempty (RefinementIso l E k A X Y f r K) := by
  let := compactification_open_quasiCompact k X Y f c
  let := compactification_open_quasiCompact k X Y f d
  have hM := integral_reduction_gamma_isIso l E k A X Y f r K _hK
  have hi := systemRefinement_component_isIso l E k X Y f r
    ((integralReduction l E k X (A.reduction X.scheme)).obj K) hM
  exact refinementIso_of_isIso l E k A X Y f r K hi

/-- The unique inverse of the specified normalized refinement component.
Source: the item's proof, Step 3 (blueprint: lem-pur-condensed-compositor-realization).
The selected iso has hom exactly equal to systemRefinement, so Iso.ext determines
its inverse uniquely; no independently supplied compactification map is selected. -/
def refinementInverse (A : CoefficientData l E k) (X Y : CondensedERealization.Base k)
    (f : X.scheme ⟶ Y.scheme) [f.IsOver (Spec (.of k))]
    {c d : Compactification f} (r : c.Refinement d)
    (K : CondensedERealization.Integral l E X.scheme) (hK : Uniform l E k X K) :
    (systemSupport l E c).obj
        ((integralReduction l E k X (A.reduction X.scheme)).obj K) ⟶
      (systemSupport l E d).obj
        ((integralReduction l E k X (A.reduction X.scheme)).obj K) :=
  (Classical.choice (refinementIso_exists l E k A X Y f (c := c) (d := d) r K hK)).iso.inv

/-- The strict-system compositor, with the two specified refinement factors. Both
maps used in the inverse are whole-system maps, before taking any total limit.
Source: the item's proof, Step 3; canonical compactification comparisons
(blueprint: lem-pur-condensed-compositor-realization). -/
def systemCompositor (A : CoefficientData l E k) (X Y Z : CondensedERealization.Base k)
    (f : X.scheme ⟶ Y.scheme) (g : Y.scheme ⟶ Z.scheme)
    [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
    (cf : Compactification f) (cg : Compactification g)
    (ch : Compactification (f ≫ g)) (d : Compactification (cf.g ≫ cg.i))
    (c : Compactification (f ≫ g))
    (r : c.Refinement (composite k X Y Z f g cf cg d)) (s : c.Refinement ch)
    (K : CondensedERealization.Integral l E X.scheme) (hK : Uniform l E k X K) :
    (systemSupport l E cg).obj ((systemSupport l E cf).obj
      ((integralReduction l E k X (A.reduction X.scheme)).obj K)) ⟶
    (systemSupport l E ch).obj
      ((integralReduction l E k X (A.reduction X.scheme)).obj K) :=
  (systemTower l E k X Y Z f g cf cg d).app
      ((integralReduction l E k X (A.reduction X.scheme)).obj K) ≫
    (systemRefinement l E k X Z (f ≫ g) r).app
      ((integralReduction l E k X (A.reduction X.scheme)).obj K) ≫
    refinementInverse l E k A X Z (f ≫ g) s K hK

/-- The five-arrow integral compositor, literally in the order in the statement:
delta_g, L F_g R(delta_f), L F_g(e), L(alpha_bullet), delta_h inverse.
Source: the displayed definition of alpha_R in the item
(blueprint: lem-pur-condensed-compositor-realization). -/
def integralCompositor (A : CoefficientData l E k) (X Y Z : CondensedERealization.Base k)
    (f : X.scheme ⟶ Y.scheme) (g : Y.scheme ⟶ Z.scheme)
    [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
    (cf : Compactification f) (cg : Compactification g)
    (ch : Compactification (f ≫ g)) (d : Compactification (cf.g ≫ cg.i))
    (c : Compactification (f ≫ g))
    (r : c.Refinement (composite k X Y Z f g cf cg d)) (s : c.Refinement ch)
    (K : CondensedERealization.Integral l E X.scheme) (hK : Uniform l E k X K) :
    (P l E k A Y Z g cg).obj ((P l E k A X Y f cf).obj K) ⟶
      (P l E k A X Z (f ≫ g) ch).obj K :=
  ObjectProperty.homMk ((purCoefficientModel l E Z.scheme).fullyFaithfulFunctor.preimage
    (delta l E k A Y Z g cg ((P l E k A X Y f cf).obj K) ≫
      (coefficientSequenceLimit l E Z.scheme).map ((systemSupport l E cg).map
        ((A.reduction Y.scheme).reduction.map (delta l E k A X Y f cf K))) ≫
      (coefficientSequenceLimit l E Z.scheme).map ((systemSupport l E cg).map
        ((A.reduction Y.scheme).adjunction.counit.app
          ((systemSupport l E cf).obj
            ((integralReduction l E k X (A.reduction X.scheme)).obj K)))) ≫
      (coefficientSequenceLimit l E Z.scheme).map
        (systemCompositor l E k A X Y Z f g cf cg ch d c r s K hK) ≫
      inv (I := delta_isIso l E k A X Z (f ≫ g) ch K)
        (delta l E k A X Z (f ≫ g) ch K)))

/-- Rational realization followed by the actual finite-valued-closure scalar extension.
Source: the item's definition of U; the two-colimit coefficient convention
(blueprint: lem-pur-condensed-compositor-realization). -/
def U (A : CoefficientData l E k) (a : E →ₐ[ℚ_[l]] PadicAlgCl l)
    (X : CondensedERealization.Base k) :
    CondensedERealization.Integral l E X.scheme ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology X.scheme) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj l) X.scheme)) :=
  pbcRationalization X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E) ⋙
    (A.realization.atObject X).realization.functor ⋙
      (boundedConstructible (CondensedERealization.Coefficient E X.scheme)).ι ⋙
        omegaScalar l E a X.scheme

/-- The specified comparison a: the rational compact-support comparison followed by
the original E-to-Omega proper/open projection, with no independently supplied arrow.
Source: the item's definition of a; compact-support realization, proof Step 5
(blueprint: lem-pur-condensed-compositor-realization). -/
def comparison (A : CoefficientData l E k) (a : E →ₐ[ℚ_[l]] PadicAlgCl l)
    (X Y : CondensedERealization.Base k) (f : X.scheme ⟶ Y.scheme)
    [f.IsOver (Spec (.of k))] (c : Compactification f)
    (K : CondensedERealization.Integral l E X.scheme) :=
  (omegaScalar l E a Y.scheme).map
      ((A.atCompactification X Y f c).realization.hom.app (ScalarLocalization.mk K)) ≫
    (condensedProjection (omegaMap l E a) c).app
      ((A.realization.atObject X).realization.functor.obj (ScalarLocalization.mk K)).obj

/-- Realization lands in the archived bounded constructible Omega category.
Source: the item's coefficient paragraph; compact-support realization, Step 13
(blueprint: lem-pur-condensed-compositor-realization).
Proof: J has constructible target, and extension to the finite-valued algebraic
closure preserves constructibility by descent to a common finite subextension. -/
theorem U_constructible (A : CoefficientData l E k) (a : E →ₐ[ℚ_[l]] PadicAlgCl l)
    (X : CondensedERealization.Base k) (K : CondensedERealization.Integral l E X.scheme) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l) X.scheme)
      ((U l E k A a X).obj K) := by
  exact omegaScalar_preserves l E a X.scheme
    ((A.realization.atObject X).realization.functor.obj (ScalarLocalization.mk K))

/-- The archived condensed compositor transported to the three supplied compactifications.
Source: ShriekComposition, boundedConstructibleLowerShriekComp_padicAlgCl;
the item's exact-map clause (blueprint: lem-pur-condensed-compositor-realization). -/
def condensedCompositor (X Y Z : CondensedERealization.Base k)
    (f : X.scheme ⟶ Y.scheme) (g : Y.scheme ⟶ Z.scheme)
    [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
    (cf : Compactification f) (cg : Compactification g)
    (ch : Compactification (f ≫ g)) :=
  Functor.isoWhiskerRight
      (CondensedRing.boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl l
        (f := CondensedERealization.Base.map X Y f) cf
        (CondensedRing.compactificationOverField (CondensedERealization.Base.map X Y f)))
      (CondensedRing.boundedConstructibleLowerShriekOfCompactification
        (Profinite.padicAlgClRingObj l) l
        (f := CondensedERealization.Base.map Y Z g) cg) ≪≫
    Functor.isoWhiskerLeft _
      (CondensedRing.boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl l
        (f := CondensedERealization.Base.map Y Z g) cg
        (CondensedRing.compactificationOverField (CondensedERealization.Base.map Y Z g))) ≪≫
    (CondensedRing.boundedConstructibleLowerShriekComp_padicAlgCl l
      (CondensedERealization.Base.map X Y f) (CondensedERealization.Base.map Y Z g)).symm ≪≫
    CondensedRing.boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl l
      (f := CondensedERealization.Base.map X Z (f ≫ g))
      (CondensedRing.compactificationOverField
        (CondensedERealization.Base.map X Z (f ≫ g))) ch

/-- The identity-proper-factor identification for an open arrow is the archived
adjunction-normalized identity comparison followed by the functor right unitor.
Source: the item's open-immersion clause; BoundedConstructiblePullback
(blueprint: lem-pur-condensed-compositor-realization). -/
def openTrivial (Y Z : CondensedERealization.Base k) (g : Y.scheme ⟶ Z.scheme)
    [g.IsOver (Spec (.of k))] [IsOpenImmersion g] :=
  letI : IsOpenImmersion (CondensedERealization.Base.map Y Z g).left :=
    inferInstanceAs (IsOpenImmersion g)
  Functor.isoWhiskerLeft
      (CondensedRing.boundedConstructibleOpenImmersionLowerShriek
        (Profinite.padicAlgClRingObj l) l (CondensedERealization.Base.map Y Z g))
      (CondensedRing.boundedConstructibleLowerStarId
        (Profinite.padicAlgClRingObj l) l Z.model) ≪≫
    Functor.rightUnitor _

/-- The comparison square for one supplied proper compactification refinement,
using the original finite-valued Omega refinement map.
Source: the item's refinement clause; compact-support realization, Steps 15--16
(blueprint: lem-pur-condensed-compositor-realization). -/
def ComparisonRefines (A : CoefficientData l E k) (a : E →ₐ[ℚ_[l]] PadicAlgCl l)
    (X Y : CondensedERealization.Base k) (f : X.scheme ⟶ Y.scheme)
    [f.IsOver (Spec (.of k))] {c d : Compactification f} (r : c.Refinement d) : Prop :=
  ∀ K : CondensedERealization.Integral l E X.scheme,
    (U l E k A a Y).map ((integralRefinement l E k A X Y f r).app K) ≫
        comparison l E k A a X Y f c K =
      comparison l E k A a X Y f d K ≫
        (fieldRefinement (Profinite.padicAlgClRingObj l) r).app
          ⟨(U l E k A a X).obj K, U_constructible l E k A a X K⟩

/-- The literal square, invertibility, naturality and all compactification transports.
The parameters d,c,r,s specify a compatible tower and its common refinement with ch.
Source: all conclusion clauses of the item
(blueprint: lem-pur-condensed-compositor-realization). -/
structure Laws (A : CoefficientData l E k) (a : E →ₐ[ℚ_[l]] PadicAlgCl l)
    (X Y Z : CondensedERealization.Base k)
    (f : X.scheme ⟶ Y.scheme) (g : Y.scheme ⟶ Z.scheme)
    [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
    (cf : Compactification f) (cg : Compactification g)
    (ch : Compactification (f ≫ g)) (d : Compactification (cf.g ≫ cg.i))
    (c : Compactification (f ≫ g))
    (r : c.Refinement (composite k X Y Z f g cf cg d)) (s : c.Refinement ch) : Prop where
  integral_invertible : ∀ (K : CondensedERealization.Integral l E X.scheme)
    (hK : Uniform l E k X K),
    IsIso (integralCompositor l E k A X Y Z f g cf cg ch d c r s K hK)
  comparison_invertible : ∀ K : CondensedERealization.Integral l E X.scheme,
    IsIso (comparison l E k A a X Y f cf K)
  square : ∀ (K : CondensedERealization.Integral l E X.scheme)
    (hK : Uniform l E k X K),
    (U l E k A a Z).map
        (integralCompositor l E k A X Y Z f g cf cg ch d c r s K hK) ≫
      comparison l E k A a X Z (f ≫ g) ch K =
    comparison l E k A a Y Z g cg ((P l E k A X Y f cf).obj K) ≫
      (CondensedRing.rightDerivedLowerShriekOfCompactification
        (Profinite.padicAlgClRingObj l) cg).map (comparison l E k A a X Y f cf K) ≫
      ((condensedCompositor l k X Y Z f g cf cg ch).hom.app
        ⟨(U l E k A a X).obj K, U_constructible l E k A a X K⟩).hom
  comparison_refinement :
    (∀ (cf' : Compactification f) (rf : cf'.Refinement cf),
      ComparisonRefines l E k A a X Y f rf) ∧
    (∀ (cg' : Compactification g) (rg : cg'.Refinement cg),
      ComparisonRefines l E k A a Y Z g rg) ∧
    (∀ (ch' : Compactification (f ≫ g)) (rh : ch'.Refinement ch),
      ComparisonRefines l E k A a X Z (f ≫ g) rh)
  naturality : ∀ (K K' : CondensedERealization.Integral l E X.scheme)
    (hK : Uniform l E k X K) (hK' : Uniform l E k X K') (v : K ⟶ K'),
    (P l E k A Y Z g cg).map ((P l E k A X Y f cf).map v) ≫
        integralCompositor l E k A X Y Z f g cf cg ch d c r s K' hK' =
      integralCompositor l E k A X Y Z f g cf cg ch d c r s K hK ≫
        (P l E k A X Z (f ≫ g) ch).map v
  tower_independence : ∀ (d' : Compactification (cf.g ≫ cg.i))
    (c' : Compactification (f ≫ g))
    (r' : c'.Refinement (composite k X Y Z f g cf cg d')) (s' : c'.Refinement ch)
    (K : CondensedERealization.Integral l E X.scheme) (hK : Uniform l E k X K),
    integralCompositor l E k A X Y Z f g cf cg ch d c r s K hK =
      integralCompositor l E k A X Y Z f g cf cg ch d' c' r' s' K hK
  refinement : ∀ (cf' : Compactification f) (cg' : Compactification g)
    (ch' : Compactification (f ≫ g))
    (rf : cf'.Refinement cf) (rg : cg'.Refinement cg) (rh : ch'.Refinement ch)
    (d' : Compactification (cf'.g ≫ cg'.i)) (c' : Compactification (f ≫ g))
    (r' : c'.Refinement (composite k X Y Z f g cf' cg' d')) (s' : c'.Refinement ch')
    (K : CondensedERealization.Integral l E X.scheme) (hK : Uniform l E k X K),
    integralCompositor l E k A X Y Z f g cf cg ch d c r s K hK ≫
        (integralRefinement l E k A X Z (f ≫ g) rh).app K =
      (integralRefinement l E k A Y Z g rg).app ((P l E k A X Y f cf).obj K) ≫
        (P l E k A Y Z g cg').map ((integralRefinement l E k A X Y f rf).app K) ≫
        integralCompositor l E k A X Y Z f g cf' cg' ch' d' c' r' s' K hK

/-- Condensed realization preserves the specified compact-support compositor.
The coefficient field E is a universe-sized presentation of Q_l, fixed by e.
IsFactorized fixes a to inverse reconstruction, the proper counit mate and the open
unit mate, rather than allowing an independently rescaled realization isomorphism.
Source: latest blueprint sk-prop-sp-composition, Towers; sk-thm-purity-transport,
Steps 2--3; the item's explicit comparison supplement
(blueprint: lem-pur-condensed-compositor-realization).
Proof:
1. Finite type over k gives noetherian finite dimension, and l is invertible.
Integral support preserves uniform constructibility and compatible etale origins.
2. Form the ordinary completed proper/open comparison b on the whole derived
sequence site. Its proper factor is the counit transpose and its open factor is
the inverse unit mate. The finite b composition identity is the etale/pro-etale
composition identity; transposition gives the finite c identity.
3. Apply the actual reduction/limit adjunction to b. Its adjunct q is L(b) after
the reconstruction unit, and beta R(q)=b by the triangle identity. The strict
proper/open word and its refinement factors are invertible on the uniform domain;
evaluations detect isomorphisms but are not used to detect equality of arrows.
4. Proper composition, open composition and the intrinsic interchange satisfy the
whole-system coefficient square by mate pasting. Take its total limit. Substitute
beta R(q)=b in the displayed five-arrow composite. Naturality and the two triangle
identities cancel its inserted counit and units, identifying it with the completed
proper/open compositor conjugated by q.
5. IsFactorized identifies a_E with J(q inverse), the actual proper scalar counit
mate and the open-unit scalar mate. Their coefficient squares identify the completed
compositor with the condensed compositor. Extending to Omega uses the original
proper/open coefficient projection; descent to a common finite field proves this
projection invertible for the finite-extension-valued coefficient ring.
6. Paste the scalar square with the conjugacy of Step 4, then cancel the invertible
image of the two q maps. The remaining equality is exactly square, with the inverse
archived compositor transported to cf,cg,ch by the canonical comparisons.
7. All these maps are natural in complexes and localized morphisms. Horizontal and
vertical mate pasting before evaluation gives refinement compatibility and tower
independence. For an open g, use (g,id); its proper counit mate becomes identity
under openTrivial, leaving the exact open extension and its specified unit.
This includes identity arrows, empty schemes and empty opens. -/
theorem condensedCompositorRealization (C : ComparisonFamily l k)
    (_hC : CompactSupportRealizationFactorization.IsFactorized l k C)
    (_e : E ≃ₐ[ℚ_[l]] ℚ_[l])
    (X Y Z : CondensedERealization.Base k)
    (f : X.scheme ⟶ Y.scheme) (g : Y.scheme ⟶ Z.scheme)
    [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
    (df dg : ℕ) [SmoothOfRelativeDimension df f] [SmoothOfRelativeDimension dg g]
    (cf : Compactification f) (cg : Compactification g)
    (ch : Compactification (f ≫ g)) (d : Compactification (cf.g ≫ cg.i))
    (c : Compactification (f ≫ g))
    (r : c.Refinement (composite k X Y Z f g cf cg d)) (s : c.Refinement ch) :
    Laws l E k (C.coefficient E) ((Algebra.ofId ℚ_[l] (PadicAlgCl l)).comp _e.toAlgHom)
      X Y Z f g cf cg ch d c r s := by
  sorry

end WeilConjectures.CondensedCompositorRealization
