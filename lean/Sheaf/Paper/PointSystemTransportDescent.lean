/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Sheaf.SixFunctors.SchemeFrobenius
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
public import Sheaf.Paper.InverseImagePullbackComparisonDerived
public import Sheaf.Paper.CoefTowerCoaugmentation
public import Sheaf.Paper.PointProEtaleSectionsExact
public import Sheaf.SixFunctors.FrobeniusPointTransport
public import Sheaf.Paper.CoefficientRingedSequenceSite
public import Sheaf.Paper.PointAutomorphismRestrictionNatural
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Paper.PointSystemTransportChain
public import Sheaf.Paper.PointSystemTransportFinite
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Predicate
import Sheaf.CategoryTheory.ExactDerivedSquareDescent
import Sheaf.Paper.PointRestrictionSequenceEvaluation

/-! # Strict point transport and descent on whole coefficient systems

Source: blueprint main-20261015, `prop-trf-rational-frobenius-integral-model`,
proof (3), point-factor prerequisite; Stacks Tags 0941, 015F and 04VG
(blueprint: lem-trf-point-system-transport-descent).

The source is the recorded ringed sequence site, without normalization or boundedness.
The target is the ordinary derived category of whole integral-module towers. The index
`n : ℕ` means exponent `n+1`. Site and coefficient universes remain independent.

## Main definitions

* `pull`, `sections`: actual inverse image and exact sections of strict systems.
* `chainTransport`, `derivedTransport`: the uniquely normalized natural maps.
* `finiteTransportComplex`, `finiteTransportDerived`: the finite representative recipe.

## Main statements

* `point_system_transport_descent`: unique descent on entire system derived categories.
* `coefficient_squares`, `tensorTransition_existsUnique`: original coefficient transitions.
* `finite_evaluation`: evaluation agrees with the finite point-transport recipe.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
attribute [local irreducible] WeilConjectures.PointSystemTransport.quotient

universe t u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.PointSystemTransport


variable (D : FiniteFieldDatum.{t}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Existence and uniqueness of the descent of the specified transformation, together
with quasi-isomorphism preservation and naturality for every derived system morphism.
The codomain is D(Tow(Mod R)), not a tower of separate derived categories.
Source: blueprint proof (3), steps 5--6; Stacks 015F and 04VG
(blueprint: lem-trf-point-system-transport-descent).
Proof: the two exact functors preserve homology and hence quasi-isomorphisms by
lem-weil-pbc-exact-functor-derived-factorization. Apply
lem-weil-pbc-localization-universal-property to the source category of entire system
complexes, with quasi-isomorphisms inverted, and target D(Tow(Mod R)). Its full
faithfulness on natural transformations gives the unique descent with the displayed
representative equation. Naturality holds for chain maps and for inverses of
quasi-isomorphisms, thus for every morphism in the localized system category.
No step assumes that derived evaluation is faithful. -/
theorem point_system_transport_descent (hl : l ≠ D.p) (r : ℕ) (hr : 1 ≤ r) :
    (∀ (M N : CochainComplex (coefficientSequenceModules l E (Spec (.of D.k))) ℤ)
      (f : M ⟶ N), QuasiIso f →
        QuasiIso ((complexSections D l E).map f) ∧
        QuasiIso ((transportedComplexSections D l E r).map f)) ∧
    ∃! I : derivedSections D l E ⟶ transportedDerivedSections D l E r,
      (∀ M : CochainComplex (coefficientSequenceModules l E (Spec (.of D.k))) ℤ,
        I.app (DerivedCategory.Q.obj M) ≫
            (pull D l E r ⋙ sections D l E).mapDerivedCategoryFactors.hom.app M =
          (sections D l E).mapDerivedCategoryFactors.hom.app M ≫
            DerivedCategory.Q.map ((chainTransport D l E hl r hr).app M)) ∧
      (∀ {C C' : coefficientSequenceDerived l E (Spec (.of D.k))} (f : C ⟶ C'),
        (derivedSections D l E).map f ≫ I.app C' =
          I.app C ≫ (transportedDerivedSections D l E r).map f) := by
  constructor
  · intro M N f hf
    have := hf
    exact ⟨inferInstance, inferInstance⟩
  · let I : derivedSections D l E ⟶ transportedDerivedSections D l E r :=
      Localization.liftNatTrans DerivedCategory.Q
        (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
        (complexSections D l E ⋙ DerivedCategory.Q)
        (transportedComplexSections D l E r ⋙ DerivedCategory.Q)
        (derivedSections D l E) (transportedDerivedSections D l E r)
        (Functor.whiskerRight (chainTransport D l E hl r hr) DerivedCategory.Q)
    have hI (M : CochainComplex (coefficientSequenceModules l E (Spec (.of D.k))) ℤ) :
        I.app (DerivedCategory.Q.obj M) ≫
            (pull D l E r ⋙ sections D l E).mapDerivedCategoryFactors.hom.app M =
          (sections D l E).mapDerivedCategoryFactors.hom.app M ≫
            DerivedCategory.Q.map ((chainTransport D l E hl r hr).app M) := by
      dsimp only [I]
      rw [Localization.liftNatTrans_app]
      change ((sections D l E).mapDerivedCategoryFactors.hom.app M ≫
        DerivedCategory.Q.map ((chainTransport D l E hl r hr).app M) ≫
        (pull D l E r ⋙ sections D l E).mapDerivedCategoryFactors.inv.app M) ≫
        (pull D l E r ⋙ sections D l E).mapDerivedCategoryFactors.hom.app M = _
      simp only [Category.assoc, Iso.inv_hom_id_app]
      exact congrArg (fun f ↦ (sections D l E).mapDerivedCategoryFactors.hom.app M ≫ f)
        (Category.comp_id (DerivedCategory.Q.map ((chainTransport D l E hl r hr).app M)))
    refine ⟨I, ⟨hI, fun f ↦ I.naturality f⟩, ?_⟩
    intro J hJ
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    intro M
    apply (cancel_mono
      ((pull D l E r ⋙ sections D l E).mapDerivedCategoryFactors.hom.app M)).1
    exact (hJ.1 M).trans (hI M).symm

/-- The descended map, specified by the localization representative equation.
Source: blueprint proof (3) (blueprint: lem-trf-point-system-transport-descent). -/
def derivedTransport (hl : l ≠ D.p) (r : ℕ) (hr : 1 ≤ r) :
    derivedSections D l E ⟶ transportedDerivedSections D l E r :=
  (point_system_transport_descent D l E hl r hr).2.exists.choose

private theorem finiteSigmaR_naturality (r n : ℕ)
    {K L : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ}
    (f : K ⟶ L) :
    ((finiteRSections D l E n).mapHomologicalComplex (.up ℤ)).map f ≫
        finiteSigmaR D l E r n L =
      finiteSigmaR D l E r n K ≫
        ((inverseImageFiniteModules l E (pointPower D r).hom n ⋙
          finiteRSections D l E n).mapHomologicalComplex (.up ℤ)).map f := by
  have hK := (finiteSigma_existsUnique D l E r n K).exists.choose_spec
  have hL := (finiteSigma_existsUnique D l E r n L).exists.choose_spec
  ext i x
  change (finiteSigma D l E r n L).f i
      ((f.f i).val.app (op (ProEt.mk (𝟙 (Spec (.of D.k))))) x) =
    (f.f i).val.app (op ((proEtaleIsoPostcompose (pointPower D r).hom).obj
      (ProEt.mk (𝟙 (Spec (.of D.k)))))) ((finiteSigma D l E r n K).f i x)
  erw [hL, hK]
  exact (PresheafOfModules.naturality_apply (f.f i).val
    (pointRestrictionArrow (pointPower D r).hom).op x).symm

private def finiteSigmaChain (r n : ℕ) :
    (finiteRSections D l E n).mapHomologicalComplex (.up ℤ) ⟶
      (inverseImageFiniteModules l E (pointPower D r).hom n ⋙
        finiteRSections D l E n).mapHomologicalComplex (.up ℤ) where
  app := finiteSigmaR D l E r n
  naturality _ _ f := finiteSigmaR_naturality D l E r n f

private def finiteSigmaDescent (r n : ℕ) :
    (finiteRSections D l E n).mapDerivedCategory ⟶
      (inverseImageFiniteModules l E (pointPower D r).hom n ⋙
        finiteRSections D l E n).mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ))
    ((finiteRSections D l E n).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    ((inverseImageFiniteModules l E (pointPower D r).hom n ⋙
      finiteRSections D l E n).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    _ _ (Functor.whiskerRight (finiteSigmaChain D l E r n) DerivedCategory.Q)

private theorem descent_representative
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F G : A ⥤ B) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (τ : F.mapHomologicalComplex (.up ℤ) ⟶ G.mapHomologicalComplex (.up ℤ))
    (I : F.mapDerivedCategory ⟶ G.mapDerivedCategory)
    (hI : ∀ M, I.app (DerivedCategory.Q.obj M) ≫
      G.mapDerivedCategoryFactors.hom.app M =
        F.mapDerivedCategoryFactors.hom.app M ≫ DerivedCategory.Q.map (τ.app M))
    (C : DerivedCategory A) :
    I.app C = F.mapDerivedCategory.map (DerivedCategory.Q.objObjPreimageIso C).inv ≫
      F.mapDerivedCategoryFactors.hom.app (DerivedCategory.Q.objPreimage C) ≫
      DerivedCategory.Q.map (τ.app (DerivedCategory.Q.objPreimage C)) ≫
      G.mapDerivedCategoryFactors.inv.app (DerivedCategory.Q.objPreimage C) ≫
      G.mapDerivedCategory.map (DerivedCategory.Q.objObjPreimageIso C).hom := by
  let e := DerivedCategory.Q.objObjPreimageIso C
  have h (M : CochainComplex A ℤ) : I.app (DerivedCategory.Q.obj M) =
      F.mapDerivedCategoryFactors.hom.app M ≫ DerivedCategory.Q.map (τ.app M) ≫
        G.mapDerivedCategoryFactors.inv.app M := by
    apply (cancel_mono (G.mapDerivedCategoryFactors.hom.app M)).1
    simpa only [Functor.comp_obj, Category.assoc, Iso.inv_hom_id_app,
      Category.comp_id] using hI M
  calc
    I.app C = F.mapDerivedCategory.map e.inv ≫ I.app _ ≫
        G.mapDerivedCategory.map e.hom := by
      rw [I.naturality_assoc, ← G.mapDerivedCategory.map_comp]
      simp
    _ = _ := by rw [h]; simp only [Category.assoc]; rfl


private theorem finiteSigmaDescent_fac (r n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :
    (finiteSigmaDescent D l E r n).app (DerivedCategory.Q.obj K) ≫
      (inverseImageFiniteModules l E (pointPower D r).hom n ⋙
        finiteRSections D l E n).mapDerivedCategoryFactors.hom.app K =
      (finiteRSections D l E n).mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map (finiteSigmaR D l E r n K) := by
  dsimp only [finiteSigmaDescent]
  rw [Localization.liftNatTrans_app]
  change ((finiteRSections D l E n).mapDerivedCategoryFactors.hom.app K ≫
    DerivedCategory.Q.map (finiteSigmaR D l E r n K) ≫
    (inverseImageFiniteModules l E (pointPower D r).hom n ⋙
      finiteRSections D l E n).mapDerivedCategoryFactors.inv.app K) ≫
    (inverseImageFiniteModules l E (pointPower D r).hom n ⋙
      finiteRSections D l E n).mapDerivedCategoryFactors.hom.app K = _
  simp only [Functor.comp_obj, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

private theorem finiteTransportDerived_factor (r n : ℕ)
    (C : normalizedDVRDerived l E (Spec (.of D.k)) n) :
    finiteTransportDerived D l E r n C =
      (finiteSigmaDescent D l E r n).app C ≫ finiteDerivedComparison D l E r n C := by
  rw [descent_representative _ _ (finiteSigmaChain D l E r n)
    (finiteSigmaDescent D l E r n) (finiteSigmaDescent_fac D l E r n)]
  dsimp only [finiteTransportDerived, finiteDerivedComparison, finiteSigmaChain,
    finiteTransportComplex]
  simp only [Functor.comp_obj, Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
  erw [Functor.map_comp]
  simp only [Category.assoc]


attribute [local irreducible] coefficientSequenceCommRingSystem integralCoefficientCommRingSheaf

private theorem normalized_square
    {A B C D : Type v} (hA : A = B) (hC : C = D)
    (f : A → B) (g : C → D) (u : A → C) (v : B → D)
    (hf : HEq f (id : B → B)) (hg : HEq g (id : D → D)) (hu : HEq u v)
    (x : A) : g (u x) = v (f x) := by
  cases hA
  cases hC
  rw [eq_of_heq hf, eq_of_heq hg, eq_of_heq hu]
  rfl

set_option backward.isDefEq.respectTransparency true in
private theorem finiteSigma_component (r n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ)
    (i : ℤ) (x : (K.X i).val.obj (op (ProEt.mk (𝟙 (Spec (.of D.k)))))) :
    (finiteSigma D l E r n K).f i x =
      pointRestrictionRaw l E (pointPower D r).hom (some n) (K.X i) x :=
  (finiteSigma_existsUnique D l E r n K).exists.choose_spec i x


set_option backward.isDefEq.respectTransparency true in
attribute [local irreducible] finiteSigma pointRestrictionRaw in
private theorem finiteSigma_system_component (r n : ℕ)
    (M : CochainComplex (coefficientSequenceModules l E (Spec (.of D.k))) ℤ) (i : ℤ) :
    HEq (fun y : (M.X i).val.obj (op (n, ProEt.mk (𝟙 (Spec (.of D.k))))) ↦
      (M.X i).val.map
        (Prod.mkHom (𝟙 n) (pointRestrictionArrow (pointPower D r).hom)).op y)
      (fun y ↦ (finiteSigma D l E r n
          (((coefficientSequenceEvaluation l E (Spec (.of D.k)) n).mapHomologicalComplex
            (.up ℤ)).obj M)).f i y) := by
  have hsigma := funext (finiteSigma_component D l E r n
    (((coefficientSequenceEvaluation l E (Spec (.of D.k)) n).mapHomologicalComplex
      (.up ℤ)).obj M) i)
  have hraw := heq_of_eq
    (pointRestrictionRaw_coefficientSequenceEvaluation l E (pointPower D r).hom n (M.X i))
  have hs := (heq_of_eq hsigma).symm
  have hh := hraw.symm.trans hs
  exact hh

set_option backward.isDefEq.respectTransparency true in
attribute [local irreducible] finiteSigma pointRestrictionRaw in
private theorem evaluation_chain_component (hl : l ≠ D.p) (r : ℕ) (hr : 1 ≤ r) (n : ℕ)
    (M : CochainComplex (coefficientSequenceModules l E (Spec (.of D.k))) ℤ)
    (i : ℤ) (x : ((sections D l E).obj (M.X i)).obj (op n)) :
    (evaluationComparisons D l E r n).2.hom.app (M.X i)
      ((((chainTransport D l E hl r hr).app M).f i).app (op n) x) =
    (finiteSigma D l E r n
      (((coefficientSequenceEvaluation l E (Spec (.of D.k)) n).mapHomologicalComplex
        (.up ℤ)).obj M)).f i
      ((evaluationComparisons D l E r n).1.hom.app (M.X i) x) := by
  have hτ := (chainTransport_existsUnique D l E hl r hr).exists.choose_spec
  have he := (evaluation_existsUnique D l E r n).exists.choose_spec
  have hcarrier (P : coefficientSequenceModules l E (Spec (.of D.k))) :
      (((sections D l E).obj P).obj (op n) : Type (max u (t + 1))) =
        (P.val.obj (op (n, ProEt.mk (𝟙 (Spec (.of D.k))))) : Type (max u (t + 1))) := by
    exact congrArg
      (fun N : scalarReductionSource l E (Spec (.of D.k)) ↦
        (N.val.obj (op (ProEt.mk (𝟙 (Spec (.of D.k))))) : Type (max u (t + 1))))
      ((coefficientSequenceRestriction_exists l E (Spec (.of D.k))).exists.choose_spec.1 P n)
  have hfun := (hτ M i n).trans (finiteSigma_system_component D l E r n M i)
  let f := fun y : ((sections D l E).obj (M.X i)).obj (op n) ↦
    (evaluationComparisons D l E r n).1.hom.app (M.X i) y
  let g := fun y : ((sections D l E).obj ((pull D l E r).obj (M.X i))).obj (op n) ↦
    (evaluationComparisons D l E r n).2.hom.app (M.X i) y
  let u := fun y : ((sections D l E).obj (M.X i)).obj (op n) ↦
    (((chainTransport D l E hl r hr).app M).f i).app (op n) y
  let v := fun y ↦ (finiteSigma D l E r n
      (((coefficientSequenceEvaluation l E (Spec (.of D.k)) n).mapHomologicalComplex
        (.up ℤ)).obj M)).f i y
  have hsquare := normalized_square (hcarrier (M.X i))
    (hcarrier ((pull D l E r).obj (M.X i))) f g u v
    (he (M.X i)).1 (he (M.X i)).2 hfun x
  exact hsquare


set_option backward.isDefEq.respectTransparency true in
attribute [local irreducible] finiteSigma pointRestrictionRaw in
private theorem evaluation_chain (hl : l ≠ D.p) (r : ℕ) (hr : 1 ≤ r) (n : ℕ)
    (M : CochainComplex (coefficientSequenceModules l E (Spec (.of D.k))) ℤ) :
    ((towerEvaluation.{t, u} l E n).mapHomologicalComplex (.up ℤ)).map
        ((chainTransport D l E hl r hr).app M) ≫
      (NatTrans.mapHomologicalComplex (evaluationComparisons D l E r n).2.hom
        (.up ℤ)).app M =
    (NatTrans.mapHomologicalComplex (evaluationComparisons D l E r n).1.hom
      (.up ℤ)).app M ≫
      finiteSigmaR D l E r n
        (((coefficientSequenceEvaluation l E (Spec (.of D.k)) n).mapHomologicalComplex
          (.up ℤ)).obj M) := by
  ext i x
  exact evaluation_chain_component D l E hl r hr n M i x

private theorem postcompose_evaluation
    {T : Type*} [Category T] {W X Y Z V : T}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (k : Z ⟶ V)
    {q : W ⟶ Z} (e : f ≫ g ≫ h = q) : f ≫ g ≫ h ≫ k = q ≫ k := by
  simpa only [Category.assoc] using congrArg (fun x ↦ x ≫ k) e

set_option backward.isDefEq.respectTransparency true in
private theorem finite_evaluation_descent (hl : l ≠ D.p) (r : ℕ) (hr : 1 ≤ r) (n : ℕ)
    (C : coefficientSequenceDerived l E (Spec (.of D.k))) :
    (sourceEvaluation D l E r n).inv.app C ≫
      (towerEvaluation.{t, u} l E n).mapDerivedCategory.map
        ((derivedTransport D l E hl r hr).app C) ≫
      (targetEvaluation D l E r n).hom.app C =
    (finiteSigmaDescent D l E r n).app
      ((coefficientSequenceDerivedEvaluation l E (Spec (.of D.k)) n).obj C) :=
  CategoryTheory.Functor.evaluated_descent
    (sections D l E) (pull D l E r ⋙ sections D l E)
    (towerEvaluation.{t, u} l E n)
    (coefficientSequenceEvaluation l E (Spec (.of D.k)) n)
    (finiteRSections D l E n)
    (inverseImageFiniteModules l E (pointPower D r).hom n ⋙ finiteRSections D l E n)
    (evaluationComparisons D l E r n).1 (evaluationComparisons D l E r n).2
    (chainTransport D l E hl r hr) (finiteSigmaChain D l E r n)
    (derivedTransport D l E hl r hr) (finiteSigmaDescent D l E r n)
    (point_system_transport_descent D l E hl r hr).2.exists.choose_spec.1
    (finiteSigmaDescent_fac D l E r n) (evaluation_chain D l E hl r hr n) C

set_option backward.isDefEq.respectTransparency true in
/-- Evaluation of the actual descended system morphism, through j, is exactly the
finite point-transport recipe. In particular this is iota^(r) whenever the nth
coefficient object is bounded constructible. The equation is available on arbitrary
ambient objects because the representative recipe itself has no boundedness condition.
Source: blueprint proof (3), step 7
(blueprint: lem-trf-point-system-transport-descent).
Proof: evaluate the representative equation of point_system_transport_descent.
The two evaluation comparisons are identity on the underlying sections. Thus the
chain map becomes precisely finiteSigmaR, by its unique restriction normalization.
Postcomposing with j gives finiteTransportComplex. The exact evaluation functors
and their mapDerivedCategory comparisons descend this equation. Transport to the
chosen representative of the evaluated object gives the displayed equality, which
is the recipe defining def-weil-frobenius-point-transport with h^r in place of h.
This proves equality of actual evaluated derived morphisms; no faithfulness of
derived evaluations, cartesianness or finite Tor-amplitude is used. -/
theorem finite_evaluation (hl : l ≠ D.p) (r : ℕ) (hr : 1 ≤ r) (n : ℕ)
    (C : coefficientSequenceDerived l E (Spec (.of D.k))) :
    (sourceEvaluation D l E r n).inv.app C ≫
        (towerEvaluation.{t, u} l E n).mapDerivedCategory.map
          ((derivedTransport D l E hl r hr).app C) ≫
        (targetEvaluation D l E r n).hom.app C ≫
        finiteDerivedComparison D l E r n
          ((coefficientSequenceDerivedEvaluation l E (Spec (.of D.k)) n).obj C) =
      finiteTransportDerived D l E r n
        ((coefficientSequenceDerivedEvaluation l E (Spec (.of D.k)) n).obj C) :=
  (postcompose_evaluation _ _ _
    (finiteDerivedComparison D l E r n
      ((coefficientSequenceDerivedEvaluation l E (Spec (.of D.k)) n).obj C))
    (finite_evaluation_descent D l E hl r hr n C)).trans
      (finiteTransportDerived_factor D l E r n
        ((coefficientSequenceDerivedEvaluation l E (Spec (.of D.k)) n).obj C)).symm


end WeilConjectures.PointSystemTransport

