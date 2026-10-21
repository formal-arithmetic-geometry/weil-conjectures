/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q54
-/
module

public import Sheaf.Paper.CompletedOperationTowerSubstitution
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Paper.IntegralReductionTowerCanonical
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
/-! # Derived limit of a strict integral comparison tower

Source: Stacks Project, Tag 0941, `lemma-derived-limit-is-ok`; Tag 07A4,
`lemma-pullback-tensor-product`, for the finite comparison application
(blueprint: lem-pur-integral-tower-limit-comparison).

Strict towers are cochain complexes on the ringed sequence site, so their maps retain
all semilinear quotient transitions. Exponent n+1 is encoded by n : ℕ. The models
are the representative-normalized presentations of the substitution dependency,
with its ComparisonLaws supplied explicitly to the theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.IntegralTowerLimit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Index the two given schemes, without changing either site.
Source: Stacks Tag 0941; node setup
(blueprint: lem-pur-integral-tower-limit-comparison). -/
def sites (X Y : Scheme.{t}) : Bool → Scheme.{t}
  | false => X
  | true => Y

/-- Flat-term K-flat levels of the actual strict quotient system.
Source: Stacks Tag 0941; node hypotheses
(blueprint: lem-pur-integral-tower-limit-comparison). -/
def Good (X : Scheme.{t}) (T : CochainComplex (coefficientSequenceModules l E X) ℤ) :
    Prop :=
  ∀ n : ℕ,
    CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology X) (R := integralCoefficientCommRingSheaf l E X n)
      (((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj T) ∧
    ∀ k : ℤ, SheafOfModules.IsFlatOnSite
      (J := Scheme.ProEt.topology X) (R := integralCoefficientCommRingSheaf l E X n)
      ((((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj T).X k)

/-- The termwise finite inverse image, including quotient transitions.
Source: Stacks Tag 0941; node definition of F_f(T)
(blueprint: lem-pur-integral-tower-limit-comparison). -/
def pullback {X Y : Scheme.{t}} (f : X ⟶ Y) :=
  (integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)

/-- The signed direct-sum total tensor, on the whole coefficient system.
Source: Stacks Tag 0941; node definition of W
(blueprint: lem-pur-integral-tower-limit-comparison).
-/
def total (X : Scheme.{t}) :=
  coefficientTotalTensor.{u, t+1, t}
    (coefficientSequenceTopology (Scheme.ProEt.topology X))
    (coefficientSequenceCommRingSheaf l E X)

/-- A quadruple from the node: three normalized strict towers with flat-term K-flat
levels and a strict chain isomorphism, whose inverse also respects every transition.
Source: Stacks Tag 0941; node hypotheses
(blueprint: lem-pur-integral-tower-limit-comparison). -/
structure Input {X Y : Scheme.{t}} (f : X ⟶ Y) where
  T : CochainComplex (coefficientSequenceModules l E Y) ℤ
  U : CochainComplex (coefficientSequenceModules l E X) ℤ
  V : CochainComplex (coefficientSequenceModules l E X) ℤ
  goodT : Good l E Y T
  goodU : Good l E X U
  goodV : Good l E X V
  normalizedT : IsNormalizedCoefficientSequence l E Y (DerivedCategory.Q.obj T)
  normalizedU : IsNormalizedCoefficientSequence l E X (DerivedCategory.Q.obj U)
  normalizedV : IsNormalizedCoefficientSequence l E X (DerivedCategory.Q.obj V)
  c : (pullback l E f).obj T ≅ (total l E X).obj (U, V)

variable {X Y : Scheme.{t}} {f : X ⟶ Y}

/-- The completed pullback of the derived limit of T.
Source: Stacks Tag 0941; node object S
(blueprint: lem-pur-integral-tower-limit-comparison). -/
def source (A : Input l E f) :=
  (integralDerivedPullback l E f).obj
    ((coefficientSequenceLimit l E Y).obj (DerivedCategory.Q.obj A.T))

/-- The completed tensor of the derived limits of U and V.
Source: Stacks Tag 0941; node object P
(blueprint: lem-pur-integral-tower-limit-comparison). -/
def target (A : Input l E f) :=
  (IntegralOnSlice.completedTensor l E X none).obj
    ((coefficientSequenceLimit l E X).obj (DerivedCategory.Q.obj A.U),
     (coefficientSequenceLimit l E X).obj (DerivedCategory.Q.obj A.V))

/-- The canonical substitution identifications, with their exact counit formulas.
The whole-system K-flat proofs are conclusions from levelwise K-flatness, not hypotheses.
Source: Stacks Tag 0941; node proof steps 1 and 3
(blueprint: lem-pur-integral-tower-limit-comparison). -/
structure Realization (M : CompletedOperations.Models l E (sites X Y)) (A : Input l E f) where
  kflatU : CochainComplex.IsKFlatIndependentCoefficients
    (J := coefficientSequenceTopology (Scheme.ProEt.topology X))
    (R := coefficientSequenceCommRingSheaf l E X) A.U
  kflatV : CochainComplex.IsKFlatIndependentCoefficients
    (J := coefficientSequenceTopology (Scheme.ProEt.topology X))
    (R := coefficientSequenceCommRingSheaf l E X) A.V
  a : source l E A ≅
    (coefficientSequenceLimit l E X).obj (DerivedCategory.Q.obj ((pullback l E f).obj A.T))
  b : target l E A ≅
    (coefficientSequenceLimit l E X).obj (DerivedCategory.Q.obj ((total l E X).obj (A.U, A.V)))
  a_formula : a.hom =
    CompletedOperations.pullbackComparison l E M (a := false) (b := true) f
      (DerivedCategory.Q.obj A.T) ≫
    (coefficientSequenceLimit l E X).map
      ((integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.hom.app A.T)
  b_formula : b.hom =
    CompletedOperations.tensorComparison l E M false
      (DerivedCategory.Q.obj A.U) (DerivedCategory.Q.obj A.V) ≫
    (coefficientSequenceLimit l E X).map
      (((M.system false).models.iso
        (coefficientSequenceTopology (Scheme.ProEt.topology X))
        (coefficientSequenceCommRingSheaf l E X) (M.system false).closed
        A.U A.V kflatU kflatV).inv)

/-- The limit of the supplied strict isomorphism, conjugated by the prescribed
substitution isomorphisms. Its inverse uses the supplied strict inverse.
Source: Stacks Tag 0941; node proof steps 2--3
(blueprint: lem-pur-integral-tower-limit-comparison).
-/
def comparison {M : CompletedOperations.Models l E (sites X Y)} {A : Input l E f}
    (r : Realization l E M A) : source l E A ≅ target l E A :=
  r.a ≪≫ (coefficientSequenceLimit l E X).mapIso (DerivedCategory.Q.mapIso A.c) ≪≫ r.b.symm

/-- A commuting diagram of strict quadruples, using the actual total tensor on maps.
Source: Stacks Tag 0941; node diagram clause
(blueprint: lem-pur-integral-tower-limit-comparison).
-/
structure Diagram (A B : Input l E f) where
  t : A.T ⟶ B.T
  u : A.U ⟶ B.U
  v : A.V ⟶ B.V
  square : (pullback l E f).map t ≫ B.c.hom =
    A.c.hom ≫ (total l E X).map (u, v)

/-- The completed source map of a strict diagram, with no arbitrary comparison arrow.
Source: Stacks Tag 0941; node proof step 5
(blueprint: lem-pur-integral-tower-limit-comparison). -/
def sourceMap {A B : Input l E f} (d : Diagram l E A B) : source l E A ⟶ source l E B :=
  (integralDerivedPullback l E f).map
    ((coefficientSequenceLimit l E Y).map (DerivedCategory.Q.map d.t))

/-- The completed target map of the same diagram.
Source: Stacks Tag 0941; node proof step 5
(blueprint: lem-pur-integral-tower-limit-comparison). -/
def targetMap {A B : Input l E f} (d : Diagram l E A B) : target l E A ⟶ target l E B :=
  (IntegralOnSlice.completedTensor l E X none).map
    (Prod.mkHom ((coefficientSequenceLimit l E X).map (DerivedCategory.Q.map d.u))
      ((coefficientSequenceLimit l E X).map (DerivedCategory.Q.map d.v)))

/-- Reduction of the specified source substitution, followed by the coherent counit.
Source: Stacks Tag 0941; node proof step 4
(blueprint: lem-pur-integral-tower-limit-comparison). -/
def sourceReduction {M : CompletedOperations.Models l E (sites X Y)} {A : Input l E f}
    (r : Realization l E M A) :=
  (M.calculus false).reduction.map r.a.hom ≫
    (M.calculus false).adjunction.counit.app (DerivedCategory.Q.obj ((pullback l E f).obj A.T))

/-- Reduction of the specified target substitution, followed by the coherent counit.
Source: Stacks Tag 0941; node proof step 4
(blueprint: lem-pur-integral-tower-limit-comparison). -/
def targetReduction {M : CompletedOperations.Models l E (sites X Y)} {A : Input l E f}
    (r : Realization l E M A) :=
  (M.calculus false).reduction.map r.b.hom ≫
    (M.calculus false).adjunction.counit.app
      (DerivedCategory.Q.obj ((total l E X).obj (A.U, A.V)))

/-- All assertions about the induced map, in the coherent system category itself.
The last clause uses quasi-isomorphisms of representatives: naturality then identifies
maps under the canonical resolution comparisons already fixed by a_formula and b_formula.
Source: Stacks Tag 0941; node conclusions
(blueprint: lem-pur-integral-tower-limit-comparison). -/
def Laws {M : CompletedOperations.Models l E (sites X Y)} {A : Input l E f}
    (r : Realization l E M A) : Prop :=
  (comparison l E r).hom ≫ (comparison l E r).inv = 𝟙 _ ∧
  (comparison l E r).inv ≫ (comparison l E r).hom = 𝟙 _ ∧
  IsIso (sourceReduction l E r) ∧ IsIso (targetReduction l E r) ∧
  (M.calculus false).reduction.map (comparison l E r).hom ≫ targetReduction l E r =
    sourceReduction l E r ≫ DerivedCategory.Q.map A.c.hom ∧
  (M.calculus false).reduction.map (comparison l E r).inv ≫ sourceReduction l E r =
    targetReduction l E r ≫ DerivedCategory.Q.map A.c.inv ∧
  ∀ (B : Input l E f) (r' : Realization l E M B) (d : Diagram l E A B),
    sourceMap l E d ≫ r'.a.hom =
      r.a.hom ≫ (coefficientSequenceLimit l E X).map
        (DerivedCategory.Q.map ((pullback l E f).map d.t)) ∧
    targetMap l E d ≫ r'.b.hom =
      r.b.hom ≫ (coefficientSequenceLimit l E X).map
        (DerivedCategory.Q.map ((total l E X).map (d.u, d.v))) ∧
    sourceMap l E d ≫ (comparison l E r').hom =
      (comparison l E r).hom ≫ targetMap l E d ∧
    targetMap l E d ≫ (comparison l E r').inv =
      (comparison l E r).inv ≫ sourceMap l E d ∧
    (QuasiIso d.t → QuasiIso d.u → QuasiIso d.v →
      IsIso (sourceMap l E d) ∧ IsIso (targetMap l E d))

private theorem good_isKFlat (Z : Scheme.{t})
    (S : CoefficientDerivedSystemCalculus l E Z)
    (K : CochainComplex (coefficientSequenceModules l E Z) ℤ) (hK : Good l E Z K) :
    CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (Scheme.ProEt.topology Z))
      (R := coefficientSequenceCommRingSheaf l E Z) K := by
  intro F hF
  change ((total l E Z).obj (F, K)).Acyclic
  apply (DerivedCategory.isZero_Q_obj_iff _).1
  have hEval : JointlyReflectIsomorphisms (coefficientSequenceDerivedEvaluation l E Z) :=
    ⟨fun g ↦ S.isIso_iff_evaluations g |>.2 (fun _ ↦ inferInstance)⟩
  apply hEval.isZero_iff.2
  intro n
  let ev := coefficientSequenceEvaluation l E Z n
  have hFn : ((ev.mapHomologicalComplex (.up ℤ)).obj F).Acyclic := by
    apply (DerivedCategory.isZero_Q_obj_iff _).1
    exact ((coefficientSequenceDerivedEvaluation l E Z n).map_isZero
      ((DerivedCategory.isZero_Q_obj_iff F).2 hF)).of_iso
        (ev.mapDerivedCategoryFactors.app F).symm
  have hTensor := (hK n).1 _ hFn
  have hz := (DerivedCategory.isZero_Q_obj_iff _).2 hTensor
  exact hz.of_iso
    ((ev.mapDerivedCategoryFactors.app ((total l E Z).obj (F, K))) ≪≫
      DerivedCategory.Q.mapIso (coefficientEvaluationTensorIso l E Z n F K))

private theorem pullbackComparison_isIso
    (M : CompletedOperations.Models l E (sites X Y))
    (hM : CompletedOperations.ComparisonLaws.{t, u, 0, 0} l E M)
    (A : Input l E f) :
    IsIso (CompletedOperations.pullbackComparison l E M (a := false) (b := true) f
      (DerivedCategory.Q.obj A.T)) := by
  let P : CompletedOperations.Expression (sites X Y) (fun _ : Unit ↦ true) false :=
    .pullback (a := false) (b := true) f (.input ())
  have h := (hM.invertible P (fun _ ↦ DerivedCategory.Q.obj A.T)
    (fun _ ↦ A.normalizedT)).1
  simpa [P, CompletedOperations.comparison, CompletedOperations.completedValue,
    CompletedOperations.systemValue, Pi.eval] using h

private theorem tensorComparison_isIso
    (M : CompletedOperations.Models l E (sites X Y))
    (hM : CompletedOperations.ComparisonLaws.{t, u, 0, 0} l E M)
    (A : Input l E f) :
    IsIso (CompletedOperations.tensorComparison l E M false
      (DerivedCategory.Q.obj A.U) (DerivedCategory.Q.obj A.V)) := by
  let P : CompletedOperations.Expression (sites X Y) (fun _ : Bool ↦ false) false :=
    .tensor (.input false) (.input true)
  let N : ∀ k : Bool, coefficientSequenceDerived l E ((sites X Y) false) :=
    fun k ↦ if k then DerivedCategory.Q.obj A.V else DerivedCategory.Q.obj A.U
  have hN : ∀ k, IsNormalizedCoefficientSequence l E _ (N k) := by
    intro k
    cases k
    · exact A.normalizedU
    · exact A.normalizedV
  have h := (hM.invertible P N hN).1
  simpa [P, N, CompletedOperations.comparison, CompletedOperations.completedValue,
    CompletedOperations.systemValue, Pi.eval] using h

private theorem source_naturality
    (M : CompletedOperations.Models l E (sites X Y))
    {A B : Input l E f} (r : Realization l E M A) (r' : Realization l E M B)
    (d : Diagram l E A B) :
    sourceMap l E d ≫ r'.a.hom = r.a.hom ≫
      (coefficientSequenceLimit l E X).map
        (DerivedCategory.Q.map ((pullback l E f).map d.t)) := by
  rw [r.a_formula, r'.a_formula]
  let L := coefficientSequenceLimit l E X
  let F := integralComparisonDerivedSequencePullback l E f
  let τ : coefficientSequenceLimit l E Y ⋙ integralDerivedPullback l E f ⟶ F ⋙ L :=
    Functor.whiskerLeft (coefficientSequenceLimit l E Y)
        (M.pullback (a := false) (b := true) f).realization.hom ≫
      Functor.whiskerRight (Functor.whiskerRight (M.calculus true).adjunction.counit F) L
  have hp := τ.naturality (DerivedCategory.Q.map d.t)
  change sourceMap l E d ≫
      CompletedOperations.pullbackComparison l E M (a := false) (b := true) f
        (DerivedCategory.Q.obj B.T) =
    CompletedOperations.pullbackComparison l E M (a := false) (b := true) f
        (DerivedCategory.Q.obj A.T) ≫
      L.map (F.map (DerivedCategory.Q.map d.t)) at hp
  rw [← Category.assoc, hp, Category.assoc, ← L.map_comp]
  rw [show F.map (DerivedCategory.Q.map d.t) ≫
      (integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.hom.app B.T =
    (integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.hom.app A.T ≫
      DerivedCategory.Q.map ((pullback l E f).map d.t) from
      (integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.hom.naturality d.t]
  simp only [L.map_comp, Category.assoc]
  rfl

set_option maxHeartbeats 800000 in
-- Elaborating the two tensor presentations compares the explicit sheafification instances.
private theorem target_naturality
    (M : CompletedOperations.Models l E (sites X Y))
    {A B : Input l E f} (r : Realization l E M A) (r' : Realization l E M B)
    (d : Diagram l E A B) :
    targetMap l E d ≫ r'.b.hom = r.b.hom ≫
      (coefficientSequenceLimit l E X).map
        (DerivedCategory.Q.map ((total l E X).map (d.u, d.v))) := by
  rw [r.b_formula, r'.b_formula]
  let L := coefficientSequenceLimit l E X
  let T := CompletedOperations.tensor l E M false
  let μ := CompletedOperations.tensorRealization l E M false
  let e := (M.calculus false).adjunction.counit
  let ee : ((L ⋙ (M.calculus false).reduction).prod
      (L ⋙ (M.calculus false).reduction)) ⟶ 𝟭 _ := NatTrans.prod e e
  let τ : L.prod L ⋙ IntegralOnSlice.completedTensor l E X none ⟶ T ⋙ L :=
    Functor.whiskerLeft (L.prod L) μ.hom ≫ Functor.whiskerRight (Functor.whiskerRight ee T) L
  have hp := τ.naturality (Prod.mkHom (DerivedCategory.Q.map d.u) (DerivedCategory.Q.map d.v))
  change targetMap l E d ≫ CompletedOperations.tensorComparison l E M false
      (DerivedCategory.Q.obj B.U) (DerivedCategory.Q.obj B.V) =
    CompletedOperations.tensorComparison l E M false
      (DerivedCategory.Q.obj A.U) (DerivedCategory.Q.obj A.V) ≫
        L.map (T.map (Prod.mkHom (DerivedCategory.Q.map d.u)
          (DerivedCategory.Q.map d.v))) at hp
  let KFlat := ObjectProperty.FullSubcategory
    (CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (Scheme.ProEt.topology X))
      (R := coefficientSequenceCommRingSheaf l E X) :
        CochainComplex (coefficientSequenceModules l E X) ℤ → Prop)
  let h : ((⟨A.U, r.kflatU⟩, ⟨A.V, r.kflatV⟩) : KFlat × KFlat) ⟶
      (⟨B.U, r'.kflatU⟩, ⟨B.V, r'.kflatV⟩) :=
    Prod.mkHom (ObjectProperty.homMk d.u) (ObjectProperty.homMk d.v)
  have hm := (M.system false).models.comparison.inv.naturality h
  change T.map (Prod.mkHom (DerivedCategory.Q.map d.u) (DerivedCategory.Q.map d.v)) ≫
      ((M.system false).models.iso
        (coefficientSequenceTopology (Scheme.ProEt.topology X))
        (coefficientSequenceCommRingSheaf l E X) (M.system false).closed
          B.U B.V r'.kflatU r'.kflatV).inv =
    ((M.system false).models.iso
        (coefficientSequenceTopology (Scheme.ProEt.topology X))
        (coefficientSequenceCommRingSheaf l E X) (M.system false).closed
          A.U A.V r.kflatU r.kflatV).inv ≫
      DerivedCategory.Q.map ((total l E X).map (d.u, d.v)) at hm
  rw [← Category.assoc, hp, Category.assoc, ← L.map_comp, hm, L.map_comp, Category.assoc]


private theorem reduction_conjugate
    {C D : Type*} [Category C] [Category D] {R : C ⥤ D} {L : D ⥤ C}
    (adj : R ⊣ L) {S P : C} {A B : D}
    (a : S ≅ L.obj A) (b : P ≅ L.obj B) (c : A ≅ B) :
    R.map (a ≪≫ L.mapIso c ≪≫ b.symm).hom ≫
        (R.map b.hom ≫ adj.counit.app B) =
      (R.map a.hom ≫ adj.counit.app A) ≫ c.hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc]
  rw [← R.map_comp_assoc b.inv b.hom, b.inv_hom_id, R.map_id, Category.id_comp]
  have h := adj.counit.naturality c.hom
  dsimp only [Functor.comp_map, Functor.id_map] at h
  rw [h]

private theorem naturality_conjugate
    {C D : Type*} [Category C] [Category D] (L : D ⥤ C)
    {S P S' P' : C} {A B A' B' : D}
    (a : S ≅ L.obj A) (b : P ≅ L.obj B)
    (a' : S' ≅ L.obj A') (b' : P' ≅ L.obj B') (c : A ≅ B) (c' : A' ≅ B')
    (s : S ⟶ S') (p : P ⟶ P') (x : A ⟶ A') (y : B ⟶ B')
    (ha : s ≫ a'.hom = a.hom ≫ L.map x)
    (hb : p ≫ b'.hom = b.hom ≫ L.map y)
    (h : x ≫ c'.hom = c.hom ≫ y) :
    s ≫ (a' ≪≫ L.mapIso c' ≪≫ b'.symm).hom =
      (a ≪≫ L.mapIso c ≪≫ b.symm).hom ≫ p := by
  apply (cancel_mono b'.hom).1
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc s, ha, Category.assoc, ← L.map_comp, h, L.map_comp]
  congr 2
  rw [hb, b.inv_hom_id_assoc]

/-- Derived limit of the strict integral comparison tower, including coherent reduction,
strict diagram naturality, and independence under simultaneous quasi-isomorphisms.
The presentation is equipped with the ComparisonLaws supplied by
completedOperationTowerSubstitution; bare Models data alone is not sufficient.

Source: Stacks Project, Tag 0941 and the supporting comparison extracted for Tag 07A4
(blueprint: lem-pur-integral-tower-limit-comparison).

Proof: (1) Exact finite pullback computes derived pullback, and K-flat levels compute
finite derived total tensor. Evaluation detects acyclicity, so the levelwise K-flat
hypotheses also give K-flatness on the ringed sequence site. The substitution lemma
and the supplied ComparisonLaws identify these normalized systems with the displayed
completed operations.
(2) Apply the actual total derived inverse-limit functor to c and its specified inverse;
functoriality preserves both inverse equations. (3) Conjugate by the substitution
isomorphisms whose formulas are a_formula and b_formula. (4) The normalized-DVR
counits are coherent isomorphisms. Counit naturality gives both reduction equations
in the whole system category, hence with every quotient transition.
(5) For a commuting strict diagram use naturality of substitution and L(yc)=L(c'x)
to obtain the forward square; the inverse square follows from xc⁻¹=c'⁻¹y.
(6) Simultaneous quasi-isomorphisms localize to isomorphisms. The unique compatible
resolution comparisons of integralOperationsWellDefined identify sourceMap and
targetMap with the canonical changes of representatives, giving the stated independence.
No boundedness or constructibility is used. -/
theorem integralTowerLimitComparison (f : X ⟶ Y)
    (_hlX : ∀ x : X, IsUnit (l : X.residueField x))
    (_hlY : ∀ y : Y, IsUnit (l : Y.residueField y))
    (M : CompletedOperations.Models l E (sites X Y))
    (_hM : CompletedOperations.ComparisonLaws.{t, u, 0, 0} l E M) (A : Input l E f) :
    ∃ r : Realization l E M A, Laws l E r := by
  have hU : CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (Scheme.ProEt.topology X))
      (R := coefficientSequenceCommRingSheaf l E X) A.U :=
    good_isKFlat l E X (M.calculus false) A.U A.goodU
  have hV : CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (Scheme.ProEt.topology X))
      (R := coefficientSequenceCommRingSheaf l E X) A.V :=
    good_isKFlat l E X (M.calculus false) A.V A.goodV
  have := pullbackComparison_isIso l E M _hM A
  have := tensorComparison_isIso l E M _hM A
  let r : Realization l E M A :=
    { kflatU := hU
      kflatV := hV
      a := asIso (CompletedOperations.pullbackComparison l E M
        (a := false) (b := true) f (DerivedCategory.Q.obj A.T)) ≪≫
          (coefficientSequenceLimit l E X).mapIso
            ((integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.app A.T)
      b := asIso (CompletedOperations.tensorComparison l E M false
        (DerivedCategory.Q.obj A.U) (DerivedCategory.Q.obj A.V)) ≪≫
          (coefficientSequenceLimit l E X).mapIso
            (((M.system false).models.iso
              (coefficientSequenceTopology (Scheme.ProEt.topology X))
              (coefficientSequenceCommRingSheaf l E X) (M.system false).closed
              A.U A.V hU hV).symm)
      a_formula := rfl
      b_formula := rfl }
  let P : CompletedOperations.Expression (sites X Y) (fun _ : Unit ↦ true) false :=
    .pullback (a := false) (b := true) f (.input ())
  have hn : IsNormalizedCoefficientSequence l E X
      ((CompletedOperations.systemValue l E M P).obj (fun _ ↦ DerivedCategory.Q.obj A.T)) :=
    _hM.normalized P (fun _ ↦ DerivedCategory.Q.obj A.T) (fun _ ↦ A.normalizedT)
  have he : IsIso ((M.calculus false).adjunction.counit.app
      ((integralComparisonDerivedSequencePullback l E f).obj (DerivedCategory.Q.obj A.T))) := by
    apply _hM.counit
    change IsNormalizedCoefficientSequence l E (sites X Y false)
      ((integralComparisonDerivedSequencePullback l E f).obj (DerivedCategory.Q.obj A.T)) at hn
    exact @hn
  have heA : IsIso ((M.calculus false).adjunction.counit.app
      (DerivedCategory.Q.obj ((pullback l E f).obj A.T))) :=
    (NatTrans.isIso_app_iff_of_iso (M.calculus false).adjunction.counit
      ((integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.app A.T)).1 he
  let PT : CompletedOperations.Expression (sites X Y) (fun _ : Bool ↦ false) false :=
    .tensor (.input false) (.input true)
  let N : ∀ k : Bool, coefficientSequenceDerived l E ((sites X Y) false) :=
    fun k ↦ if k then DerivedCategory.Q.obj A.V else DerivedCategory.Q.obj A.U
  have hN : ∀ k, IsNormalizedCoefficientSequence l E _ (N k) := by
    intro k
    cases k
    · exact A.normalizedU
    · exact A.normalizedV
  have heT : IsIso ((M.calculus false).adjunction.counit.app
      ((CompletedOperations.tensor l E M false).obj
        (DerivedCategory.Q.obj A.U, DerivedCategory.Q.obj A.V))) := by
    apply _hM.counit
    have hnT : IsNormalizedCoefficientSequence l E X
        ((CompletedOperations.systemValue l E M PT).obj N) := _hM.normalized PT N hN
    change IsNormalizedCoefficientSequence l E (sites X Y false)
      ((CompletedOperations.tensor l E M false).obj
        (DerivedCategory.Q.obj A.U, DerivedCategory.Q.obj A.V)) at hnT
    exact @hnT
  have heB : IsIso ((M.calculus false).adjunction.counit.app
      (DerivedCategory.Q.obj ((total l E X).obj (A.U, A.V)))) :=
    (NatTrans.isIso_app_iff_of_iso (M.calculus false).adjunction.counit
      (((M.system false).models.iso
        (coefficientSequenceTopology (Scheme.ProEt.topology X))
        (coefficientSequenceCommRingSheaf l E X) (M.system false).closed A.U A.V hU hV).symm)).1 heT
  refine ⟨r, (comparison l E r).hom_inv_id, (comparison l E r).inv_hom_id,
    ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [sourceReduction]
    infer_instance
  · dsimp only [targetReduction]
    infer_instance
  · exact reduction_conjugate (M.calculus false).adjunction r.a r.b
      (DerivedCategory.Q.mapIso A.c)
  · simpa only [comparison, Iso.trans_inv, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv,
      Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc, sites, sourceReduction,
      targetReduction] using reduction_conjugate (M.calculus false).adjunction r.b r.a
        (DerivedCategory.Q.mapIso A.c).symm
  · intro B r' d
    have ha := source_naturality l E M r r' d
    have hb := target_naturality l E M r r' d
    have hc : DerivedCategory.Q.map ((pullback l E f).map d.t) ≫
        (DerivedCategory.Q.mapIso B.c).hom =
      (DerivedCategory.Q.mapIso A.c).hom ≫
        DerivedCategory.Q.map ((total l E X).map (d.u, d.v)) := by
      simpa only [Functor.map_comp, Functor.mapIso_hom] using
        DerivedCategory.Q.congr_map d.square
    have hf : sourceMap l E d ≫ (comparison l E r').hom =
        (comparison l E r).hom ≫ targetMap l E d :=
      naturality_conjugate (coefficientSequenceLimit l E X)
      r.a r.b r'.a r'.b (DerivedCategory.Q.mapIso A.c) (DerivedCategory.Q.mapIso B.c)
      (sourceMap l E d) (targetMap l E d)
      (DerivedCategory.Q.map ((pullback l E f).map d.t))
      (DerivedCategory.Q.map ((total l E X).map (d.u, d.v))) ha hb hc
    refine ⟨ha, hb, hf, ?_, ?_⟩
    · apply (cancel_mono (comparison l E r').hom).1
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [hf, Iso.inv_hom_id_assoc]
    · intro ht hu hv
      let := ht
      let := hu
      let := hv
      constructor
      · dsimp only [sourceMap]
        infer_instance
      · dsimp only [targetMap]
        have : IsIso (Prod.mkHom
            ((coefficientSequenceLimit l E X).map (DerivedCategory.Q.map d.u))
            ((coefficientSequenceLimit l E X).map (DerivedCategory.Q.map d.v))) :=
          (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
        infer_instance

end WeilConjectures.IntegralTowerLimit
