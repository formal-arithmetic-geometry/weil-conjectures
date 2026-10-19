/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Sheaf.Paper.SmoothPurityNormalizedTowers
public import Sheaf.Paper.SmoothPurityTowerShriekLevels
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.KrullDimension
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import Sheaf.Paper.CompactSupportUniformTorBound
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.Paper.SmoothPurityTowerLevels
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite

/-!
# Compactly supported direct image preserves constructible towers

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower-bound,
statement and proof (blueprint: sk-lem-sp-tower-bound).

The sequence-site presentation is transported along its section-normalized equivalence
with the recorded coefficient towers. All natural indices denote the positive exponent n+1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The ordinary derived equivalence induced by the section-normalized presentation.
Source: blueprint, coefficient towers and compactification composite
(blueprint: sk-lem-sp-tower-bound). -/
def spTowerShriekRealization (b : SpTowerShriek.Base l E) (T : Scheme.{u})
    (D : SpCoefficientTowersAbelian l E T) :
    spDerivedCoefficientTowers l E T D ≌ SpTowerShriek.D l E T :=
  letI := D.hasDerived
  letI := b.realizationAdditive T
  (b.realization T).mapDerivedCategory

/-- The actual compactification operation, in the recorded coefficient-tower category.
It is exact termwise open extension followed by total derived proper direct image,
transported by the section-normalized equivalences on source and target.
Source: blueprint, displayed definition of Rf_!,bullet
(blueprint: sk-lem-sp-tower-bound). -/
def spTowerCompactSupport (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (DX : SpCoefficientTowersAbelian l E X) (DY : SpCoefficientTowersAbelian l E Y) :
    spDerivedCoefficientTowers l E X DX ⥤ spDerivedCoefficientTowers l E Y DY :=
  (spTowerShriekRealization l E b X DX).functor ⋙ SpTowerShriek.F l E b o c ⋙
    (spTowerShriekRealization l E b Y DY).inverse

private theorem spPushforwardSections {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K] (R : Sheaf K RingCat.{u + 1})
    (S : Sheaf J RingCat.{u + 1})
    (h : S = (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj R)
    (M : SheafOfModules.{u + 1} R) (U : Cᵒᵖ) :
    HEq (((SheafOfModules.pushforward (eqToHom h)).obj M).val.obj U)
      (M.val.obj (F.op.obj U)) := by
  subst S
  rfl

private theorem spPushforwardRestrictions {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K] (R : Sheaf K RingCat.{u + 1})
    (S : Sheaf J RingCat.{u + 1})
    (h : S = (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj R)
    (M : SheafOfModules.{u + 1} R) {U V : Cᵒᵖ} (a : U ⟶ V) :
    HEq (((SheafOfModules.pushforward (eqToHom h)).obj M).val.map a)
      (M.val.map (F.op.map a)) := by
  subst S
  rfl

private theorem spPushforwardMorphisms {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K] (R : Sheaf K RingCat.{u + 1})
    (S : Sheaf J RingCat.{u + 1})
    (h : S = (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj R)
    {M N : SheafOfModules.{u + 1} R} (a : M ⟶ N) (U : Cᵒᵖ) :
    HEq (((SheafOfModules.pushforward (eqToHom h)).map a).val.app U)
      (a.val.app (F.op.obj U)) := by
  subst S
  rfl

private theorem spConjugate {C : Type*} [Category C] {W X Y Z : C}
    (f : W ⟶ X) (g : Y ⟶ Z) (h : W = Y) (h' : X = Z) (he : HEq f g) :
    f ≫ eqToHom h' = eqToHom h ≫ g := by
  subst Y
  subst Z
  simpa using eq_of_heq he

private def spSectionwiseIso {A C : Type*} [Category A] [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u + 1}}
    (F G : A ⥤ SheafOfModules.{u + 1} R)
    (ho : ∀ (M : A) (U : Cᵒᵖ), HEq ((F.obj M).val.obj U) ((G.obj M).val.obj U))
    (hr : ∀ (M : A) {U V : Cᵒᵖ} (a : U ⟶ V),
      HEq ((F.obj M).val.map a) ((G.obj M).val.map a))
    (hm : ∀ {M N : A} (a : M ⟶ N) (U : Cᵒᵖ),
      HEq ((F.map a).val.app U) ((G.map a).val.app U)) : F ≅ G := by
  have h (M : A) (U : Cᵒᵖ) : (F.obj M).val.obj U = (G.obj M).val.obj U :=
    eq_of_heq (ho M U)
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · apply (SheafOfModules.fullyFaithfulForget R).preimageIso
    refine PresheafOfModules.isoMk (fun U ↦ eqToIso (h M U)) ?_
    intro U V a
    simp only [eqToIso.hom, eqToHom_map]
    exact spConjugate _ _ (h M U)
      (congrArg (ModuleCat.restrictScalars (R.obj.map a).hom).obj (h M V)) (hr M a)
  · intro M N a
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    exact spConjugate _ _ (h M U) (h N U) (hm a U)

private def spPushforwardIso {A C V : Type*}
    [Category A] [Category C] [Category V]
    {J : GrothendieckTopology C} {K : GrothendieckTopology V}
    (F : C ⥤ V) [F.IsContinuous J K] (R : Sheaf K RingCat.{u + 1})
    (S : Sheaf J RingCat.{u + 1})
    (h : S = (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj R)
    (L : A ⥤ SheafOfModules.{u + 1} R) (G : A ⥤ SheafOfModules.{u + 1} S)
    (ho : ∀ (M : A) (U : Cᵒᵖ),
      HEq ((L.obj M).val.obj (F.op.obj U)) ((G.obj M).val.obj U))
    (hr : ∀ (M : A) {U W : Cᵒᵖ} (a : U ⟶ W),
      HEq ((L.obj M).val.map (F.op.map a)) ((G.obj M).val.map a))
    (hm : ∀ {M N : A} (a : M ⟶ N) (U : Cᵒᵖ),
      HEq ((L.map a).val.app (F.op.obj U)) ((G.map a).val.app U)) :
    L ⋙ SheafOfModules.pushforward (eqToHom h) ≅ G := by
  apply spSectionwiseIso
  · intro M U
    exact (spPushforwardSections F R S h (L.obj M) U).trans (ho M U)
  · intro M U W a
    exact (spPushforwardRestrictions F R S h (L.obj M) a).trans (hr M a)
  · intro M N a U
    exact (spPushforwardMorphisms F R S h (L.map a) U).trans (hm a U)

-- Keep the fixed coefficient sheaves abstract during the sectionwise comparison.
section
attribute [local irreducible] spCoefficientCommRings spCoefficientRings constantSheaf

private def spTowerOrdinaryEvaluation (b : SpTowerShriek.Base l E) (T : Scheme.{u})
    (D : SpCoefficientTowersAbelian l E T) (n : ℕ) :
    (b.realization T).functor ⋙ SpTowerShriek.ev l E T n ≅
      spCoefficientEvaluation l E T D.equivalence n := by
  apply spPushforwardIso (Prod.sectR n T.ProEt) _ _
    (WeilConjectures.SemilinearSections.evaluation_ring
      (Scheme.ProEt.topology T) (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) n).symm
  · intro M U
    exact (b.sections T M n U).trans (D.sections M n U).symm
  · intro M U V a
    exact (b.restrictions T M
      (Prod.mkHom (𝟙 n) a.unop).op).trans (D.restrictions M n a).symm
  · intro M N a U
    exact (b.morphisms T a (Opposite.op (n, U.unop))).trans (D.morphisms a n U).symm

end

private def spTowerDerivedEvaluation (b : SpTowerShriek.Base l E) (T : Scheme.{u})
    (D : SpCoefficientTowersAbelian l E T) (n : ℕ) :
    (spTowerShriekRealization l E b T D).functor ⋙ SpTowerShriek.Ev l E T n ≅
      spDerivedCoefficientEvaluation l E T D n := by
  let := D.hasDerived
  let := b.realizationAdditive T
  let := D.equivalenceAdditive
  let := D.evaluationLimits n
  let := D.evaluationColimits n
  exact (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (spTowerOrdinaryEvaluation l E b T D n)

private def spTowerInverseEvaluation (b : SpTowerShriek.Base l E) (T : Scheme.{u})
    (D : SpCoefficientTowersAbelian l E T) (n : ℕ) :
    (spTowerShriekRealization l E b T D).inverse ⋙
        spDerivedCoefficientEvaluation l E T D n ≅ SpTowerShriek.Ev l E T n :=
  Functor.isoWhiskerLeft _ (spTowerDerivedEvaluation l E b T D n).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (spTowerShriekRealization l E b T D).counitIso _ ≪≫
    Functor.leftUnitor _

private def spTowerCompactSupportEvaluation
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (DX : SpCoefficientTowersAbelian l E X) (DY : SpCoefficientTowersAbelian l E Y)
    (n : ℕ) :
    spTowerCompactSupport l E b o c DX DY ⋙ spDerivedCoefficientEvaluation l E Y DY n ≅
      spDerivedCoefficientEvaluation l E X DX n ⋙ SpTowerShriek.finiteF l E b c n :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
      (spTowerInverseEvaluation l E b Y DY n)) ≪≫
    Functor.isoWhiskerLeft _ (SpTowerShriek.Fcomparison l E b o c n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (spTowerDerivedEvaluation l E b X DX n) _

private theorem spSystemHomExt {V : Type*} [Category V]
    {J : GrothendieckTopology V}
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [HasSheafify J AddCommGrpCat.{u + 1}]
    {B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{u + 1}}
    {M N : SheafOfModules.StrictRingSystem B}
    (f g : M ⟶ N) (h : ∀ n, f.app n = g.app n) : f = g := by
  have he : f.app = g.app := funext h
  exact match f, g, he with
    | ⟨f, hf⟩, ⟨g, hg⟩, he => by
      cases he
      rfl

private theorem spTowerLowerBound (T : Scheme.{u})
    (D : SpCoefficientTowersAbelian l E T) (C : spDerivedCoefficientTowers l E T D)
    (a : ℤ) (h : ∀ n : ℕ, ∀ i : ℤ, i < a → IsZero
      ((@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) i).obj
        ((spDerivedCoefficientEvaluation l E T D n).obj C))) :
    @DerivedCategory.IsGE _ _ _ D.hasDerived C a := by
  let := D.hasDerived
  let := D.equivalenceAdditive
  apply (DerivedCategory.isGE_iff C a).2
  intro i hi
  let H := (DerivedCategory.homologyFunctor (spCoefficientTowers l E T) i).obj C
  apply IsZero.of_full_of_faithful_of_isZero D.equivalence.functor
  apply (IsZero.iff_id_eq_zero _).2
  have hlevel (n : ℕ) : IsZero ((D.equivalence.functor.obj H).level n) := by
    let := D.evaluationLimits n
    let := D.evaluationColimits n
    let : (spCoefficientEvaluation l E T D.equivalence n).Additive :=
      Functor.additive_of_preserves_binary_products _
    exact (h n i hi).of_iso
      (((spCoefficientEvaluation l E T D.equivalence n).mapDerivedCategoryHomologyFunctorIso
        i).app C)
  apply spSystemHomExt
  intro n
  exact (hlevel n).eq_of_src _ _

private def spFiniteSupportComparison (b : SpTowerShriek.Base l E)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) [QuasiCompact c.i] (n : ℕ) :
    SpTowerShriek.finiteF l E b c n ≅
      Scheme.proEtaleRingCompactSupportImage c
        (Scheme.proEtaleConstantRing Y (SpTowerShriek.R l E n))
        (Scheme.proEtaleConstantRing c.Z (SpTowerShriek.R l E n))
        (Scheme.proEtaleConstantRing X (SpTowerShriek.R l E n))
        (Scheme.proEtaleConstantRingComparison c.g (SpTowerShriek.R l E n))
        (Scheme.proEtaleConstantRingComparison c.i (SpTowerShriek.R l E n)) := by
  let a := SpTowerShriek.finiteOpenAdjunction l E b c.i n
  let a' := Adjunction.ofIsRightAdjoint
    (Scheme.proEtaleConstantRingPullback (SpTowerShriek.R l E n) c.i)
  change Scheme.sfIntrinsicDerivedOpen (SpTowerShriek.R l E n) c.i ⋙ _ ≅
    Scheme.proEtaleRingDerivedOpenExtension c.i _ _ _ ⋙ _
  exact Functor.isoWhiskerRight
    (Functor.mapDerivedCategoryNatIso
      (show Scheme.sfIntrinsicExtensionByZero c.i (SpTowerShriek.R l E n) ≅
        Scheme.proEtaleRingOpenExtension c.i _ _ _ from a.leftAdjointUniq a')) _

private theorem spAmplitudeIso (T : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : Scheme.proEtaleDerivedCategory T A} (e : K ≅ L) (a b : ℤ)
    (h : Scheme.HasProEtaleTorAmplitude T A K a b) :
    Scheme.HasProEtaleTorAmplitude T A L a b := by
  refine ⟨h.1, ?_⟩
  intro N P hN f hf hP M i hi
  obtain ⟨q⟩ := hN
  exact h.2 N P ⟨q ≪≫ e.symm⟩ f hf hP M i hi

private theorem spConstructibleSheafIso (T : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A]
    {M N : Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T A)} (e : M ≅ N)
    (h : Scheme.IsConstructibleProEtaleModuleSheaf T A M) :
    Scheme.IsConstructibleProEtaleModuleSheaf T A N := by
  obtain ⟨S, hS, h⟩ := h
  refine ⟨S, hS, fun i ↦ ?_⟩
  let F := Scheme.proEtaleConstantRingPullback A (S.immersion i)
  have ei := F.mapIso e
  obtain ⟨hlc, hfin⟩ := h i
  constructor
  · obtain ⟨I, U, f, hf, hU⟩ := hlc
    refine ⟨I, U, f, hf, fun j ↦ ?_⟩
    obtain ⟨V, ⟨ej⟩⟩ := hU j
    exact ⟨V, ⟨(SheafOfModules.overFunctor _ (U j)).mapIso ei.symm ≪≫ ej⟩⟩
  · intro Ω _ _ y
    let O := Scheme.proEtaleConstantRing (S.domain i) A
    let G := SheafOfModules.forget
      ((sheafCompose (Scheme.ProEt.topology (S.domain i))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O) ⋙
      PresheafOfModules.pushforward₀ (Scheme.proEtaleGeometricNeighbourhoodForget y)
        (O.obj ⋙ forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
      PresheafOfModules.colimitFunctor
        (colimit.isColimit (Scheme.proEtaleGeometricStalkRingDiagram y O))
    let e' := G.mapIso ei
    let : Finite (G.obj (F.obj M)) := hfin Ω y
    exact Finite.of_equiv _ ((forget _).mapIso e').toEquiv

-- Transport uses the proved interfaces without unfolding geometric stalks or K-flat tests.
attribute [local irreducible] Scheme.HasProEtaleTorAmplitude
  Scheme.IsConstructibleProEtaleModuleSheaf

private theorem spFiniteCtfIso (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    {K L : Scheme.proEtaleDerivedCategory T A} (e : K ≅ L)
    (h : spFiniteConstructibleTor T A K) : spFiniteConstructibleTor T A L := by
  obtain ⟨⟨a, b, hab, hv⟩, hc, ⟨c, d, ht⟩⟩ := h
  exact ⟨⟨a, b, hab, fun i hi ↦ (hv i hi).of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso e).symm⟩,
    fun i ↦ spConstructibleSheafIso T A ((DerivedCategory.homologyFunctor _ i).mapIso e)
      (hc i), c, d, spAmplitudeIso T A e c d ht⟩

-- Derived comparisons are used through their natural-isomorphism interfaces.
attribute [local irreducible] spTowerOrdinaryEvaluation spTowerDerivedEvaluation
  spTowerInverseEvaluation spTowerCompactSupportEvaluation spFiniteSupportComparison

/-- Compact support preserves the unnormalized constructible finite-Tor tower category.
The first clause gives the bounded-below domain and codomain of the displayed functor;
the second is its natural level identification; the third is preservation of Dctf.
Both smooth pure dimension d and the stated general fibre bound are included.

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower-bound,
statement and the uniform-interval proof (blueprint: sk-lem-sp-tower-bound).

Proof:
1. Use the common cohomological interval in spConstructibleTorTowers. Exact level
   evaluation commutes with derived homology; the strict-system equivalence reflects
   zero objects, and identities of strict systems are detected componentwise. This
   proves the input lower bound.
2. Compare the two section-normalized ordinary evaluations, derive their natural
   isomorphism, and conjugate Fcomparison by the realization unit and counit. Exact
   realization and open extension preserve a lower bound. Compatibility of total
   right derivation with D+ gives the bounded-below output.
3. Apply compactSupport_uniform_tor_bound. Smooth relative dimension gives the
   geometric fibre bound; in the general case specialize to algebraic closures of
   residue fields. Each positive ell-power quotient is finite and killed by that
   power of ell. Uniqueness of open-extension left adjoints identifies finiteF with
   the finite compact-support operation, so its constructibility conclusion applies.
4. The tower clause of the uniform theorem gives output Tor amplitude and homology
   vanishing in [r,t+2d]. Transport these along the inverse-realization evaluation
   comparison and combine them with finite-level constructibility. No normalization
   condition is used. -/
theorem sp_tower_bound
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] (_hlp : l ≠ p)
    (X Y : Over (Spec (CommRingCat.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (d : ℕ) (_hd : SmoothOfRelativeDimension d f.left ∨
      ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (CommRingCat.of Ω) ⟶ Y.left),
        topologicalKrullDim (pullback f.left s : Scheme.{u}) ≤ (d : WithBot ℕ∞))
    (c : Compactification f.left)
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (DX : SpCoefficientTowersAbelian l E X.left)
    (DY : SpCoefficientTowersAbelian l E Y.left) :
    (∀ C : spDerivedCoefficientTowers l E X.left DX,
      (∃ a : ℤ, @DerivedCategory.IsGE (spCoefficientTowers l E X.left) _ _ DX.hasDerived C a) →
      ∃ a : ℤ, @DerivedCategory.IsGE (spCoefficientTowers l E Y.left) _ _ DY.hasDerived
        ((spTowerCompactSupport l E b o c DX DY).obj C) a) ∧
    (∀ n : ℕ, Nonempty
      (@DerivedCategory.Plus.ι (spCoefficientTowers l E X.left) _ _ DX.hasDerived ⋙
          spTowerCompactSupport l E b o c DX DY ⋙ spDerivedCoefficientEvaluation l E Y.left DY n ≅
        @DerivedCategory.Plus.ι (spCoefficientTowers l E X.left) _ _ DX.hasDerived ⋙
          spDerivedCoefficientEvaluation l E X.left DX n ⋙ SpTowerShriek.finiteF l E b c n)) ∧
    (∀ C : spDerivedCoefficientTowers l E X.left DX,
      spConstructibleTorTowers l E X.left DX C →
      (∃ a : ℤ, @DerivedCategory.IsGE (spCoefficientTowers l E X.left) _ _ DX.hasDerived C a) ∧
      spConstructibleTorTowers l E Y.left DY ((spTowerCompactSupport l E b o c DX DY).obj C)) := by
  classical
  let := DX.hasDerived
  let := DY.hasDerived
  let := b.realizationAdditive X.left
  let := b.realizationAdditive Y.left
  let := (b.calculus c.Z).grothendieck
  have hbounded (C : spDerivedCoefficientTowers l E X.left DX)
      (hC : ∃ a : ℤ, C.IsGE a) :
      ∃ a : ℤ, ((spTowerCompactSupport l E b o c DX DY).obj C).IsGE a := by
    obtain ⟨a, ha⟩ := hC
    let := ha
    let K := (spTowerShriekRealization l E b X.left DX).functor.obj C
    have hK : K.IsGE a := (b.realization X.left).functor.isGE_mapDerivedCategory_obj C a
    let := hK
    let L := (SpTowerShriek.openD l E b (o.openOp c.i)).obj K
    have hL : L.IsGE a := (o.openOp c.i).extension.isGE_mapDerivedCategory_obj K a
    let := hL
    let Lplus : DerivedCategory.Plus (SpTowerShriek.S l E c.Z) :=
      ⟨L, a, inferInstanceAs (DerivedCategory.TStructure.t.IsGE L a)⟩
    let P := (o.geometry c.g).push.rightDerivedFunctorPlus.obj Lplus
    obtain ⟨m, hm⟩ := P.property
    have hP' : DerivedCategory.TStructure.t.IsGE
        (((o.geometry c.g).push.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).obj Lplus) m := hm
    let := hP'
    let e := (o.geometry c.g).push.rightDerivedFunctorPlusCompatibility.app Lplus
    have hF : ((SpTowerShriek.F l E b o c).obj K).IsGE m :=
      DerivedCategory.TStructure.t.isGE_of_iso e m
    let := hF
    exact ⟨m, (b.realization Y.left).inverse.isGE_mapDerivedCategory_obj
      ((SpTowerShriek.F l E b o c).obj K) m⟩
  refine ⟨hbounded, ?_, ?_⟩
  · intro n
    exact ⟨Functor.isoWhiskerLeft _
      (spTowerCompactSupportEvaluation l E b o c DX DY n)⟩
  · intro C hC
    obtain ⟨hfinite, a, z, r, t, haz, hrt, hinterval⟩ := hC
    have hbelow : C.IsGE a := spTowerLowerBound l E X.left DX C a
      (fun n i hi ↦ (hinterval n).1 i (Or.inl hi))
    refine ⟨⟨a, hbelow⟩, ?_⟩
    let := c.quasiCompact_openImmersion inferInstance
    have hdim (y : Y.left) : topologicalKrullDim
        (pullback f.left (Spec.map (CommRingCat.ofHom
          (algebraMap (Y.left.residueField y) (AlgebraicClosure (Y.left.residueField y)))) ≫
            Y.left.fromSpecResidueField y) : Scheme.{u}) ≤ (d : WithBot ℕ∞) := by
      rcases _hd with hs | hg
      · let := hs
        exact topologicalKrullDim_le_of_smoothOfRelativeDimension (pullback.snd _ _) d
      · exact hg _ _
    let : X.left.Over (Spec (CommRingCat.of k)) := ⟨X.hom⟩
    let : Y.left.Over (Spec (CommRingCat.of k)) := ⟨Y.hom⟩
    let : IsSeparated (X.left ↘ Spec (CommRingCat.of k)) := ‹IsSeparated X.hom›
    let : LocallyOfFiniteType (X.left ↘ Spec (CommRingCat.of k)) :=
      ‹LocallyOfFiniteType X.hom›
    let : QuasiCompact (X.left ↘ Spec (CommRingCat.of k)) := ‹QuasiCompact X.hom›
    let : IsSeparated (Y.left ↘ Spec (CommRingCat.of k)) := ‹IsSeparated Y.hom›
    let : LocallyOfFiniteType (Y.left ↘ Spec (CommRingCat.of k)) :=
      ‹LocallyOfFiniteType Y.hom›
    let : QuasiCompact (Y.left ↘ Spec (CommRingCat.of k)) := ‹QuasiCompact Y.hom›
    have hu := compactSupport_uniform_tor_bound p l k _hlp X.left Y.left f.left c d
      hdim r t hrt
    let K := (spTowerShriekRealization l E b X.left DX).functor.obj C
    have hK (n : ℕ) : spFiniteConstructibleTor X.left (SpTowerShriek.R l E n)
        ((SpTowerShriek.Ev l E X.left n).obj K) ∧
        Scheme.HasProEtaleTorAmplitude X.left (SpTowerShriek.R l E n)
          ((SpTowerShriek.Ev l E X.left n).obj K) r t := by
      let e := (spTowerDerivedEvaluation l E b X.left DX n).app C
      exact ⟨spFiniteCtfIso X.left _ e.symm (hfinite n),
        spAmplitudeIso X.left _ e.symm r t (hinterval n).2⟩
    have hout := hu.2 E b o K hK
    have hfiniteOut (n : ℕ) : spFiniteConstructibleTor Y.left (SpTowerShriek.R l E n)
        ((spDerivedCoefficientEvaluation l E Y.left DY n).obj
          ((spTowerCompactSupport l E b o c DX DY).obj C)) := by
      have hkilled : ∃ q : ℕ, 0 < q ∧ (l : SpTowerShriek.R l E n) ^ q = 0 := by
        refine ⟨n + 1, Nat.succ_pos _, ?_⟩
        change (Ideal.Quotient.mk (spEllIdeal l E ^ (n + 1))
          (l : Padic.coefficientExtensionIntegers l E)) ^ (n + 1) = 0
        rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton _)) _
      have hn := (hu.1 (SpTowerShriek.R l E n) hkilled
        ((spDerivedCoefficientEvaluation l E X.left DX n).obj C)
        (hfinite n) (hinterval n).2).1
      let e := (spTowerCompactSupportEvaluation l E b o c DX DY n).app C ≪≫
        (spFiniteSupportComparison l E b c n).app
          ((spDerivedCoefficientEvaluation l E X.left DX n).obj C)
      exact spFiniteCtfIso Y.left _ e.symm hn
    refine ⟨hfiniteOut, r, t + 2 * (d : ℤ), r, t + 2 * (d : ℤ), ?_, ?_, ?_⟩
    · omega
    · omega
    · intro n
      let e := (spTowerInverseEvaluation l E b Y.left DY n).app
        ((SpTowerShriek.F l E b o c).obj K)
      constructor
      · intro q hq
        exact ((hout n).2 q hq).of_iso ((DerivedCategory.homologyFunctor _ q).mapIso e)
      · exact spAmplitudeIso Y.left _ e.symm r (t + 2 * (d : ℤ)) (hout n).1

end AlgebraicGeometry.ProEtale

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
