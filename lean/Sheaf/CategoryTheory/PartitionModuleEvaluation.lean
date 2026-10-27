/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Sheaf.CategoryTheory.PartitionRefinementSheafification
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Mathlib.CategoryTheory.Sites.Coherent.ExtensiveColimits
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small

/-! # Exact evaluation at a partition object

Source: Hemo--Richarz--Scholbach, Lemma 4.1(1); Stacks Tags 0F63, 03DA,
03DB, 079P and 015F, arbitrary commutative ring-sheaf extension
(blueprint: lem-zl-partition-module-evaluation-localization).
-/

@[expose] public section

set_option autoImplicit false

universe u v w d₁ d₂

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : Precoverage C)

/-- The underlying ring sheaf, using the canonical forgetful functor.
Source: Stacks, Modules on Sites, Tag 03CY
(blueprint: lem-zl-partition-module-evaluation-localization). -/
def partitionModuleRings (O : Sheaf J.toGrothendieck CommRingCat.{max u v w}) :=
  (sheafCompose J.toGrothendieck
    (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})).obj O

/-- The functor E(M) = M(W), over A = O(W), using Mathlib evaluation.
Source: Hemo--Richarz--Scholbach, Lemma 4.1(1)
(blueprint: lem-zl-partition-module-evaluation-localization). -/
abbrev partitionModuleEvaluation
    (O : Sheaf J.toGrothendieck CommRingCat.{max u v w}) (W : C) :
    ringedSiteModules.{max u v w} (partitionModuleRings J O) ⥤
      ModuleCat.{max u v w} ((partitionModuleRings J O).obj.obj (op W)) :=
  SheafOfModules.evaluation.{max u v w} (partitionModuleRings J O) (op W)

variable [HasPullbacks C] [HasFiniteCoproducts C] [HasStrictInitialObjects C]
  [hJ : Fact J.IsSiteForCoverings]
  [hdisjoint : Fact (∀ (n : ℕ) (U : Fin n → C) (X : C) (j : ∀ a, U a ⟶ X),
    IsColimit (Cofan.mk X j) → ∀ (a b : Fin n), a ≠ b →
      Nonempty (IsInitial (pullback (j a) (j b))))]
  [hstable : Fact (∀ (n : ℕ) (U : Fin n → C) (X : C) (j : ∀ a, U a ⟶ X),
    IsColimit (Cofan.mk X j) → ∀ (Y : C) (f : Y ⟶ X),
      Nonempty (IsColimit (Cofan.mk Y (fun a ↦ pullback.snd (j a) f))))]
  [hcover : Fact (∀ (n : ℕ) (U : Fin n → C) (X : C) (j : ∀ a, U a ⟶ X),
    IsColimit (Cofan.mk X j) → Presieve.ofArrows U j ∈ J X)]
  (W : C)
  [hrefine : Fact (∀ (S : Presieve W), S ∈ J W →
    ∃ (n : ℕ) (U : Fin n → C) (j : ∀ a, U a ⟶ W),
      Nonempty (IsColimit (Cofan.mk W j)) ∧
      ∀ a, ∃ (V : C) (f : V ⟶ W), S f ∧ ∃ h : U a ⟶ V, h ≫ f = j a)]
  (O : Sheaf J.toGrothendieck CommRingCat.{max u v w})
  [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}]
  [J.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]

/-- O placed in degree zero, for the unit normalization.
Source: HRS Lemma 4.1(1), Stacks Tag 015F
(blueprint: lem-zl-partition-module-evaluation-localization). -/
noncomputable abbrev partitionModuleUnitComplex
    (O : Sheaf J.toGrothendieck CommRingCat.{max u v w}) :=
  (CochainComplex.singleFunctor
    (ringedSiteModules (partitionModuleRings J O)) 0).obj
      (SheafOfModules.unit (partitionModuleRings J O))

include hJ hdisjoint hstable hcover hrefine

omit [HasFiniteCoproducts C] [HasStrictInitialObjects C] hJ hcover hrefine
  [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}]
  [J.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
private theorem partition_inclusion_mono
    (n : ℕ) (U : Fin n → C) (X : C) (j : ∀ a, U a ⟶ X)
    (hc : IsColimit (Cofan.mk X j)) (a : Fin n) : Mono (j a) := by
  classical
  obtain ⟨hp⟩ := hstable.out n U X j hc (U a) (j a)
  let t : ∀ b, pullback (j b) (j a) ⟶ U a := fun b ↦
    if h : b = a then
      eqToHom (congrArg (fun b ↦ pullback (j b) (j a)) h) ≫ pullback.fst (j a) (j a)
    else (hdisjoint.out n U X j hc b a h).some.to (U a)
  let r : U a ⟶ U a := hp.desc (Cofan.mk (U a) t)
  have hr : pullback.snd (j a) (j a) ≫ r = pullback.fst (j a) (j a) := by
    simpa [r, t] using hp.fac (Cofan.mk (U a) t) ⟨a⟩
  have hid : r = 𝟙 (U a) := by
    have h := congrArg (fun f ↦ pullback.lift (𝟙 (U a)) (𝟙 (U a)) rfl ≫ f) hr
    simpa only [← Category.assoc, pullback.lift_snd, pullback.lift_fst,
      Category.id_comp] using h
  have heq : pullback.snd (j a) (j a) = pullback.fst (j a) (j a) := by
    simpa [hid] using hr
  constructor
  intro Z f g hfg
  have h := congrArg (fun k ↦ pullback.lift f g hfg ≫ k) heq
  simpa using h.symm

omit hJ hrefine [HasStrictInitialObjects C]
  [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}]
  [J.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
private theorem partition_sheaf_products
    (M : ringedSiteModules.{max u v w} (partitionModuleRings J O)) :
    PreservesFiniteProducts M.val.presheaf := by
  classical
  let P := M.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{max u v w}
  have hs : Presieve.IsSheaf J.toGrothendieck P :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      ((sheafCompose J.toGrothendieck
        (CategoryTheory.forget AddCommGrpCat.{max u v w})).obj
          ((SheafOfModules.toSheaf _).obj M)).property
  have hempty : (Presieve.ofArrows (X := ⊥_ C) (Empty.elim : Empty → C)
      Empty.instIsEmpty.elim).IsSheafFor P := by
    apply hs.isSheafFor_of_mem_precoverage
    let U₀ : Fin 0 → C := Fin.elim0
    let j₀ : ∀ a, U₀ a ⟶ ⊥_ C := fun a ↦ a.elim0
    have hc : IsColimit (Cofan.mk (⊥_ C) j₀) :=
      (isColimitEquivIsInitialOfIsEmpty C (Cofan.mk (⊥_ C) j₀)).symm initialIsInitial
    have h := hcover.out 0 U₀ (⊥_ C) j₀ hc
    convert h using 1
    funext Z f
    apply propext
    constructor
    · rintro ⟨a⟩
      exact a.elim
    · rintro ⟨a⟩
      exact a.elim0
  have hP : PreservesFiniteProducts P := by
    refine ⟨fun n ↦ ⟨fun {K} ↦ ?_⟩⟩
    let U : Fin n → C := fun a ↦ (K.obj ⟨a⟩).unop
    let j : ∀ a, U a ⟶ ∐ U := fun a ↦ Sigma.ι U a
    have hc := coproductIsCoproduct U
    have : ∀ a, Mono ((Cofan.mk (∐ U) j).inj a) := fun a ↦
      partition_inclusion_mono n U (∐ U) j hc a
    have hd : Pairwise (fun a b ↦
        IsPullback (initial.to (U a)) (initial.to (U b)) (j a) (j b)) := by
      intro a b hab
      let hi := (hdisjoint.out n U (∐ U) j hc a b hab).some
      exact IsPullback.of_iso_pullback (by simp)
        (initialIsInitial.uniqueUpToIso hi)
        (initialIsInitial.hom_ext _ _) (initialIsInitial.hom_ext _ _)
    have hp := Presieve.preservesProduct_of_isSheafFor P hempty initialIsInitial
      (Cofan.mk (∐ U) j) hc hd
      (hs.isSheafFor_of_mem_precoverage (hcover.out n U (∐ U) j hc))
    let e : K ≅ Discrete.functor (fun a ↦ op (U a)) := Discrete.natIsoFunctor
    exact preservesLimit_of_iso_diagram P e.symm
  exact preservesFiniteProducts_of_reflects_of_preserves M.val.presheaf
    (CategoryTheory.forget AddCommGrpCat.{max u v w})

/-- Sectionwise module colimits send the empty object to zero, preserve finite
partitions, and their linear sheafification unit is invertible at W.
Source: HRS Lemma 4.1(1), Stacks Tags 0F63, 03CY and 03DB
(blueprint: lem-zl-partition-module-evaluation-localization).

Proof: (1) For each sheaf and finite decomposition, glue by zero off one component.
Restrictions r_a and these extensions j_a satisfy r_a j_b = delta_ab and sum j_a r_a = 1.
The empty covering gives zero sections on the initial object.
(2) Present each module colimit by the direct sum modulo the arrow relations.
Restrictions and zero extensions descend to that quotient, retaining these identities.
Their finite sum is inverse to the product restriction map. The empty diagram gives zero.
(3) Module sheafification has underlying abelian sheafification. Forgetting further to sets
is the set sheafification, compatibly with the unit, by
lem-pc-sites-sheafification-underlying-sets. Apply
lem-zl-partition-refinement-sheafification to the underlying set presheaf.
The resulting bijection is linear and therefore is an isomorphism of A-modules. -/
theorem partitionModuleColimit_sections
    (I : Type (max u v w)) [SmallCategory I]
    (F : I ⥤ ringedSiteModules (partitionModuleRings J O)) :
    Subsingleton ((PresheafOfModules.colimitPresheafOfModules
      (F ⋙ SheafOfModules.forget (partitionModuleRings J O))).obj (op (⊥_ C))) ∧
    (∀ (n : ℕ) (U : Fin n → C) (X : C) (j : ∀ a, U a ⟶ X),
      IsColimit (Cofan.mk X j) →
        Function.Bijective (fun s : (PresheafOfModules.colimitPresheafOfModules
          (F ⋙ SheafOfModules.forget (partitionModuleRings J O))).obj (op X) ↦
          fun a ↦ (PresheafOfModules.colimitPresheafOfModules
            (F ⋙ SheafOfModules.forget (partitionModuleRings J O))).map (j a).op s)) ∧
    (∃ e : sheafify J.toGrothendieck
        ((PresheafOfModules.colimitPresheafOfModules
          (F ⋙ SheafOfModules.forget (partitionModuleRings J O))).presheaf ⋙
            CategoryTheory.forget AddCommGrpCat.{max u v w}) ≅
        (((PresheafOfModules.sheafification (𝟙 (partitionModuleRings J O).obj)).obj
          (PresheafOfModules.colimitPresheafOfModules
            (F ⋙ SheafOfModules.forget (partitionModuleRings J O)))).val.presheaf ⋙
              CategoryTheory.forget AddCommGrpCat.{max u v w}),
      toSheafify J.toGrothendieck
          ((PresheafOfModules.colimitPresheafOfModules
            (F ⋙ SheafOfModules.forget (partitionModuleRings J O))).presheaf ⋙
              CategoryTheory.forget AddCommGrpCat.{max u v w}) ≫ e.hom =
        Functor.whiskerRight (toSheafify J.toGrothendieck
          (PresheafOfModules.colimitPresheafOfModules
            (F ⋙ SheafOfModules.forget (partitionModuleRings J O))).presheaf)
          (CategoryTheory.forget AddCommGrpCat.{max u v w})) ∧
    IsIso (((PresheafOfModules.sheafificationAdjunction
      (𝟙 (partitionModuleRings J O).obj)).unit.app
        (PresheafOfModules.colimitPresheafOfModules
          (F ⋙ SheafOfModules.forget (partitionModuleRings J O)))).app (op W)) := by
  -- Finite products are biproducts, so colimits preserve them directly; no quotient
  -- presentation is needed for the first two clauses.
  classical
  have : EssentiallySmall.{max u v w} C := essentiallySmallSelf.{w} C
  have : ∀ X : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow X (equivSmallModel.{max u v w} C).inverse.op)
        AddCommGrpCat.{max u v w} := fun _ ↦ hasLimitsOfShape_of_essentiallySmall _ _
  have : ∀ X : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow X (equivSmallModel.{max u v w} C).inverse.op)
        (Type (max u v w)) := fun _ ↦ hasLimitsOfShape_of_essentiallySmall _ _
  have : J.toGrothendieck.PreservesSheafification
      (CategoryTheory.forget AddCommGrpCat.{max u v w}) := inferInstance
  let R := partitionModuleRings J O
  let D := F ⋙ SheafOfModules.forget R
  let P := PresheafOfModules.colimitPresheafOfModules D
  let G := D ⋙ PresheafOfModules.toPresheaf R.obj
  have : ∀ i : I, PreservesFiniteProducts (G.obj i) := fun i ↦
    partition_sheaf_products J O (F.obj i)
  have : PreservesFiniteProducts G.flip :=
    ⟨fun n ↦ preservesLimitsOfShape_of_evaluation _ _ (fun i ↦
      inferInstanceAs (PreservesLimitsOfShape (Discrete (Fin n)) (G.obj i)))⟩
  have : PreservesFiniteProducts (G.flip ⋙ colim) := inferInstance
  let e : P.presheaf ≅ G.flip ⋙ colim :=
    (isColimitOfPreserves (PresheafOfModules.toPresheaf R.obj)
      (PresheafOfModules.isColimitColimitCocone D)).coconePointUniqueUpToIso
        (pointwiseIsColimit G)
  have : PreservesFiniteProducts P.presheaf :=
    ⟨fun n ↦ preservesLimitsOfShape_of_natIso e.symm⟩
  let Q := P.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{max u v w}
  have : PreservesFiniteProducts Q := inferInstance
  have hprod : ∀ (n : ℕ) (U : Fin n → C) (X : C) (j : ∀ a, U a ⟶ X),
      IsColimit (Cofan.mk X j) →
        Function.Bijective (fun s : Q.obj (op X) ↦ fun a ↦ Q.map (j a).op s) := by
    intro n U X j hc
    let l : IsLimit (Fan.mk (Q.obj (op X)) (fun a ↦ Q.map (j a).op)) :=
      isLimitFanMkObjOfIsLimit Q _ _ (Cofan.IsColimit.op hc)
    let e : Q.obj (op X) ≅ (∀ a, Q.obj (op (U a))) :=
      l.conePointUniqueUpToIso
        (Types.productLimitCone (fun a ↦ Q.obj (op (U a)))).isLimit
    have he : (fun s : Q.obj (op X) ↦ fun a ↦ Q.map (j a).op s) =
        (fun s ↦ e.hom s) := by
      funext x a
      exact (ConcreteCategory.congr_hom
        (l.conePointUniqueUpToIso_hom_comp
          (Types.productLimitCone (fun a ↦ Q.obj (op (U a)))).isLimit ⟨a⟩) x).symm
    rw [he]
    exact ConcreteCategory.bijective_of_isIso e.hom
  have ht := IsTerminal.isTerminalObj Q _ initialIsInitial.op
  have hsub : Subsingleton (Q.obj (op (⊥_ C))) := by
    have : Unique (Q.obj (op (⊥_ C))) := Types.isTerminalEquivUnique _ ht
    infer_instance
  let e' := sheafifyComposeIso J.toGrothendieck
    (CategoryTheory.forget AddCommGrpCat.{max u v w}) P.presheaf
  have hb := (bijective_toSheafify_of_partition_refinement J hJ.out hdisjoint.out
    hstable.out hcover.out W hrefine.out Q ⟨⟨0⟩, hsub⟩ hprod).1
  have hunit : Function.Bijective
      ((Functor.whiskerRight (toSheafify J.toGrothendieck P.presheaf)
        (CategoryTheory.forget AddCommGrpCat.{max u v w})).app (op W)) := by
    rw [← sheafComposeIso_hom_fac]
    exact (ConcreteCategory.bijective_of_isIso (e'.hom.app (op W))).comp hb
  refine ⟨hsub, hprod, ⟨e', sheafComposeIso_hom_fac _ _ _⟩, ?_⟩
  exact (ConcreteCategory.isIso_iff_bijective _).mpr hunit

/-- Evaluation preserves every small colimit, including the empty one.
Source: HRS Lemma 4.1(1), Stacks Tags 0F63 and 03DB
(blueprint: lem-zl-partition-module-evaluation-localization).

Proof: By lem-weil-pbc-module-sheaves-colimits-forgetful the colimit is the
sheafification of the sectionwise module colimit. Its canonical comparison at W
is exactly the linear unit of partitionModuleColimit_sections, hence invertible.
The comparison is natural because the sheafification unit and colimit maps are natural. -/
@[instance] theorem partitionModuleEvaluation_preservesColimits :
    PreservesColimitsOfSize.{max u v w, max u v w} (partitionModuleEvaluation J O W) := by
  constructor
  intro I hI
  constructor
  intro F
  let R := partitionModuleRings J O
  let E := partitionModuleEvaluation J O W
  let c := PresheafOfModules.colimitCocone (F ⋙ SheafOfModules.forget R)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  let u := (adj.unit.app c.pt).app (op W)
  have : IsIso u := (partitionModuleColimit_sections J W O I F).2.2.2
  obtain ⟨s, ⟨hs⟩, e, he⟩ :=
    (moduleSheaves_colimits_forgetful R).2.2.2.2.2 I |>.2.2.2 F
  have hh (i : I) :
      E.map (s.ι.app i) ≫ E.map e.hom = (c.ι.app i).app (op W) ≫ u := by
    apply (forget₂ _ AddCommGrpCat).map_injective
    exact congrArg (fun η ↦ η.app (op W)) (he i)
  let e' : (PresheafOfModules.evaluation R.obj (op W)).mapCocone c ≅ E.mapCocone s :=
    Cocone.ext (asIso u ≪≫ (E.mapIso e).symm) (fun i ↦ by
      apply (cancel_mono (E.map e.hom)).1
      dsimp only [R, E, u, c, adj] at *
      change (c.ι.app i).app (op W) ≫ (u ≫ E.map e.inv) ≫ E.map e.hom = _
      simp only [Category.assoc, ← Functor.map_comp, e.inv_hom_id,
        Functor.map_id]
      exact (hh i).symm)
  exact preservesColimit_of_preserves_colimit_cocone hs
    (IsColimit.ofIsoColimit
      (isColimitOfPreserves (PresheafOfModules.evaluation R.obj (op W))
        (PresheafOfModules.isColimitColimitCocone _)) e')

set_option linter.unusedSectionVars false in
/-- Evaluation is additive, since morphism addition is sectionwise.
Source: Stacks Tag 03DA
(blueprint: lem-zl-partition-module-evaluation-localization).
Proof: evaluate the sectionwise sum of two linear natural maps at W. The result
is their sum as A-linear maps; zero is treated in the same way. -/
@[instance] theorem partitionModuleEvaluation_additive :
    (partitionModuleEvaluation J O W).Additive := by
  dsimp only [partitionModuleEvaluation, SheafOfModules.evaluation]
  infer_instance

/-- Exactness: evaluation preserves finite colimits as well as sectionwise finite limits.
Source: Stacks Tags 03DA and 03DB; HRS Lemma 4.1(1)
(blueprint: lem-zl-partition-module-evaluation-localization).

Proof: The preceding colimit assertion includes cokernels and the zero object.
Kernels are sectionwise by lem-weil-pbc-module-sheaves-limits-sectionwise.
Evaluation is additive because addition is sectionwise. Since images are kernels
of cokernels, it preserves exact sequences. Finite colimits are in particular preserved. -/
@[instance] theorem partitionModuleEvaluation_preservesFiniteColimits :
    PreservesFiniteColimits (partitionModuleEvaluation J O W) := by
  infer_instance

/-- Termwise evaluation preserves cohomology and all quasi-isomorphisms.
Source: Stacks Tag 015F; HRS Lemma 4.1(1)
(blueprint: lem-zl-partition-module-evaluation-localization).

Proof: Exactness preserves cycles, boundaries, and their quotient, naturally in
chain maps. Thus the canonical cohomology comparison is invertible, and a map
invertible on all cohomology remains so after termwise evaluation. -/
theorem partitionModuleEvaluation_homology :
    (partitionModuleEvaluation J O W).PreservesHomology ∧
    ∀ (K L : CochainComplex (ringedSiteModules (partitionModuleRings J O)) ℤ)
      (s : K ⟶ L), QuasiIso s →
        QuasiIso (((partitionModuleEvaluation J O W).mapHomologicalComplex
          (ComplexShape.up ℤ)).map s) := by
  constructor
  · infer_instance
  · intro K L s hs
    have := hs
    infer_instance

variable [HasDerivedCategory.{d₁} (ringedSiteModules (partitionModuleRings J O))]
  [HasDerivedCategory.{d₂} (ModuleCat.{max u v w} ((partitionModuleRings J O).obj.obj (op W)))]

/-- The canonical identification Q(E(O[0])) = A[0], from the single-complex
comparison for an additive exact functor and the rank-one module O.
Source: HRS Lemma 4.1(1), Stacks Tag 015F
(blueprint: lem-zl-partition-module-evaluation-localization). -/
noncomputable def partitionModuleUnitEvaluationIso :
    DerivedCategory.Q.obj (((partitionModuleEvaluation J O W).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (partitionModuleUnitComplex J O)) ≅
    DerivedCategory.Q.obj ((CochainComplex.singleFunctor
      (ModuleCat.{max u v w} ((partitionModuleRings J O).obj.obj (op W))) 0).obj
        (ModuleCat.of ((partitionModuleRings J O).obj.obj (op W))
          ((partitionModuleRings J O).obj.obj (op W)))) :=
  DerivedCategory.Q.mapIso
    (((partitionModuleEvaluation J O W).mapCochainComplexSingleFunctor 0).app
      (SheafOfModules.unit (partitionModuleRings J O)))

/-- The localization of termwise evaluation is the total right derived functor,
with its specified canonical unit; every K-injective resolution computes that unit.
Source: Stacks Tags 015F and 079P, def-sfb-right-derived-functor
(blueprint: lem-zl-partition-module-evaluation-localization).

Proof: (5) Exactness preserves quasi-isomorphisms, so
lem-weil-pbc-exact-functor-derived-factorization gives mapDerivedCategory and its
canonical factorization phi. By lem-weil-pbc-exact-functor-derived-functor,
(phi inverse) is the right-derived unit.
(6) K-injective resolutions exist by prop-pur-kinjective-resolutions-exist.
The universal property of def-sfb-right-derived-functor identifies any chosen
right-derived pair with this pair by a unique unit-compatible isomorphism e.
For s : K → I, naturality of phi gives exactly the displayed equation; E(s)
is a quasi-isomorphism by the previous assertion. In particular it identifies the
termwise model with the K-injective model, with no preservation of injectives needed.
(7) On the degree-zero unit module, E(O[0]) = A[0]. Unit compatibility says that
the comparison followed by e inverse and phi is the identity on this object.
Empty diagrams, W initial, and the zero ring give zero modules and the same identities. -/
theorem partitionModuleEvaluation_derived :
    ((partitionModuleEvaluation J O W).mapDerivedCategory).IsRightDerivedFunctor
      (partitionModuleEvaluation J O W).mapDerivedCategoryFactors.inv
      (HomologicalComplex.quasiIso (ringedSiteModules (partitionModuleRings J O))
        (ComplexShape.up ℤ)) ∧
    ∀ (RE : DerivedCategory (ringedSiteModules (partitionModuleRings J O)) ⥤
        DerivedCategory (ModuleCat.{max u v w} ((partitionModuleRings J O).obj.obj (op W))))
      (η : (partitionModuleEvaluation J O W).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RE),
      RE.IsRightDerivedFunctor η
        (HomologicalComplex.quasiIso (ringedSiteModules (partitionModuleRings J O))
          (ComplexShape.up ℤ)) →
      ∃! e : (partitionModuleEvaluation J O W).mapDerivedCategory ≅ RE,
        (partitionModuleEvaluation J O W).mapDerivedCategoryFactors.inv ≫
          Functor.whiskerLeft DerivedCategory.Q e.hom = η := by
  -- The universal property gives the comparison without choosing any resolution.
  let E := partitionModuleEvaluation J O W
  have h : E.mapDerivedCategory.IsRightDerivedFunctor E.mapDerivedCategoryFactors.inv
      (HomologicalComplex.quasiIso (ringedSiteModules (partitionModuleRings J O))
        (ComplexShape.up ℤ)) :=
    (E.exactFunctor_derivedFunctor E.mapDerivedCategory E.mapDerivedCategoryFactors).1
  refine ⟨h, ?_⟩
  intro RE η hRE
  have := hRE
  let e := E.mapDerivedCategory.rightDerivedUnique RE E.mapDerivedCategoryFactors.inv η
    (HomologicalComplex.quasiIso (ringedSiteModules (partitionModuleRings J O))
      (ComplexShape.up ℤ))
  have he : E.mapDerivedCategoryFactors.inv ≫ Functor.whiskerLeft DerivedCategory.Q e.hom =
      η := by
    simp [e, Functor.rightDerivedUnique]
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  exact E.mapDerivedCategory.rightDerived_ext E.mapDerivedCategoryFactors.inv
    (HomologicalComplex.quasiIso (ringedSiteModules (partitionModuleRings J O))
      (ComplexShape.up ℤ)) RE e'.hom e.hom (he'.trans he.symm)

/-- The resolution comparison is the image of E(s), with the canonical unit.
Source: Stacks Tag 015F and def-sfb-right-derived-functor
(blueprint: lem-zl-partition-module-evaluation-localization).
Proof: Naturality of the factorization phi identifies D(E)(Qs) with Q(E(s)).
The unit compatibility equation replaces eta by phi inverse followed by e.
Naturality of e and cancellation of its inverse give the asserted equation.
E(s) is a quasi-isomorphism by partitionModuleEvaluation_homology. -/
theorem partitionModuleEvaluation_resolution
    (RE : DerivedCategory (ringedSiteModules (partitionModuleRings J O)) ⥤
      DerivedCategory (ModuleCat.{max u v w} ((partitionModuleRings J O).obj.obj (op W))))
    (η : (partitionModuleEvaluation J O W).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RE)
    (e : (partitionModuleEvaluation J O W).mapDerivedCategory ≅ RE)
    (he : (partitionModuleEvaluation J O W).mapDerivedCategoryFactors.inv ≫
      Functor.whiskerLeft DerivedCategory.Q e.hom = η)
    (K I : CochainComplex (ringedSiteModules (partitionModuleRings J O)) ℤ)
    (s : K ⟶ I) [I.IsKInjective] [QuasiIso s] :
    QuasiIso (((partitionModuleEvaluation J O W).mapHomologicalComplex
      (ComplexShape.up ℤ)).map s) ∧
    η.app K ≫ RE.map (DerivedCategory.Q.map s) ≫
      e.inv.app (DerivedCategory.Q.obj I) ≫
      (partitionModuleEvaluation J O W).mapDerivedCategoryFactors.hom.app I =
    DerivedCategory.Q.map (((partitionModuleEvaluation J O W).mapHomologicalComplex
      (ComplexShape.up ℤ)).map s) := by
  constructor
  · exact (partitionModuleEvaluation_homology J W O).2 K I s inferInstance
  · have hunit : η.app I ≫ e.inv.app (DerivedCategory.Q.obj I) ≫
        (partitionModuleEvaluation J O W).mapDerivedCategoryFactors.hom.app I = 𝟙 _ := by
      rw [← he]
      simp
    have hn : DerivedCategory.Q.map
        (((partitionModuleEvaluation J O W).mapHomologicalComplex
          (ComplexShape.up ℤ)).map s) ≫ η.app I =
        η.app K ≫ RE.map (DerivedCategory.Q.map s) := η.naturality s
    rw [← Category.assoc, ← hn]
    simp only [Category.assoc, hunit]
    exact Category.comp_id _

/-- Under the canonical comparison, the right-derived unit is the identity.
In particular take K = O[0]: its termwise evaluation is A[0], so this is the
specified identity on A[0].
Source: Stacks Tag 015F and def-sfb-right-derived-functor
(blueprint: lem-zl-partition-module-evaluation-localization).
Proof: Substitute he, cancel e.hom against e.inv, then cancel phi inverse
against phi. The remaining composite is the canonical A[0] comparison followed
by its inverse, hence the identity.
If W is initial or O is zero, all these evaluated objects are zero. -/
theorem partitionModuleEvaluation_unit
    (RE : DerivedCategory (ringedSiteModules (partitionModuleRings J O)) ⥤
      DerivedCategory (ModuleCat.{max u v w} ((partitionModuleRings J O).obj.obj (op W))))
    (η : (partitionModuleEvaluation J O W).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RE)
    (e : (partitionModuleEvaluation J O W).mapDerivedCategory ≅ RE)
    (he : (partitionModuleEvaluation J O W).mapDerivedCategoryFactors.inv ≫
      Functor.whiskerLeft DerivedCategory.Q e.hom = η)
    :
    (partitionModuleUnitEvaluationIso J W O).inv ≫
      η.app (partitionModuleUnitComplex J O) ≫
      e.inv.app (DerivedCategory.Q.obj (partitionModuleUnitComplex J O)) ≫
      (partitionModuleEvaluation J O W).mapDerivedCategoryFactors.hom.app
        (partitionModuleUnitComplex J O) ≫
      (partitionModuleUnitEvaluationIso J W O).hom = 𝟙 _ := by
  rw [← he]
  simp

end CategoryTheory
