/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Sheaf.Paper.PodReconstructionCommonStageData
import Sheaf.Paper.PodReconstructionScalarRealizations
import WeilConjectures.CategoryTheory.StageSystem.Functor

/-! # Coherence and descent of the actual reconstruction comparisons

Source: blueprint, lem-pod-point-dualizing-complex.proof.md, first sentence.
(blueprint: lem-pod-reconstruction-common-stage-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false

set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall
attribute [local irreducible] HasDerivedCategory.standard
attribute [local irreducible] CategoryTheory.PrincipalQuotientCompletion.quotientTower
  CategoryTheory.roosF SheafOfModules.monoidalCategory
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory

universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
  AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.PodCommonStageReconstruction
open PodCompletionScalar PodRawReconstruction
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open GeneralAlgebraicallyClosedCoefficients (Stage stageSystem stageTransition integralTransition)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (A : ∀ E : Index l Ω,
    CoefficientDerivedSystemCalculus l (Coefficient.{u} l Ω E) (point D))

attribute [local irreducible] IdentitySupport SameIndexRealization scalarUnit

private theorem unit_associator_coherence
    {I : Type*} [Preorder I] {C : I → Type*} [∀ i, Category (C i)]
    (S : StageSystem C) (H : ∀ i, C i ⥤ C i) (u : ∀ i, 𝟭 (C i) ≅ H i)
    (b : ∀ {i j} (h : i ≤ j), H i ⋙ S.T h ≅ S.T h ⋙ H j)
    (hb : ∀ {i j} (h : i ≤ j) (x : C i),
      (b h).hom.app x ≫ (u j).inv.app ((S.T h).obj x) =
        (S.T h).map ((u i).inv.app x))
    {i j k : I} (h : i ≤ j) (q : j ≤ k) (x : C i) :
    (S.T q).map ((b h).hom.app x) ≫ (b q).hom.app ((S.T h).obj x) ≫
        (H k).map ((S.assoc h q).hom.app x) =
      (S.assoc h q).hom.app ((H i).obj x) ≫ (b (h.trans q)).hom.app x := by
  apply (cancel_mono ((u k).inv.app ((S.T (h.trans q)).obj x))).mp
  have hn := (u k).inv.naturality ((S.assoc h q).hom.app x)
  change (H k).map _ ≫ (u k).inv.app _ = (u k).inv.app _ ≫ _ at hn
  calc
    _ = (S.T q).map ((b h).hom.app x) ≫
        ((b q).hom.app ((S.T h).obj x) ≫
          (u k).inv.app ((S.T q).obj ((S.T h).obj x))) ≫
        (S.assoc h q).hom.app x := by
      rw [Category.assoc, Category.assoc, hn]
      simp only [Functor.id_map, Functor.comp_obj, Category.assoc]
    _ = (S.T q).map ((S.T h).map ((u i).inv.app x)) ≫
        (S.assoc h q).hom.app x := by
      rw [hb, ← Functor.map_comp_assoc, hb]
    _ = (S.assoc h q).hom.app ((H i).obj x) ≫
        (S.T (h.trans q)).map ((u i).inv.app x) :=
      (S.assoc h q).hom.naturality ((u i).inv.app x)
    _ = _ := by rw [Category.assoc, hb]

section Generic
variable {I : Type*} [Preorder I] [IsDirectedOrder I]
  {C : I → Type*} [∀ i, Category (C i)]
  (S : StageSystem C) (H : ∀ i, C i ⥤ C i) (unit : ∀ i, 𝟭 (C i) ≅ H i)
  (e : ∀ i, S.T (i := i) le_rfl ≅ 𝟭 (C i))

private theorem genericCoherence_of_inverse_units
    (β : ∀ (E L : I) (h : E ≤ L), H E ⋙ S.T h ≅ S.T h ⋙ H L)
    (hb : ∀ (E L : I) (h : E ≤ L) (x : C E),
      (β E L h).hom.app x ≫ (unit L).inv.app ((S.T h).obj x) =
        (S.T h).map ((unit E).inv.app x)) :
    stageCoherence S H unit e β := by
  have hc {E L M : I} (h : E ≤ L) (k : L ≤ M)
      (C : C E) :=
    unit_associator_coherence S (fun E ↦ (H E))
      (fun E ↦ (unit E)) (fun {E L} h ↦ β E L h)
      (fun h C ↦ hb _ _ h C) h k C
  let F : S.Morphism S :=
    { Φ := fun E ↦ (H E)
      β := fun {E L} h ↦ β E L h
      coh := hc }
  let G := StageSystem.Morphism.id S
  let τ : StageSystem.Morphism.Hom F G :=
    { τ := fun E ↦ (unit E).inv
      comm := fun h C ↦ by
        change (S.T h).map ((unit _).inv.app C) ≫ 𝟙 _ = _
        rw [Category.comp_id]
        exact (hb _ _ h C).symm }
  let σ : StageSystem.Morphism.Hom G F :=
    { τ := fun E ↦ (unit E).hom
      comm := fun {E L} h C ↦ by
        dsimp only [G, StageSystem.Morphism.id, Iso.refl_hom, NatTrans.id_app]
        rw [Category.id_comp]
        change (S.T h).map ((unit E).hom.app C) ≫
            (β E L h).hom.app C = (unit L).hom.app ((S.T h).obj C)
        apply (cancel_mono ((unit L).inv.app ((S.T h).obj C))).mp
        rw [Category.assoc, hb, ← Functor.map_comp]
        simp }
  let v : F.functor ≅ 𝟭 S.PairCategory :=
    StageSystem.Morphism.descNatIso τ σ
      (by ext E C; exact (unit E).inv_hom_id_app C)
      (by ext E C; exact (unit E).hom_inv_id_app C) ≪≫
      StageSystem.Morphism.functorIdIso
  refine ⟨?_, ?_, ?_, ?_, ?_, F.functor, v, ?_, ?_, ?_, ?_⟩
  · intro E C
    apply (cancel_mono ((unit E).inv.app C)).mp
    have hn := (unit E).inv.naturality ((e E).hom.app C)
    have hn' : (H E).map ((e E).hom.app C) ≫
        (unit E).inv.app C =
      (unit E).inv.app ((S.T le_rfl).obj C) ≫
        (e E).hom.app C := by
      simpa only [Functor.id_obj, Functor.id_map] using hn
    calc
      _ = (S.T le_rfl).map
          ((unit E).inv.app C) ≫ (e E).hom.app C := by
        rw [Category.assoc, hn', ← Category.assoc, hb]
      _ = _ := (e E).hom.naturality ((unit E).inv.app C)
  · exact fun E L M h k C ↦ hc h k C
  · intro X Y M N hX hY h f
    exact F.tr_mapAt h f
  · intro X Y M hX hY f
    exact (unit M).inv.naturality f
  · intro X Y M hX hY f
    have hn := τ.mapAt_naturality f
    have hid : G.mapAt f = f := by
      change 𝟙 _ ≫ f ≫ 𝟙 _ = f
      rw [Category.id_comp, Category.comp_id]
    rw [hid] at hn
    exact hn
  · exact fun X ↦ rfl
  · exact fun X Y M hX hY f ↦ HEq.rfl
  · intro X
    constructor
    · change HEq ((S.ι X.stage).map ((unit X.stage).inv.app X.obj) ≫ 𝟙 _) _
      rw [Category.comp_id]
    · change HEq (𝟙 _ ≫ (S.ι X.stage).map ((unit X.stage).hom.app X.obj)) _
      rw [Category.id_comp]
  · exact fun X Y f ↦ v.hom.naturality f

end Generic

private theorem coherence_of_inverse_units
    (R : ∀ E, Realization D l Ω E (A E))
    (β : ∀ (E L : Index l Ω) (h : E ≤ L),
      (R E).rational ⋙ stageTransition l Ω (point D) E L h ≅
        stageTransition l Ω (point D) E L h ⋙ (R L).rational)
    (hb : ∀ (E L : Index l Ω) (h : E ≤ L) (C : Stage l Ω (point D) E),
      (β E L h).hom.app C ≫ (R L).rationalUnit.inv.app
          ((stageTransition l Ω (point D) E L h).obj C) =
        (stageTransition l Ω (point D) E L h).map ((R E).rationalUnit.inv.app C)) :
    Coherence D l Ω A R β := by
  exact @genericCoherence_of_inverse_units (Index l Ω) inferInstance inferInstance
    (Stage l Ω (point D))
    (fun E ↦ GeneralAlgebraicallyClosedCoefficients.stageCategory l Ω (point D) E)
    (stageSystem l Ω (point D))
    (fun E ↦ (R E).rational) (fun E ↦ (R E).rationalUnit) (scalarUnit D l Ω) β hb

/-- Coherence of the specified quotient-cone comparisons, strict identity compact
support, and reconstruction on all literal common-field representatives.
Source: current blueprint, lem-pod-point-dualizing-complex.proof.md, first sentence;
Bhatt--Scholze, Definitions 3.5.2--3.5.3, Lemmas 3.5.7 and 6.8.2(1).
(blueprint: lem-pod-reconstruction-common-stage-coherence).

Proof (the seven DAG steps, composition translated to Lean's left-to-right order):
1. Use lem-pod-reconstruction-raw-rational-naturality to restrict the actual
reconstruction, rationalize it, and identify strict identity compact support.
Use lem-pod-completion-unit-scalar-intertwining for the specified quotient-cone
comparison. Its inverse-unit equation determines beta uniquely: beta equals
S(v_E) followed by u_L. This is an equality for the specified maps, not their definition.
2. Naturality of the actual v_E at the canonical scalar unit, and naturality of
that unit at v_E, give the identity-extension equation after cancelling v_E.
3. Postcompose both associator expressions with v_M. Naturality of v_M, its
inverse-unit intertwining, and naturality of the canonical scalar associator
reduce both expressions to the same iterated scalar extension of v_E. Cancel v_M.
4. At an arbitrary common-field rational arrow f, naturality of v_F and the
intertwining identify the displayed representative with S(v_X) followed by f
followed by the inverse of S(v_Y). No integral lift of f is required.
5. Extend this formula further. Naturality of the specified associators at v_X
and v_Y shows that it commutes with representative transport. Equality in the
Hom colimit is equality at a later common field, so representatives and fields
can be changed freely; use def-weil-algebraically-closed-coefficients.
6. At a common field the conjugation formula sends identities to identities
and composites to composites, by cancellation of the middle v and its inverse.
It therefore gives the stated functor. Step 1 and the localized integral beta
identify it with the actual compact-support construction of
def-weil-integral-rational-qbar-compact-support under the strict-tower comparisons.
7. Include v_E and u_E at each pair. Their composites are identities already at
E. Step 4 gives naturality at every representative, and Step 5 preserves it
under every further extension. Thus they give the asserted natural isomorphism
and inverse, with no preferred field or finite-projection conservativity. -/
theorem reconstructionCommonStageCoherence (hl : l ≠ D.p) :
    ∃ (R : ∀ E, Realization D l Ω E (A E))
      (b : ∀ (E L : Index l Ω) (h : E ≤ L),
        (R E).integral ⋙ integralTransition l Ω (point D) E L h ≅
          integralTransition l Ω (point D) E L h ⋙ (R L).integral)
      (β : ∀ (E L : Index l Ω) (h : E ≤ L),
        (R E).rational ⋙ stageTransition l Ω (point D) E L h ≅
          stageTransition l Ω (point D) E L h ⋙ (R L).rational),
      (∀ E, IdentitySupport D l Ω E (A E) (R E)) ∧
      (∀ (E L : Index l Ω) (h : E ≤ L), SameIndexRealization D l Ω A R E L h (b E L h)) ∧
      (∀ (E L : Index l Ω) (h : E ≤ L)
        (C : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) (point D)),
        (b E L h).hom.app C ≫ (R L).integralUnit.inv.app
            ((integralTransition l Ω (point D) E L h).obj C) =
          (integralTransition l Ω (point D) E L h).map ((R E).integralUnit.inv.app C)) ∧
      (∀ (E L : Index l Ω) (h : E ≤ L) (C : Stage l Ω (point D) E),
        HEq ((β E L h).hom.app C)
          ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω L) (point D)).map
            ((b E L h).hom.app C.obj))) ∧
      (∀ (E L : Index l Ω) (h : E ≤ L) (C : Stage l Ω (point D) E),
        (β E L h).hom.app C ≫ (R L).rationalUnit.inv.app
            ((stageTransition l Ω (point D) E L h).obj C) =
          (stageTransition l Ω (point D) E L h).map ((R E).rationalUnit.inv.app C)) ∧
      Coherence D l Ω A R β := by
  have hr (E : Index l Ω) : Nonempty (Realization D l Ω E (A E)) := by
    let h0 := (reconstructionRawRationalNaturality D l (Coefficient.{u} l Ω E) hl
      (Coefficient.{u} l Ω E) (AlgHom.id _ _) (A E) (A E)).2.2
    let H := h0.choose
    let h1 := h0.choose_spec
    let h2 := h1.choose_spec
    let unit := h2.choose
    let h3 := h2.choose_spec
    let facts := h3.choose_spec
    let r0 := facts.2.2.2.2
    let J := r0.choose
    let r1 := r0.choose_spec
    let r2 := r1.choose_spec
    let unitRat := r2.choose
    let r3 := r2.choose_spec
    let factsRat := r3.choose_spec
    exact ⟨⟨H, unit, facts.1, J, unitRat, factsRat.1⟩⟩
  let R : ∀ E, Realization D l Ω E (A E) := fun E ↦ (hr E).some
  obtain ⟨b, β, hs, hi, hq, hb⟩ := reconstructionScalarRealizations D l Ω A hl R
  refine ⟨R, b, β, ?_, hs, hi, hq, hb, coherence_of_inverse_units D l Ω A R β hb⟩
  intro E
  unfold IdentitySupport
  exact reconstruction_identityCompactSupport D l (Coefficient.{u} l Ω E) hl (A E)
    (R E).integral (R E).integralUnit (R E).integral_actual
    (R E).rational (R E).rationalUnit (R E).rational_actual

end WeilConjectures.PodCommonStageReconstruction
