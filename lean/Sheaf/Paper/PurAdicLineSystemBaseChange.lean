/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.Paper.PurAdicLineSystemData
import Sheaf.Paper.PurAdicIntegralComparison
import Sheaf.Paper.PurAdicLocalizationComparison
import Sheaf.Paper.PurAdicFilteredColimitExists
import Sheaf.Paper.PurAdicFilteredColimitComparison
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-! # Base change of adic line systems

Source: the integral twist and rational coefficient paragraphs of
`sk-prop-sfb-cartesian-coefficients-twists.proof.md`.
(blueprint: lem-pur-adic-line-system-base-change).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

universe w uC vC uD vD uI vI

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

private theorem purAdicStride_initial (e : ℕ) (he : 1 ≤ e) :
    (purAdicStride e).Initial := by
  let f : ℕ →o ℕ :=
    ⟨fun n ↦ e * (n + 1) - 1,
      fun _ _ h ↦ Nat.sub_le_sub_right (Nat.mul_le_mul_left e (Nat.add_le_add_right h 1)) 1⟩
  have hf : f.monotone.functor.Final := by
    apply f.monotone.final_functor_iff.mpr
    intro n
    refine ⟨n, ?_⟩
    change n ≤ e * (n + 1) - 1
    have h := Nat.mul_le_mul_right (n + 1) he
    omega
  exact inferInstanceAs f.monotone.functor.op.Initial

private theorem purAdicCofinalRestriction_proof
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} {I : Type w} [PartialOrder I] {e : I → ℕ}
    (A : PurAdicLineLimits.{w} J I e) (he : ∀ i, 1 ≤ e i) :
    PurAdicCofinalRestriction A := by
  intro i
  let F := purAdicStride (e i)
  have : F.Initial := purAdicStride_initial (e i) (he i)
  let S := (Cone.mk (A.integral.R.obj i) (A.rπ i)).whisker F
  have hS : IsLimit S := (Functor.Initial.isLimitWhiskerEquiv F _).symm (A.rlimit i)
  refine ⟨⟨⟨S, hS⟩⟩, ?_⟩
  intro T hT
  let q := hS.conePointUniqueUpToIso hT
  refine ⟨q, ?_, ?_⟩
  · intro n
    exact hT.fac S (op n)
  · intro m n h
    have hh := ((A.rπ i).naturality (homOfLE h).op).symm
    simp only [Functor.const_obj_map] at hh
    change (A.rπ i).app (op (e i * (n + 1) - 1)) ≫
        (A.full i).map (homOfLE h).op = (A.rπ i).app (op m) at hh
    rw [← hh, ← Category.assoc]
    change (q.inv ≫ S.π.app (op n)) ≫ _ = _
    exact congrArg (fun f ↦ f ≫ (A.full i).map (homOfLE h).op)
      (hS.conePointUniqueUpToIso_inv_comp hT (op n))

private theorem purAdicIntegral_hom_ext
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} {I : Type w} [PartialOrder I] {e : I → ℕ}
    (A : PurAdicLineLimits.{w} J I e) (i : I) {T : Sheaf J (Type w)}
    (f g : T ⟶ A.integral.modules.obj i)
    (h : ∀ n : ℕ, f ≫ (sheafCompose J (forget AddCommGrpCat.{w})).map
        ((A.pπ i).app (op n)) =
      g ≫ (sheafCompose J (forget AddCommGrpCat.{w})).map ((A.pπ i).app (op n))) :
    f = g := by
  let P := sheafCompose J (forget AddCommGrpCat.{w})
  have : PreservesLimitsOfShape ℕᵒᵖ (P ⋙ sheafToPresheaf J (Type w)) :=
    inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ
      (sheafToPresheaf J AddCommGrpCat.{w} ⋙
        (Functor.whiskeringRight Cᵒᵖ AddCommGrpCat.{w} (Type w)).obj
          (forget AddCommGrpCat.{w})))
  have : PreservesLimitsOfShape ℕᵒᵖ P :=
    preservesLimitsOfShape_of_reflects_of_preserves P (sheafToPresheaf J (Type w))
  apply (isLimitOfPreserves P (A.plimit i)).hom_ext
  intro n
  exact h n.unop

private theorem purAdicRingSets_colimits
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) [HasSheafify J CommRingCat.{w}]
    (I : Type w) [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)] :
    PreservesColimitsOfShape I (sheafCompose J (forget CommRingCat.{w})) := by
  let U := forget CommRingCat.{w}
  have : ∀ X : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow X (equivSmallModel.{w} C).inverse.op)
        CommRingCat.{w} := fun _ ↦ hasLimitsOfShape_of_essentiallySmall.{w} _ _
  have : ∀ X : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow X (equivSmallModel.{w} C).inverse.op)
        (Type w) := fun _ ↦ hasLimitsOfShape_of_essentiallySmall.{w} _ _
  have : HasSheafify J (Type w) := hasSheafifyEssentiallySmallSite J _
  have : ((equivSmallModel.{w} C).inverse.inducedTopology J).PreservesSheafification U :=
    GrothendieckTopology.instPreservesSheafification _ U
  have : J.PreservesSheafification U := inferInstance
  rw [(sheafificationAdjunction J CommRingCat.{w}).preservesColimitsOfShape_iff]
  exact preservesColimitsOfShape_of_natIso
    (sheafComposeNatIso J U (sheafificationAdjunction J CommRingCat.{w})
      (sheafificationAdjunction J (Type w)))

private theorem purAdicModuleSets_colimits
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{w}]
    (I : Type w) [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)] :
    PreservesColimitsOfShape I (sheafCompose J (forget AddCommGrpCat.{w})) := by
  let U := forget AddCommGrpCat.{w}
  have : ∀ X : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow X (equivSmallModel.{w} C).inverse.op)
        AddCommGrpCat.{w} := fun _ ↦ hasLimitsOfShape_of_essentiallySmall.{w} _ _
  have : ∀ X : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow X (equivSmallModel.{w} C).inverse.op)
        (Type w) := fun _ ↦ hasLimitsOfShape_of_essentiallySmall.{w} _ _
  have : HasSheafify J (Type w) := hasSheafifyEssentiallySmallSite J _
  have : ((equivSmallModel.{w} C).inverse.inducedTopology J).PreservesSheafification U :=
    GrothendieckTopology.instPreservesSheafification _ U
  have : J.PreservesSheafification U := inferInstance
  rw [(sheafificationAdjunction J AddCommGrpCat.{w}).preservesColimitsOfShape_iff]
  exact preservesColimitsOfShape_of_natIso
    (sheafComposeNatIso J U (sheafificationAdjunction J AddCommGrpCat.{w})
      (sheafificationAdjunction J (Type w)))

private theorem purAdicColimitComparison_unique
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [HasSheafify J AddCommGrpCat.{w}] [HasSheafify J CommRingCat.{w}]
    (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    (V : Sheaf K (Type w) ⥤ Sheaf J (Type w)) (adj : L ⊣ V)
    {I : Type w} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {A : PurAdicPairDiagram.{w} J I} {B : PurAdicPairDiagram.{w} K I}
    (t : PurAdicPairComparison L A B)
    (F : PurAdicFilteredColimit A) (G : PurAdicFilteredColimit B)
    (z z' : PurAdicColimitComparison L t F G) :
    z'.a.ringUnderlying = z.a.ringUnderlying ∧
      purAdicPresentedModuleIso F.M G.M F.identify G.identify z'.a z'.c =
        purAdicPresentedModuleIso F.M G.M F.identify G.identify z.a z.c := by
  have : PreservesColimitsOfSize.{w, w} L := adj.leftAdjoint_preservesColimits
  have : PreservesColimitsOfShape I (sheafCompose J (forget CommRingCat.{w})) :=
    purAdicRingSets_colimits J I
  have : PreservesColimitsOfShape I (sheafCompose J (forget AddCommGrpCat.{w})) :=
    purAdicModuleSets_colimits J I
  constructor
  · apply Iso.ext
    apply (isColimitOfPreserves (sheafCompose J (forget CommRingCat.{w}) ⋙ L)
      F.rcolimit).hom_ext
    intro i
    exact (z'.ring_ι i).trans (z.ring_ι i).symm
  · apply Iso.ext
    apply (isColimitOfPreserves (sheafCompose J (forget AddCommGrpCat.{w}) ⋙ L)
      F.pcolimit).hom_ext
    intro i
    exact (z'.module_ι i).trans (z.module_ι i).symm

/-- Inverse image of adic line systems, with localization and filtered coefficient change.
Source: Integral twist and Rational and algebraic closure paragraphs of
`sk-prop-sfb-cartesian-coefficients-twists.proof.md`; Stacks Sites, Tag 03CF
(blueprint: lem-pur-adic-line-system-base-change).

Proof:
1. Restriction to the positive stride is cofinal. Recover coordinate m by reducing
   any coordinate e(n+1) at least m+1; comparison at a larger coordinate proves independence.
2. The full coefficient projection equations identify the subsequence limit comparison
   with the given coefficient isomorphism, hence it is invertible.
3. Apply `lem-pur-inverse-image-compatible-free-tower` on the single common cover,
   then compose with the levelwise comparisons c. This gives the displayed projections.
4. Test scalar compatibility, uniqueness and naturality on every projection. These
   formulas mention no bases, proving independence of the cover and bases.
5. By `lem-sc-module-localization-filtered-colimit` the sheafified sequential colimit
   is the localization, with the actual fraction-ring action obtained by module sheafification.
6. `lem-weil-pbc-localization-tensor` and the module-sheafification tensor comparison
   identify it with tensor localization, preserving m/1 and m tensor 1.
7. Apply `lem-weil-pbc-localization-inverse-image-coherence`. The semilinear integral
   comparison induces a comparison of the sequential diagrams. Cocone normalization
   proves uniqueness and naturality after localization.
8. Form ring and abelian presheaf colimits and define [r_i][m_j] at a common upper bound.
   The representative criteria for filtered ring and module colimits make this independent
   of representatives and prove all ring/module laws at a common stage.
9. Sheafify. Sectionwise presheaf colimits and the sheafification adjunction give the two
   colimit universal properties. Preservation of finite products gives the displayed action.
10. Colimit preservation of inverse image gives the final comparisons. Test semilinearity
    on stage products and normalize on every coprojection to obtain uniqueness.
-/
theorem purAdicLineSystem_baseChange
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    [HasFiniteLimits C] [HasFiniteLimits D]
    (J : Precoverage C) (K : Precoverage D)
    (_hJ : J.IsSiteForCoverings) (_hK : K.IsSiteForCoverings)
    (U : C ⥤ D) [PreservesFiniteLimits U]
    (_hUcover : ∀ (X : C) (S : Presieve X), S ∈ J X → S.map U ∈ K (U.obj X))
    [U.IsContinuous J.toGrothendieck K.toGrothendieck]
    (L : Sheaf J.toGrothendieck (Type w) ⥤ Sheaf K.toGrothendieck (Type w))
    (_adj : L ⊣ U.sheafPushforwardContinuous (Type w) J.toGrothendieck K.toGrothendieck)
    [PreservesFiniteLimits L]
    [HasSheafify J.toGrothendieck AddCommGrpCat.{w}]
    [J.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify J.toGrothendieck CommRingCat.{w}]
    [HasSheafify K.toGrothendieck AddCommGrpCat.{w}]
    [K.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify K.toGrothendieck CommRingCat.{w}]
    (I : Type w) [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (e : I → ℕ) (_he : ∀ i : I, 1 ≤ e i)
    (A : PurAdicLineLimits.{w} J.toGrothendieck I e)
    (B : PurAdicLineLimits.{w} K.toGrothendieck I e)
    (c : PurAdicPairComparison L A.levels B.levels)
    (a : PurAdicCoefficientComparison L A B c)
    (_bases : PurAdicLineLocallyBased J A)
    (s : ∀ i : I, ((A.integral.R.obj i).obj ⋙ forget CommRingCat.{w}).sections)
    (s' : ∀ i : I, ((B.integral.R.obj i).obj ⋙ forget CommRingCat.{w}).sections)
    (_hs : ∀ {i j : I} (h : i ≤ j) (V : Cᵒᵖ),
      (A.integral.R.map (homOfLE h)).hom.app V ((s i).val V) = (s j).val V)
    (_hsection : ∀ i : I, IsInverseImageSection.{w, uC, vC, uD, vD} (a.integral i) (s i) (s' i)) :
    PurAdicCofinalRestriction A ∧ PurAdicCofinalRestriction B ∧
    ∃ t : PurAdicPairComparison L A.integral B.integral,
      (∀ i : I, (t.a i).ringUnderlying = (a.integral i).ringUnderlying) ∧
      PurAdicIntegralNormalized L A B c t ∧
      (∀ (i : I) (f : L.obj (A.integral.modules.obj i) ⟶ B.integral.modules.obj i),
        (∀ n : ℕ, f ≫ (sheafCompose K.toGrothendieck (forget AddCommGrpCat.{w})).map
            ((B.pπ i).app (op n)) =
          L.map ((sheafCompose J.toGrothendieck (forget AddCommGrpCat.{w})).map
              ((A.pπ i).app (op n))) ≫
            (purAdicModuleIso L A.levels B.levels (i, op n) (c.a _) (c.c _)).hom) →
        f = (purAdicModuleIso L A.integral B.integral i (t.a i) (t.c i)).hom) ∧
      ∃ (Q : PurAdicLocalization A.integral s) (Q' : PurAdicLocalization B.integral s')
        (d : PurAdicPairComparison L Q.pairs Q'.pairs),
        PurAdicLocalizationNormalized L t Q Q' d ∧
        (∀ d' : PurAdicPairComparison L Q.pairs Q'.pairs,
          PurAdicLocalizationNormalized L t Q Q' d' →
          ∀ i : I, (d'.a i).ringUnderlying = (d.a i).ringUnderlying ∧
            purAdicModuleIso L Q.pairs Q'.pairs i (d'.a i) (d'.c i) =
              purAdicModuleIso L Q.pairs Q'.pairs i (d.a i) (d.c i)) ∧
        ∃ (F : PurAdicFilteredColimit Q.pairs) (G : PurAdicFilteredColimit Q'.pairs)
          (z : PurAdicColimitComparison L d F G),
          ∀ z' : PurAdicColimitComparison L d F G,
            z'.a.ringUnderlying = z.a.ringUnderlying ∧
            purAdicPresentedModuleIso F.M G.M F.identify G.identify z'.a z'.c =
              purAdicPresentedModuleIso F.M G.M F.identify G.identify z.a z.c := by
  have hA := purAdicCofinalRestriction_proof A _he
  have hB := purAdicCofinalRestriction_proof B _he
  choose ci hci using purAdicIntegralComparison_exists J K _hJ _hK U _hUcover L _adj
    A B c a _bases hA hB
  let t : PurAdicPairComparison L A.integral B.integral :=
    { a := a.integral
      c := ci
      ring_natural := fun h ↦ a.integral_natural (leOfHom h)
      module_natural := by
        intro i j h
        apply purAdicIntegral_hom_ext B j
        intro n
        let P := sheafCompose J.toGrothendieck (forget AddCommGrpCat.{w})
        let P' := sheafCompose K.toGrothendieck (forget AddCommGrpCat.{w})
        let f := Prod.mkHom h (𝟙 (op n))
        have hA := congrArg P.map (A.pπ_natural (leOfHom h) n)
        have hB := congrArg P'.map (B.pπ_natural (leOfHom h) n)
        simp only [Functor.map_comp] at hA hB
        change A.integral.modules.map h ≫ P.map ((A.pπ j).app (op n)) =
          P.map ((A.pπ i).app (op n)) ≫ A.levels.modules.map f at hA
        change B.integral.modules.map h ≫ P'.map ((B.pπ j).app (op n)) =
          P'.map ((B.pπ i).app (op n)) ≫ B.levels.modules.map f at hB
        rw [Category.assoc, hci j n, ← L.map_comp_assoc, hA, L.map_comp,
          Category.assoc, c.module_natural f, ← Category.assoc,
          ← hci i n, Category.assoc, ← hB, ← Category.assoc] }
  refine ⟨purAdicCofinalRestriction_proof A _he, purAdicCofinalRestriction_proof B _he,
    t, fun _ ↦ rfl, hci, ?_, ?_⟩
  · intro i f hf
    apply purAdicIntegral_hom_ext B i
    intro n
    exact (hf n).trans (hci i n).symm
  · obtain ⟨Q, Q', d, hd, hdu⟩ := purAdicLocalizationComparison_exists L _ _adj
      A.integral B.integral t s s' _hs _hsection
    refine ⟨Q, Q', d, hd, hdu, ?_⟩
    obtain ⟨F⟩ := purAdicFilteredColimit_exists Q.pairs
    obtain ⟨G⟩ := purAdicFilteredColimit_exists Q'.pairs
    obtain ⟨z⟩ := purAdicFilteredColimitComparison_exists L _ _adj Q.pairs Q'.pairs d F G
    exact ⟨F, G, z, fun z' ↦ purAdicColimitComparison_unique L _ _adj d F G z z'⟩

end CategoryTheory
