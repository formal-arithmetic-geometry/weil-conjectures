/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups NQ, NG and NS
-/
module

public import Sheaf.Paper.PbcRationalCategory
public import Sheaf.Paper.PbcFiniteCompletedCoefficientMap
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.CategoryTheory.StageSystem.Basic

/-!
# Scalar extension of completed integral coefficients and its raw rationalization

Source: blueprint, proper base change, order 1307
(blueprint: def-weil-pbc-finite-stage-pair-category).

The coefficient map is fixed by every finite quotient. Its derived tensor functor
is the recorded K-flat construction. Rationalization is uniquely fixed by its
composite with the integral localization, including its object function.

For objects `(E,K)` and `(F,L)`, an upstream `PairCategory.Rep` contains a finite
coefficient field `M`, inclusions `E ≤ M` and `F ≤ M`, and a morphism between
the two specified scalar extensions in `pbcStageCategory M`. Its transport is
`pbcScalarAssociator.inv ≫ pbcScalarExtension.map u ≫ pbcScalarAssociator.hom`.
The upstream quotient identifies exactly those representatives whose transports
agree at a further finite coefficient field; none of these data is a parameter
of `PbcFiniteStagePairCategory`.

## Main definitions

* `pbcStageCategory`: the recorded raw rational finite coefficient stage.
* `pbcScalarSystem`: its concrete normalized tensor extension system.
* `PbcFiniteStagePairCategory`: the common-stage quotient with its Hom group laws.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u c
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.StageSystem

universe w v z
variable {I : Type w} [Preorder I] [IsDirectedOrder I]
  {C : I → Type z} [∀ i, Category.{v} (C i)] [∀ i, Preadditive (C i)]
  (S : StageSystem C)

/-- Addition on classes is fixed by addition of representatives at any common stage.
Source: blueprint finite-stage pair category
(blueprint: def-weil-pbc-finite-stage-pair-category). -/
def PairPreadditiveNormalized (P : Preadditive S.PairCategory) : Prop := by
  letI := P
  exact ∀ (X Y : S.PairCategory) (n : I) (hX : X.stage ≤ n) (hY : Y.stage ≤ n)
    (f g : X.toStage hX ⟶ Y.toStage hY),
    PairCategory.mkHom n hX hY (f + g) =
      PairCategory.mkHom n hX hY f + PairCategory.mkHom n hX hY g ∧
    PairCategory.mkHom n hX hY (0 : X.toStage hX ⟶ Y.toStage hY) = 0

section AdditiveConstruction

variable [∀ i j (h : i ≤ j), (S.T h).Additive]

omit [IsDirectedOrder I] in
private lemma pair_tr_add {i j n p : I} {hi : i ≤ n} {hj : j ≤ n}
    (h : n ≤ p) {x : C i} {y : C j}
    (f g : (S.T hi).obj x ⟶ (S.T hj).obj y) :
    S.tr h (f + g) = S.tr h f + S.tr h g := by
  simp [tr, Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]

omit [IsDirectedOrder I] in
private lemma pair_tr_zero {i j n p : I} {hi : i ≤ n} {hj : j ≤ n}
    (h : n ≤ p) {x : C i} {y : C j} :
    S.tr h (0 : (S.T hi).obj x ⟶ (S.T hj).obj y) = 0 := by
  simp [tr]

omit [IsDirectedOrder I] in
private lemma pair_tr_neg {i j n p : I} {hi : i ≤ n} {hj : j ≤ n}
    (h : n ≤ p) {x : C i} {y : C j}
    (f : (S.T hi).obj x ⟶ (S.T hj).obj y) :
    S.tr h (-f) = -S.tr h f := by
  simp [tr]

open PairCategory in
private def pairAddRep {X Y : S.PairCategory} (r s : Rep X Y) : Rep X Y :=
  ⟨commonStage r.k s.k, r.hX.trans (le_commonStage_left _ _),
    r.hY.trans (le_commonStage_left _ _),
    S.tr (le_commonStage_left _ _) r.u + S.tr (le_commonStage_right _ _) s.u⟩

open PairCategory in
private lemma pairAddRep_rel {X Y : S.PairCategory} {r r' s s' : Rep X Y}
    (hr : Rep.Rel r r') (hs : Rep.Rel s s') :
    Rep.Rel (pairAddRep S r s) (pairAddRep S r' s') := by
  obtain ⟨p, h₁, h₂, e⟩ := hr
  obtain ⟨q, h₃, h₄, e'⟩ := hs
  obtain ⟨a, ha₁, ha₂⟩ := exists_ge_ge p q
  obtain ⟨b, hb₁, hb₂⟩ := exists_ge_ge (commonStage r.k s.k) (commonStage r'.k s'.k)
  obtain ⟨m, hm₁, hm₂⟩ := exists_ge_ge a b
  refine ⟨m, hb₁.trans hm₂, hb₂.trans hm₂, ?_⟩
  change S.tr _ (S.tr _ r.u + S.tr _ s.u) = S.tr _ (S.tr _ r'.u + S.tr _ s'.u)
  rw [pair_tr_add, pair_tr_add, tr_tr, tr_tr, tr_tr, tr_tr]
  exact congrArg₂ (· + ·)
    (Rep.rel_of_eq h₁ h₂ e (ha₁.trans hm₁))
    (Rep.rel_of_eq h₃ h₄ e' (ha₂.trans hm₁))

private def pairHomAdd {X Y : S.PairCategory} (f g : X ⟶ Y) : X ⟶ Y :=
  Quotient.map₂ (pairAddRep S) (fun _ _ hr _ _ hs ↦ pairAddRep_rel S hr hs) f g

open PairCategory in
private lemma pairHomAdd_mk {X Y : S.PairCategory} {n : I}
    {hX : X.stage ≤ n} {hY : Y.stage ≤ n} (f g : X.toStage hX ⟶ Y.toStage hY) :
    pairHomAdd S (mkHom n hX hY f) (mkHom n hX hY g) = mkHom n hX hY (f + g) := by
  change mkHom _ _ _ _ = _
  rw [mkHom_eq_mkHom_iff']
  refine ⟨commonStage n n, le_rfl, le_commonStage_left _ _, ?_⟩
  simp only [pair_tr_add, tr_tr]

private def pairHomNeg {X Y : S.PairCategory} (f : X ⟶ Y) : X ⟶ Y :=
  Quotient.map (fun r ↦ ⟨r.k, r.hX, r.hY, -r.u⟩)
    (by
      rintro r s ⟨p, hr, hs, e⟩
      exact ⟨p, hr, hs, by simpa only [pair_tr_neg] using congrArg Neg.neg e⟩) f

open PairCategory in
private lemma pairHomNeg_mk {X Y : S.PairCategory} {n : I}
    {hX : X.stage ≤ n} {hY : Y.stage ≤ n} (f : X.toStage hX ⟶ Y.toStage hY) :
    pairHomNeg S (mkHom n hX hY f) = mkHom n hX hY (-f) := rfl

open PairCategory in
private def pairHomZero (X Y : S.PairCategory) : X ⟶ Y :=
  mkHom (commonStage X.stage Y.stage) (le_commonStage_left _ _)
    (le_commonStage_right _ _) 0

open PairCategory in
private lemma pairHomZero_mk {X Y : S.PairCategory} (n : I)
    (hX : X.stage ≤ n) (hY : Y.stage ≤ n) :
    pairHomZero S X Y = mkHom n hX hY 0 := by
  rw [pairHomZero, mkHom_eq_mkHom_iff']
  obtain ⟨p, hp, hn⟩ := exists_ge_ge (commonStage X.stage Y.stage) n
  exact ⟨p, hp, hn, by simp only [pair_tr_zero]⟩

open PairCategory in
private abbrev pairHomGroup (X Y : S.PairCategory) : AddCommGroup (X ⟶ Y) := by
  letI : Add (X ⟶ Y) := ⟨pairHomAdd S⟩
  letI : Zero (X ⟶ Y) := ⟨pairHomZero S X Y⟩
  letI : Neg (X ⟶ Y) := ⟨pairHomNeg S⟩
  exact {
    add := pairHomAdd S
    zero := pairHomZero S X Y
    neg := pairHomNeg S
    nsmul := nsmulRec
    zsmul := zsmulRec
    add_assoc f g h := by
      change pairHomAdd S (pairHomAdd S f g) h = pairHomAdd S f (pairHomAdd S g h)
      induction f using hom_induction with
      | h n hX hY f =>
        induction g using hom_induction with
        | h n' hX' hY' g =>
          induction h using hom_induction with
          | h n'' hX'' hY'' h =>
            obtain ⟨a, ha, ha'⟩ := exists_ge_ge n n'
            obtain ⟨p, hp, hp'⟩ := exists_ge_ge a n''
            rw [← mkHom_tr (ha.trans hp) f, ← mkHom_tr (ha'.trans hp) g,
              ← mkHom_tr hp' h]
            simp only [pairHomAdd_mk, add_assoc]
    zero_add f := by
      change pairHomAdd S (pairHomZero S X Y) f = f
      induction f using hom_induction with
      | h n hX hY f => rw [pairHomZero_mk S n hX hY, pairHomAdd_mk, zero_add]
    add_zero f := by
      change pairHomAdd S f (pairHomZero S X Y) = f
      induction f using hom_induction with
      | h n hX hY f => rw [pairHomZero_mk S n hX hY, pairHomAdd_mk, add_zero]
    neg_add_cancel f := by
      change pairHomAdd S (pairHomNeg S f) f = pairHomZero S X Y
      induction f using hom_induction with
      | h n hX hY f =>
        rw [pairHomNeg_mk, pairHomAdd_mk, neg_add_cancel, pairHomZero_mk S n hX hY]
    add_comm f g := by
      change pairHomAdd S f g = pairHomAdd S g f
      obtain ⟨n, _, hX, hY, _, _, f, g, rfl, rfl⟩ :=
        exists_common_stage f g X.stage
      rw [pairHomAdd_mk, pairHomAdd_mk, add_comm] }

open PairCategory in
private abbrev pairPreadditiveStructure : Preadditive S.PairCategory where
  homGroup := pairHomGroup S
  add_comp X Y Z f g h := by
    induction f using hom_induction with
    | h n hX hY f =>
      induction g using hom_induction with
      | h n' hX' hY' g =>
        induction h using hom_induction with
        | h n'' hY'' hZ h =>
          obtain ⟨a, ha, ha'⟩ := exists_ge_ge n n'
          obtain ⟨p, hp, hp'⟩ := exists_ge_ge a n''
          rw [← mkHom_tr (ha.trans hp) f, ← mkHom_tr (ha'.trans hp) g,
            ← mkHom_tr hp' h]
          change pairHomAdd S _ _ ≫ _ = pairHomAdd S (_ ≫ _) (_ ≫ _)
          rw [pairHomAdd_mk, mkHom_comp_mkHom, mkHom_comp_mkHom,
            mkHom_comp_mkHom, pairHomAdd_mk, Preadditive.add_comp]
  comp_add X Y Z f g h := by
    induction f using hom_induction with
    | h n hX hY f =>
      induction g using hom_induction with
      | h n' hY' hZ g =>
        induction h using hom_induction with
        | h n'' hY'' hZ' h =>
          obtain ⟨a, ha, ha'⟩ := exists_ge_ge n n'
          obtain ⟨p, hp, hp'⟩ := exists_ge_ge a n''
          rw [← mkHom_tr (ha.trans hp) f, ← mkHom_tr (ha'.trans hp) g,
            ← mkHom_tr hp' h]
          change _ ≫ pairHomAdd S _ _ = pairHomAdd S (_ ≫ _) (_ ≫ _)
          rw [pairHomAdd_mk, mkHom_comp_mkHom, mkHom_comp_mkHom,
            mkHom_comp_mkHom, pairHomAdd_mk, Preadditive.comp_add]

end AdditiveConstruction

/-- The common-stage formulas determine a unique preadditive structure.
Source: blueprint finite-stage pair category
(blueprint: def-weil-pbc-finite-stage-pair-category).
Proof: transport is conjugation of an additive functor by associators, so it is
additive. For two representatives pass to their finite common upper stage and
add there. A second choice agrees after transport to a common further stage.
Negation and zero descend in the same way. All abelian-group identities and
bilinearity of composition hold after passing to one common stage. Every
morphism has a representative, so these equations also prove uniqueness. -/
theorem pairPreadditive_exists [∀ i j (h : i ≤ j), (S.T h).Additive] :
    ∃! P : Preadditive S.PairCategory, S.PairPreadditiveNormalized P := by
  refine ⟨pairPreadditiveStructure S, ?_, ?_⟩
  · intro X Y n hX hY f g
    exact ⟨(pairHomAdd_mk S f g).symm, (pairHomZero_mk S n hX hY).symm⟩
  · intro P hP
    apply Preadditive.ext
    funext X Y
    apply AddCommGroup.ext
    funext f g
    obtain ⟨n, _, hX, hY, _, _, f, g, rfl, rfl⟩ :=
      PairCategory.exists_common_stage f g X.stage
    exact ((hP X Y n hX hY f g).1).symm.trans (pairHomAdd_mk S f g).symm

/-- The preadditive structure determined by the common-stage group laws.
Source: blueprint finite-stage pair category
(blueprint: def-weil-pbc-finite-stage-pair-category). -/
instance pairPreadditive [∀ i j (h : i ≤ j), (S.T h).Additive] :
    Preadditive S.PairCategory := (S.pairPreadditive_exists).exists.choose

end CategoryTheory.StageSystem

namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (Ω : Type c) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]
variable {E F G : Padic.FiniteCoefficientFields l Ω}

variable (T : Scheme.{u})

/-- The existing bounded constructible complete integral stage, with its coefficient fixed.
Source: blueprint order 1308 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
abbrev pbcIntegralStage (E : Padic.FiniteCoefficientFields l Ω) :=
  PbcBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω E)

/-- The ambient derived coefficient stage used by the integral full inclusion.
Source: blueprint order 1308 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
abbrev pbcAmbientStage (E : Padic.FiniteCoefficientFields l Ω) :=
  PbcCompletedDerived T (pbcStageDatum.{u} l Ω E)

/-- The existing full inclusion of the integral stage into its ambient derived category.
Source: blueprint order 1308 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
abbrev pbcStageInclusion (E : Padic.FiniteCoefficientFields l Ω) :
    pbcIntegralStage l Ω T E ⥤ pbcAmbientStage l Ω T E :=
  ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω E))

/-- The recorded raw rationalization at the canonical small model of E.
Source: blueprint order 1308 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
abbrev pbcStageCategory (E : Padic.FiniteCoefficientFields l Ω) :=
  PbcRationalCategory T (pbcStageDatum.{u} l Ω E) (pbcStageUniformizer.{u} l Ω E)

/-- The recorded integral localization functor at this coefficient stage.
Source: blueprint order 1308 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
abbrev pbcStageLocalization (E : Padic.FiniteCoefficientFields l Ω) :=
  pbcRationalization T (pbcStageDatum.{u} l Ω E) (pbcStageUniformizer.{u} l Ω E)

/-- Finite coefficient extension preserves the three defining integral conditions.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category).
Proof: the target integer ring is finite free over the source integer ring.
Compute derived extension on K-flat representatives. Finite freeness commutes
with the reduction tower and its derived limit and preserves completion.
Tensor the common bounded local models and the compatible etale origins.
Their normalization equations follow from ordinary tensor balancing at every
finite quotient; neither the bounds nor the finite stratification changes. -/
theorem pbcAmbientScalarExtension_preserves (h : E ≤ F)
    [IsNoetherian T] (_hdim : ∃ m : ℕ, topologicalKrullDim T ≤ m)
    (_hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t))
    (K : pbcIntegralStage l Ω T E) :
    PbcIsBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω F)
      ((pbcAmbientScalarExtension l Ω T h).obj K.obj) := by
  sorry

variable [IsNoetherian T] (hdim : ∃ m : ℕ, topologicalKrullDim T ≤ m)
  (hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t))

/-- Restriction of the specified ambient tensor extension to the integral subcategories.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
def pbcIntegralScalarExtension (h : E ≤ F) :
    pbcIntegralStage l Ω T E ⥤
      pbcIntegralStage l Ω T F :=
  ObjectProperty.lift (PbcIsBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω F))
    ((pbcStageInclusion l Ω T E) ⋙
      pbcAmbientScalarExtension l Ω T h)
    (pbcAmbientScalarExtension_preserves l Ω T h hdim hl)

/-- Integral tensor extension has a unique factorization through raw localization.
The equality fixes objects as well as integral morphisms; inverses of uniformizer
multiples then fix every fraction. No arbitrary functor is chosen.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category).
Proof: the image of the source uniformizer is a unit times a positive power of
the target uniformizer, so it becomes invertible in the target localization.
Send a fraction f/pi^n to the integral tensor image of f divided by the image of
pi^n. The tensor relations, bilinearity and balancing prove well-definedness
and functoriality. Every localized morphism is such a fraction, proving uniqueness. -/
theorem pbcRationalScalarExtension_exists (h : E ≤ F) :
    ∃! B : pbcStageCategory l Ω T E ⥤
        pbcStageCategory l Ω T F,
      pbcStageLocalization l Ω T E ⋙ B =
        pbcIntegralScalarExtension l Ω T hdim hl h ⋙
          pbcStageLocalization l Ω T F := by
  sorry

/-- Raw rationalized tensor extension. Equal coefficient fields use identity literally.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
def pbcScalarExtension (h : E ≤ F) :
    pbcStageCategory l Ω T E ⥤
      pbcStageCategory l Ω T F :=
  by
    classical
    exact if e : E = F then e ▸ 𝟭 _ else
      (pbcRationalScalarExtension_exists l Ω T hdim hl h).exists.choose


set_option linter.unusedSectionVars false in
/-- Coefficient maps compose exactly, including repeated fields.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category).
Proof: both composites have the same quotient projections, because the field
inclusions compose. Use uniqueness of the completed limit map. -/
theorem pbcCompletedScalarMap_comp (h : E ≤ F) (k : F ≤ G) :
    pbcCompletedScalarMap l Ω T h ≫ pbcCompletedScalarMap l Ω T k =
      pbcCompletedScalarMap l Ω T (h.trans k) := by
  have hi : (pbcIntegerInclusion l Ω k).comp (pbcIntegerInclusion l Ω h) =
      pbcIntegerInclusion l Ω (h.trans k) := by
    apply RingHom.ext
    intro x
    apply ULift.ext
    apply Subtype.ext
    have hinc : pbcFiniteFieldInclusion l Ω k
        (pbcFiniteFieldInclusion l Ω h x.down.val) =
        pbcFiniteFieldInclusion l Ω (h.trans k) x.down.val := by
      change (Shrink.algEquiv (Padic l) G.val).symm
          (IntermediateField.inclusion k
            ((Shrink.algEquiv (Padic l) F.val)
              ((Shrink.algEquiv (Padic l) F.val).symm
                (IntermediateField.inclusion h
                  ((Shrink.algEquiv (Padic l) E.val) x.down.val))))) = _
      rw [AlgEquiv.apply_symm_apply]
      rfl
    simpa [pbcIntegerInclusion, WeilConjectures.integralScalarIntegerInclusion] using hinc
  have hq (n : ℕ) :
      (pbcQuotientInclusion l Ω k n).comp (pbcQuotientInclusion l Ω h n) =
        pbcQuotientInclusion l Ω (h.trans k) n := by
    apply RingHom.ext
    intro x
    refine Quotient.inductionOn' x ?_
    intro x
    change Ideal.Quotient.mk _ (pbcIntegerInclusion l Ω k (pbcIntegerInclusion l Ω h x)) =
      Ideal.Quotient.mk _ (pbcIntegerInclusion l Ω (h.trans k) x)
    exact congrArg (Ideal.Quotient.mk _) (RingHom.congr_fun hi x)
  have hf (n : ℕ) : pbcFiniteScalarMap l Ω T h n ≫ pbcFiniteScalarMap l Ω T k n =
      pbcFiniteScalarMap l Ω T (h.trans k) n := by
    dsimp only [pbcFiniteScalarMap]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Functor.map_comp_assoc]
    congr 2
    exact congrArg ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map)
      (congrArg CommRingCat.ofHom (hq n))
  apply (pbcCompletedScalarMap_exists l Ω T (h.trans k)).unique
  · intro n
    dsimp only [pbcCompletedScalarMap]
    rw [Category.assoc,
      (pbcCompletedScalarMap_exists l Ω T k).exists.choose_spec n,
      ← Category.assoc,
      (pbcCompletedScalarMap_exists l Ω T h).exists.choose_spec n,
      Category.assoc, hf n]
  · exact (pbcCompletedScalarMap_exists l Ω T (h.trans k)).exists.choose_spec

/-- The tensor unit comparison is fixed on sheafified pure tensors.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category).
Proof: inclusion E→E is identity, also on completions. The balanced map
r tensor x ↦ r*x and x ↦ 1 tensor x are inverse sectionwise, commute with
restriction, and descend through sheafification. Pure tensors generate locally,
so the indicated formula determines the natural isomorphism uniquely. -/
theorem pbcOrdinaryScalarUnit_exists (E : Padic.FiniteCoefficientFields l Ω) :
    ∃! e : pbcExtend (pbcCompletedScalarMap l Ω T (le_refl E)) ≅
        𝟭 (pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))),
      ∀ (M : pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E)))
        (U : T.ProEtᵒᵖ) (r : (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E)).obj.obj U)
        (x : M.val.obj U),
        (e.hom.app M).val.app U
          (pbcTensorSection (pbcCompletedScalarMap l Ω T (le_refl E)) M U r x) = r • x := by
  sorry

/-- The section-normalized ordinary tensor unit.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
def pbcOrdinaryScalarUnit (E : Padic.FiniteCoefficientFields l Ω) :
    pbcExtend (pbcCompletedScalarMap l Ω T (le_refl E)) ≅
        𝟭 (pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))) :=
  (pbcOrdinaryScalarUnit_exists l Ω T E).exists.choose

/-- The derived tensor unit is uniquely fixed by its universal counit on complexes.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category).
Proof: tensor extension along identity is exact. Its universal left-derived
counit is invertible; descend the section-normalized ordinary tensor unit.
Localization of complexes is essentially surjective and full on natural
transformations, so this normalization determines the comparison uniquely. -/
theorem pbcAmbientScalarUnit_exists (E : Padic.FiniteCoefficientFields l Ω) :
    ∃! e : pbcAmbientScalarExtension l Ω T (le_refl E) ≅
        𝟭 (pbcAmbientStage l Ω T E),
      ∀ P : CochainComplex (pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))) ℤ,
        e.hom.app (DerivedCategory.Q.obj P) =
          pbcComplexCounit (pbcCompletedScalarMap l Ω T (le_refl E)) P ≫
            DerivedCategory.Q.map
              ((NatTrans.mapHomologicalComplex
                (pbcOrdinaryScalarUnit l Ω T E).hom (.up ℤ)).app P) := by
  sorry

/-- The canonical derived tensor unit, rather than an arbitrary unit isomorphism.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
def pbcAmbientScalarUnit (E : Padic.FiniteCoefficientFields l Ω) :
    pbcAmbientScalarExtension l Ω T (le_refl E) ≅
        𝟭 (pbcAmbientStage l Ω T E) :=
  (pbcAmbientScalarUnit_exists l Ω T E).exists.choose

/-- The integral tensor unit is the restriction of the canonical ambient one.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category).
Proof: the integral subcategories are full. Lift each component of the ambient
unit and its inverse. Faithfulness gives naturality, inverse equations and
uniqueness. -/
theorem pbcIntegralScalarUnit_exists (E : Padic.FiniteCoefficientFields l Ω) :
    ∃! e : pbcIntegralScalarExtension l Ω T hdim hl (le_refl E) ≅
        𝟭 (pbcIntegralStage l Ω T E),
      Functor.whiskerRight e.hom
          (pbcStageInclusion l Ω T E) =
        Functor.whiskerLeft
          (pbcStageInclusion l Ω T E)
          (pbcAmbientScalarUnit l Ω T E).hom := by
  let e : pbcIntegralScalarExtension l Ω T hdim hl (le_refl E) ≅
      𝟭 (pbcIntegralStage l Ω T E) :=
    NatIso.ofComponents
      (fun K ↦ ObjectProperty.isoMk _ ((pbcAmbientScalarUnit l Ω T E).app K.obj))
      (fun f ↦ by
        apply ObjectProperty.hom_ext
        exact (pbcAmbientScalarUnit l Ω T E).hom.naturality f.hom)
  refine ⟨e, rfl, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext _
  exact congrArg (fun η ↦ η.app K) he'

/-- Integral unit with its ambient normalization.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
def pbcIntegralScalarUnit (E : Padic.FiniteCoefficientFields l Ω) :
    pbcIntegralScalarExtension l Ω T hdim hl (le_refl E) ≅
        𝟭 (pbcIntegralStage l Ω T E) :=
  (pbcIntegralScalarUnit_exists l Ω T hdim hl E).exists.choose

/-- The integral/rational comparison is fixed by the tensor unit at equal fields
and the unique localization factorization at distinct fields.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category).
Proof: at equal fields use the section-normalized tensor unit. Otherwise use the
equality in the unique factorization through scalar localization. These cases
are exhaustive. Heterogeneous equality retains the exact functor indices under
the literal identity normalization. Either formula specifies every component
and hence gives uniqueness. -/
theorem pbcScalarIntegralComparison_exists (h : E ≤ F) :
    ∃! c : pbcStageLocalization l Ω T E ⋙
        pbcScalarExtension l Ω T hdim hl h ≅
      pbcIntegralScalarExtension l Ω T hdim hl h ⋙
        pbcStageLocalization l Ω T F,
      (E = F → HEq c
        ((Functor.rightUnitor
          (pbcStageLocalization l Ω T E)) ≪≫
        (Functor.leftUnitor
          (pbcStageLocalization l Ω T E)).symm ≪≫
        Functor.isoWhiskerRight (pbcIntegralScalarUnit l Ω T hdim hl E).symm
          (pbcStageLocalization l Ω T E))) ∧
      (E ≠ F → HEq c
        (eqToIso (pbcRationalScalarExtension_exists l Ω T hdim hl h).exists.choose_spec)) := by
  classical
  by_cases hEF : E = F
  · subst F
    have hs : pbcScalarExtension l Ω T hdim hl h = 𝟭 _ := by
      simp [pbcScalarExtension]
    rw [hs]
    let e := (Functor.rightUnitor (pbcStageLocalization l Ω T E)) ≪≫
      (Functor.leftUnitor (pbcStageLocalization l Ω T E)).symm ≪≫
      Functor.isoWhiskerRight (pbcIntegralScalarUnit l Ω T hdim hl E).symm
        (pbcStageLocalization l Ω T E)
    refine ⟨e, ⟨fun _ ↦ HEq.rfl, fun hne ↦ (hne rfl).elim⟩, ?_⟩
    intro e' he'
    exact eq_of_heq (he'.1 rfl)
  · have hs : pbcScalarExtension l Ω T hdim hl h =
        (pbcRationalScalarExtension_exists l Ω T hdim hl h).exists.choose := by
      simp [pbcScalarExtension, hEF]
    rw [hs]
    refine ⟨eqToIso
      (pbcRationalScalarExtension_exists l Ω T hdim hl h).exists.choose_spec,
      ⟨fun heq ↦ (hEF heq).elim, fun _ ↦ HEq.rfl⟩, ?_⟩
    intro e' he'
    exact eq_of_heq (he'.2 hEF)

/-- The uniquely normalized comparison with integral scalar extension.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
def pbcScalarIntegralComparison (h : E ≤ F) :
    pbcStageLocalization l Ω T E ⋙
        pbcScalarExtension l Ω T hdim hl h ≅
      pbcIntegralScalarExtension l Ω T hdim hl h ⋙
        pbcStageLocalization l Ω T F :=
  (pbcScalarIntegralComparison_exists l Ω T hdim hl h).exists.choose

/-- The ambient tensor associator is the mate of composition of actual scalar
restrictions, normalized by their identity on sections.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
def pbcAmbientScalarAssociator (h : E ≤ F) (k : F ≤ G) :
    pbcAmbientScalarExtension l Ω T h ⋙ pbcAmbientScalarExtension l Ω T k ≅
      pbcAmbientScalarExtension l Ω T (h.trans k) :=
  Adjunction.leftAdjointCompIso
    (pbcDerivedScalarAdjunction (pbcCompletedScalarMap l Ω T h))
    (pbcDerivedScalarAdjunction (pbcCompletedScalarMap l Ω T k))
    (pbcDerivedScalarAdjunction (pbcCompletedScalarMap l Ω T (h.trans k)))
    (pbcDerivedRestrictComp (pbcCompletedScalarMap l Ω T h)
      (pbcCompletedScalarMap l Ω T k) (pbcCompletedScalarMap l Ω T (h.trans k))
      (pbcCompletedScalarMap_comp l Ω T h k))

/-- Restriction of the canonical ambient associator to the full integral subcategories.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category).
Proof: lift its components and inverse components using fullness. Naturality and
inverse equations follow after the faithful inclusion; the same inclusion gives
uniqueness. -/
theorem pbcIntegralScalarAssociator_exists (h : E ≤ F) (k : F ≤ G) :
    ∃! e : pbcIntegralScalarExtension l Ω T hdim hl h ⋙
        pbcIntegralScalarExtension l Ω T hdim hl k ≅
        pbcIntegralScalarExtension l Ω T hdim hl (h.trans k),
      Functor.whiskerRight e.hom
          (pbcStageInclusion l Ω T G) =
        Functor.whiskerLeft
          (pbcStageInclusion l Ω T E)
          (pbcAmbientScalarAssociator l Ω T h k).hom := by
  let e : pbcIntegralScalarExtension l Ω T hdim hl h ⋙
      pbcIntegralScalarExtension l Ω T hdim hl k ≅
      pbcIntegralScalarExtension l Ω T hdim hl (h.trans k) :=
    NatIso.ofComponents
      (fun K ↦ ObjectProperty.isoMk _ ((pbcAmbientScalarAssociator l Ω T h k).app K.obj))
      (fun f ↦ by
        apply ObjectProperty.hom_ext
        exact (pbcAmbientScalarAssociator l Ω T h k).hom.naturality f.hom)
  refine ⟨e, rfl, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext _
  exact congrArg (fun η ↦ η.app K) he'

/-- The integral associator with the ambient tensor normalization.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
def pbcIntegralScalarAssociator (h : E ≤ F) (k : F ≤ G) :
    pbcIntegralScalarExtension l Ω T hdim hl h ⋙
        pbcIntegralScalarExtension l Ω T hdim hl k ≅
        pbcIntegralScalarExtension l Ω T hdim hl (h.trans k) :=
  (pbcIntegralScalarAssociator_exists l Ω T hdim hl h k).exists.choose

/-- The rational associator is uniquely determined on the unchanged integral objects.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category).
Proof: apply target rationalization to the integral associator, conjugating by
the integral comparisons. Naturality holds on integral morphisms and hence on
their fractions. Rationalization is surjective on objects, giving uniqueness. -/
theorem pbcScalarAssociator_exists (h : E ≤ F) (k : F ≤ G) :
    ∃! e : pbcScalarExtension l Ω T hdim hl h ⋙
        pbcScalarExtension l Ω T hdim hl k ≅
        pbcScalarExtension l Ω T hdim hl (h.trans k),
      ∀ K : pbcIntegralStage l Ω T E,
        e.hom.app
            ((pbcStageLocalization l Ω T E).obj K) =
          (pbcScalarExtension l Ω T hdim hl k).map
              ((pbcScalarIntegralComparison l Ω T hdim hl h).hom.app K) ≫
            (pbcScalarIntegralComparison l Ω T hdim hl k).hom.app
              ((pbcIntegralScalarExtension l Ω T hdim hl h).obj K) ≫
            (pbcStageLocalization l Ω T G).map
              ((pbcIntegralScalarAssociator l Ω T hdim hl h k).hom.app K) ≫
            (pbcScalarIntegralComparison l Ω T hdim hl (h.trans k)).inv.app K := by
  sorry

/-- The scalar associator induced by tensor balancing, including the normalized units.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
def pbcScalarAssociator (h : E ≤ F) (k : F ≤ G) :
    pbcScalarExtension l Ω T hdim hl h ⋙
        pbcScalarExtension l Ω T hdim hl k ≅
        pbcScalarExtension l Ω T hdim hl (h.trans k) :=
  (pbcScalarAssociator_exists l Ω T hdim hl h k).exists.choose

/-- The tensor associators satisfy the pentagon in component form.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category).
Proof: the ambient associators are mates of identity-on-sections restriction
comparisons. Their two four-field composites therefore agree. Full integral
inclusions and rational integral comparisons transport that equality; every
rational object is an integral object, so these tests prove the displayed equality. -/
theorem pbcScalarAssociator_cocycle {H : Padic.FiniteCoefficientFields l Ω}
    (h : E ≤ F) (k : F ≤ G) (j : G ≤ H)
    (K : pbcStageCategory l Ω T E) :
    (pbcScalarExtension l Ω T hdim hl j).map
          ((pbcScalarAssociator l Ω T hdim hl h k).hom.app K) ≫
        (pbcScalarAssociator l Ω T hdim hl (h.trans k) j).hom.app K =
      (pbcScalarAssociator l Ω T hdim hl k j).hom.app
          ((pbcScalarExtension l Ω T hdim hl h).obj K) ≫
        (pbcScalarAssociator l Ω T hdim hl h (k.trans j)).hom.app K := by
  sorry

/-- Normalized tensor identities give the literal identity transitions and unit associators.
Source: blueprint order 1308 (blueprint: def-weil-pbc-finite-stage-pair-category).
Proof: the equal-field branch of pbcScalarExtension is identity by definition.
The ambient tensor-unit comparison is multiplication on pure tensors, and the
ambient associator is tensor balancing with the same ordinary adjunction units.
Their unit equations hold on those generators. Faithful integral inclusions and
rationalization transport the equations, including repeated coefficient fields. -/
theorem pbcScalarSystem_units (h : E ≤ F) :
    pbcScalarExtension l Ω T hdim hl (le_refl E) = 𝟭 _ ∧
      HEq (pbcScalarAssociator l Ω T hdim hl (le_refl E) h)
        (Functor.leftUnitor (pbcScalarExtension l Ω T hdim hl h)) ∧
      HEq (pbcScalarAssociator l Ω T hdim hl h (le_refl F))
        (Functor.rightUnitor (pbcScalarExtension l Ω T hdim hl h)) := by
  sorry

/-- Rationalized tensor extension is additive.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category).
Proof: tensor extension is additive on complexes and derived morphisms. The
localization formula sends sums of fractions to sums; identity fields are
literal identity functors, which are additive as well. -/
@[instance] theorem pbcScalarExtension_additive (h : E ≤ F) :
    (pbcScalarExtension l Ω T hdim hl h).Additive := by
  sorry

/-- The concrete finite-stage scalar system on the PBC raw rational categories.
Source: blueprint order 1307 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
abbrev pbcScalarSystem :
    StageSystem (fun E : Padic.FiniteCoefficientFields l Ω ↦
      pbcStageCategory l Ω T E) where
  T h := pbcScalarExtension l Ω T hdim hl h
  assoc h k := pbcScalarAssociator l Ω T hdim hl h k
  cocycle h k j K := pbcScalarAssociator_cocycle l Ω T hdim hl h k j K


/-- Finite composita give the common coefficient stages.
Source: blueprint finite-stage pair category
(blueprint: def-weil-pbc-finite-stage-pair-category). -/
instance pbcFiniteCoefficientFields_directed :
    IsDirectedOrder (Padic.FiniteCoefficientFields l Ω) :=
  ⟨fun E F ↦ ⟨Padic.finiteCoefficientCompositum l Ω E F,
    (Padic.finiteCoefficientFields_properties l Ω).1 E F⟩⟩

/-- The concrete PBC finite-stage pair category, without an idempotent envelope.
Its quotient representatives, transport, identities and common-stage composition
are exactly StageSystem.PairCategory with this concrete coefficient system.
Source: blueprint finite-stage pair category
(blueprint: def-weil-pbc-finite-stage-pair-category). -/
abbrev PbcFiniteStagePairCategory := (pbcScalarSystem l Ω T hdim hl).PairCategory

/-- The base field witnesses nonemptiness, including the empty-diagram case.
Source: blueprint order 1308 (blueprint: def-weil-pbc-finite-stage-pair-category). -/
instance pbcFiniteCoefficientFields_nonempty : Nonempty (Padic.FiniteCoefficientFields l Ω) :=
  ⟨Padic.finiteCoefficientBase l Ω⟩

end AlgebraicGeometry.Scheme

