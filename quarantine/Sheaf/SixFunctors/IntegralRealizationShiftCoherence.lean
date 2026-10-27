/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Sheaf.SixFunctors.IntegralOperationShiftData
public import Sheaf.SixFunctors.SynchronizedCanonicalMaps

import Sheaf.SixFunctors.IntegralRealizationRecursion
import Sheaf.SixFunctors.RealizationAdjunctionInsertionShift
import Sheaf.SixFunctors.RealizationTreeShiftTransport
import Sheaf.SixFunctors.CanonicalTreeGeneratorShiftLaws
import Sheaf.SixFunctors.CanonicalShiftSynchronization

/-! # Slotwise shift coherence of the specified integral realization

Source: blueprint sec-smooth-purity, sk-thm-purity-transport, Step 2
(blueprint: lem-pur-integral-realization-shift-coherence).

Input labels name occurrences. Their object values may be equal. The supplied
Realizations record is the actual comparison, with its primitive normalizations,
not a newly selected endpoint isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

open Classical in
/-- The displayed realization square, including closure of its full domain under
one independently labelled input shift.
Source: blueprint Step 2 (blueprint: lem-pur-integral-realization-shift-coherence). -/
def RealizationShiftSquare (D : FiniteFieldDatum.{u}) (o : Operations l E)
    (R : Realizations l E D o) {I : Type u} [Finite I]
    {X : I → Over (Spec (.of D.k))} {W : Over (Spec (.of D.k))}
    (e : IndependentExpression _ I X W) (ge : e.val.geometric)
    (K : (e.val.domain l E o).FullSubcategory) (i : I) (r : ℤ) : Prop :=
  ∃ h : e.val.domain l E o (Function.update K.obj i ((K.obj i)⟦r⟧)),
    (R.comparison e.val ge).hom.app ⟨Function.update K.obj i ((K.obj i)⟦r⟧), h⟩ ≫
        (e.integralShift l E K.obj i r).hom =
      (e.sourceShift l E o K.obj i r).hom ≫
        ((R.comparison e.val ge).hom.app K)⟦r⟧'

open Classical in
/-- The shift squares for the same system/integral canonical map, evaluated at
the original and shifted input families, with their actual output maps.
Source: blueprint Step 2 (blueprint: lem-pur-integral-realization-shift-coherence). -/
def CanonicalMapShiftSquares {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    (o : Operations l E) {W : Over B} (e t : IndependentExpression B I X W)
    (K : ∀ i, Integral l E (X i).left) (i : I) (r : ℤ)
    (s : e.val.systemObj l E o ((inputReduction l E X).obj K) ⟶
      t.val.systemObj l E o ((inputReduction l E X).obj K))
    (v : (e.val.evaluate (integralInterpretation l E)).obj K ⟶
      (t.val.evaluate (integralInterpretation l E)).obj K)
    (sNew : e.val.systemObj l E o
        ((inputReduction l E X).obj (Function.update K i ((K i)⟦r⟧))) ⟶
      t.val.systemObj l E o
        ((inputReduction l E X).obj (Function.update K i ((K i)⟦r⟧))))
    (vNew : (e.val.evaluate (integralInterpretation l E)).obj
        (Function.update K i ((K i)⟦r⟧)) ⟶
      (t.val.evaluate (integralInterpretation l E)).obj
        (Function.update K i ((K i)⟦r⟧))) : Prop :=
  (coefficientSequenceLimit l E W.left).map sNew ≫
      (t.sourceShift l E o K i r).hom =
    (e.sourceShift l E o K i r).hom ≫
      ((coefficientSequenceLimit l E W.left).map s)⟦r⟧' ∧
  vNew ≫ (t.integralShift l E K i r).hom =
    (e.integralShift l E K i r).hom ≫ v⟦r⟧'

open Classical in
/-- Shift every specified canonical map by retaining its constructor and finite
outer expression contexts. Existence covers every old canonical map; the universal
clause covers every evaluation of the same formal construction at the shifted inputs.
Source: blueprint Step 2 (blueprint: lem-pur-integral-realization-shift-coherence). -/
def CanonicalMapShiftCoherence (D : FiniteFieldDatum.{u}) (o : Operations l E)
    (R : Realizations l E D o) {I : Type u} [Finite I]
    {X : I → Over (Spec (.of D.k))} {W : Over (Spec (.of D.k))}
    (e t : IndependentExpression _ I X W) (K : (e.val.domain l E o).FullSubcategory)
    (i : I) (r : ℤ) : Prop :=
  ∀ (s : e.val.systemObj l E o ((inputReduction l E X).obj K.obj) ⟶
        t.val.systemObj l E o ((inputReduction l E X).obj K.obj))
    (v : (e.val.evaluate (integralInterpretation l E)).obj K.obj ⟶
      (t.val.evaluate (integralInterpretation l E)).obj K.obj),
    CanonicalPair l E o R.compositors R.openComparisons R.canonicalBridge R.properOpen
      R.ringedModels R.ringedOpenComparisons R.ringedProperOpen
      ((inputReduction l E X).obj K.obj) K.obj e.val t.val s v →
    (∃ sNew vNew,
      SynchronizedPair l E o R.compositors R.openComparisons R.canonicalBridge R.properOpen
          R.ringedModels R.ringedOpenComparisons R.ringedProperOpen
          ((inputReduction l E X).obj K.obj) K.obj
          ((inputReduction l E X).obj (Function.update K.obj i ((K.obj i)⟦r⟧)))
          (Function.update K.obj i ((K.obj i)⟦r⟧)) e.val t.val s v sNew vNew) ∧
      ∀ sNew vNew,
        SynchronizedPair l E o R.compositors R.openComparisons R.canonicalBridge R.properOpen
          R.ringedModels R.ringedOpenComparisons R.ringedProperOpen
          ((inputReduction l E X).obj K.obj) K.obj
          ((inputReduction l E X).obj (Function.update K.obj i ((K.obj i)⟦r⟧)))
          (Function.update K.obj i ((K.obj i)⟦r⟧)) e.val t.val s v sNew vNew →
        CanonicalMapShiftSquares l E o e t K.obj i r s v sNew vNew

private def OccurrenceMatching {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    {W : Over B} (e t : Expression B I X W) : Prop :=
  ∃ f : e.Occurrences ≃ t.Occurrences, ∀ j, e.occurrenceLabel j = t.occurrenceLabel (f j)

private theorem occurrenceMatching_refl {B : Scheme.{u}} {I : Type u}
    {X : I → Over B} {W : Over B} (e : Expression B I X W) :
    OccurrenceMatching e e := ⟨Equiv.refl _, fun _ ↦ rfl⟩

private theorem occurrenceMatching_symm {B : Scheme.{u}} {I : Type u}
    {X : I → Over B} {W : Over B} {e t : Expression B I X W}
    (h : OccurrenceMatching e t) : OccurrenceMatching t e := by
  obtain ⟨f, hf⟩ := h
  refine ⟨f.symm, fun j ↦ ?_⟩
  simpa only [Equiv.apply_symm_apply] using (hf (f.symm j)).symm

private theorem occurrenceMatching_trans {B : Scheme.{u}} {I : Type u}
    {X : I → Over B} {W : Over B} {e t v : Expression B I X W}
    (h : OccurrenceMatching e t) (k : OccurrenceMatching t v) :
    OccurrenceMatching e v := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨g, hg⟩ := k
  exact ⟨f.trans g, fun j ↦ (hf j).trans (hg (f j))⟩

private theorem occurrenceMatching_tensor {B : Scheme.{u}} {I : Type u}
    {X : I → Over B} {W : Over B} {e t v z : Expression B I X W}
    (h : OccurrenceMatching e t) (k : OccurrenceMatching v z) :
    OccurrenceMatching (.tensor e v) (.tensor t z) := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨g, hg⟩ := k
  exact ⟨Equiv.sumCongr f g, fun j ↦ by cases j with
    | inl j => exact hf j
    | inr j => exact hg j⟩

section OccurrencePreservation
variable {o : Operations l E} {c : Compositors l E o} {a : OpenComparisons l E o c}
  {bridge : CanonicalBridge l E o} {h : ProperOpenCoherence l E o c a bridge}
  {d : RingedModels l E} {b : RingedOpenComparisons l E d} {q : RingedProperOpen l E d b}
  {B : Scheme.{u}} {I : Type u} {X : I → Over B}
  {M : ∀ i, System l E (X i).left} {K : ∀ i, Integral l E (X i).left}

private theorem canonicalIso_matching {W : Over B} {e t : Expression B I X W}
    {s : e.systemObj l E o M ≅ t.systemObj l E o M}
    {v : e.ringedObj l E d K ≅ t.ringedObj l E d K}
    (g : CanonicalIsoPair l E o c a d b M K e t s v) : OccurrenceMatching e t := by
  cases g with
  | tensorAssoc e f g =>
    refine ⟨Equiv.sumAssoc _ _ _, ?_⟩
    intro j
    rcases j with (j | j) | j <;> rfl
  | _ => exact ⟨Equiv.refl _, fun _ ↦ rfl⟩

private theorem basic_matching {W : Over B} {e t : Expression B I X W}
    {s : e.systemObj l E o M ⟶ t.systemObj l E o M}
    {v : e.ringedObj l E d K ⟶ t.ringedObj l E d K}
    (g : BasicPair l E o c a bridge h d b q M K e t s v) : OccurrenceMatching e t := by
  cases g with
  | isoHom g => exact canonicalIso_matching l E g
  | isoInv g => exact occurrenceMatching_symm (canonicalIso_matching l E g)
  | _ => exact ⟨Equiv.refl _, fun _ ↦ rfl⟩

private theorem canonicalPair_matching {W : Over B} {e t : Expression B I X W}
    {s : e.systemObj l E o M ⟶ t.systemObj l E o M}
    {v : (e.evaluate (integralInterpretation l E)).obj K ⟶
      (t.evaluate (integralInterpretation l E)).obj K}
    (g : CanonicalPair l E o c a bridge h d b q M K e t s v) :
    OccurrenceMatching e t := by
  induction g with
  | basic g _ => exact basic_matching l E g
  | identity e => exact occurrenceMatching_refl e
  | comp _ _ _ _ ih₁ ih₂ => exact occurrenceMatching_trans ih₁ ih₂
  | pull _ _ ih => exact ih
  | push _ _ _ ih => exact ih
  | shriek _ _ _ ih => exact ih
  | compactSupport _ _ _ ih => exact ih
  | tensor _ _ ih₁ ih₂ => exact occurrenceMatching_tensor ih₁ ih₂

private theorem occurrenceMatching_injective {W : Over B} {e t : Expression B I X W}
    (h : OccurrenceMatching e t) (hi : Function.Injective e.occurrenceLabel) :
    Function.Injective t.occurrenceLabel := by
  obtain ⟨f, hf⟩ := h
  intro x y hxy
  apply f.symm.injective
  apply hi
  simpa only [hf, Equiv.apply_symm_apply] using hxy

end OccurrencePreservation

private theorem synchronizedPair_selected (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) (bridge : CanonicalBridge l E o)
    (h : ProperOpenCoherence l E o c a bridge) (d : RingedModels l E)
    (b : RingedOpenComparisons l E d) (q : RingedProperOpen l E d b)
    {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    (M : ∀ i, System l E (X i).left) (K : ∀ i, Integral l E (X i).left)
    (MNew : ∀ i, System l E (X i).left) (KNew : ∀ i, Integral l E (X i).left)
    {W : Over B} {e t : Expression B I X W}
    {s : e.systemObj l E o M ⟶ t.systemObj l E o M}
    {v : (e.evaluate (integralInterpretation l E)).obj K ⟶
      (t.evaluate (integralInterpretation l E)).obj K}
    {sNew : e.systemObj l E o MNew ⟶ t.systemObj l E o MNew}
    {vNew : (e.evaluate (integralInterpretation l E)).obj KNew ⟶
      (t.evaluate (integralInterpretation l E)).obj KNew}
    (g : SynchronizedPair l E o c a bridge h d b q M K MNew KNew e t s v sNew vNew)
    (hi : Function.Injective e.occurrenceLabel) :
    TreeSynchronizedPair l E o c a bridge h d b q M K MNew KNew
      (fun {_} {_ _} {_ _ _ _} _ ↦ True) e t s v sNew vNew := by
  induction g with
  | basic g he heNew => exact .basic g trivial he heNew
  | identity e => exact .identity e
  | comp gt ht htNew g₁ _ ih₁ ih₂ =>
    have hj := occurrenceMatching_injective
      (canonicalPair_matching l E (g₁.components l E o c a bridge h d b q M K MNew KNew).1) hi
    exact .comp gt hj ht htNew (ih₁ hi) (ih₂ hj)
  | pull f _ ih => exact .pull f (ih hi)
  | push f hf _ ih => exact .push f hf (ih hi)
  | shriek f hq _ ih => exact .shriek f hq (ih hi)
  | compactSupport f cf _ ih => exact .compactSupport f cf (ih hi)
  | tensor _ _ ih₁ ih₂ =>
    exact .tensor (ih₁ (hi.comp Sum.inl_injective)) (ih₂ (hi.comp Sum.inr_injective))

private theorem map_shift_square {C D : Type*} [Category* C] [Category* D]
    [HasShift C ℤ] [HasShift D ℤ] (L : C ⥤ D) (r : ℤ)
    (α : shiftFunctor C r ⋙ L ≅ L ⋙ shiftFunctor D r)
    {A B ANew BNew : C} (s : A ⟶ B) (sNew : ANew ⟶ BNew)
    (χA : ANew ≅ A⟦r⟧) (χB : BNew ≅ B⟦r⟧)
    (h : sNew ≫ χB.hom = χA.hom ≫ s⟦r⟧') :
    L.map sNew ≫ (L.mapIso χB ≪≫ α.app B).hom =
      (L.mapIso χA ≪≫ α.app A).hom ≫ (L.map s)⟦r⟧' := by
  have hα : L.map (s⟦r⟧') ≫ α.hom.app B = α.hom.app A ≫ (L.map s)⟦r⟧' := by
    simpa only [Functor.comp_map] using α.hom.naturality s
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  rw [← L.map_comp_assoc, h, L.map_comp, Category.assoc, Category.assoc, hα]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
open Classical in
private theorem limit_systemShift_square (o : Operations l E)
    {B : Scheme.{u}} {I : Type u} {X : I → Over B} {W : Over B}
    (e t : IndependentExpression _ I X W) (K : ∀ i, Integral l E (X i).left)
    (i : I) (r : ℤ)
    (s : e.val.systemObj l E o ((inputReduction l E X).obj K) ⟶
      t.val.systemObj l E o ((inputReduction l E X).obj K))
    (sNew : e.val.systemObj l E o
        ((inputReduction l E X).obj (Function.update K i ((K i)⟦r⟧))) ⟶
      t.val.systemObj l E o
        ((inputReduction l E X).obj (Function.update K i ((K i)⟦r⟧))))
    (hs : sNew ≫ (treeSystemShift l E o t K i r).hom =
      (treeSystemShift l E o e K i r).hom ≫ s⟦r⟧') :
    (coefficientSequenceLimit l E W.left).map sNew ≫ (t.sourceShift l E o K i r).hom =
      (e.sourceShift l E o K i r).hom ≫
        ((coefficientSequenceLimit l E W.left).map s)⟦r⟧' := by
  let L := coefficientSequenceLimit l E W.left
  let α := Functor.commShiftIso L (self := limitShift l E W.left) r
  change L.map sNew ≫ (L.mapIso (treeSystemShift l E o t K i r) ≪≫ α.app _).hom =
    (L.mapIso (treeSystemShift l E o e K i r) ≪≫ α.app _).hom ≫ (L.map s)⟦r⟧'
  exact map_shift_square L r α s sNew (treeSystemShift l E o e K i r)
    (treeSystemShift l E o t K i r) hs

private theorem canonicalTreeGeneratorShiftLaws (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (o : Operations l E) (R : Realizations l E D o) :
    TreeGeneratorShiftLaws l E D o R (canonicalTreeGenerators l E D o R) := by
  classical
  intro I _ X W e t ei ti ge gt K i r he ht heNew htNew s v sNew vNew g _
    c hc hOld hNew d hd kOld kNew
  refine ⟨canonicalTreeGeneratorSystemShift l E D hl o R e t ei ti ge gt K i r
    he ht heNew htNew s v sNew vNew g c hc hOld hNew d hd kOld kNew, ?_, ?_⟩
  all_goals
    let := R.completionIso e ge ⟨K, he⟩
    let := R.completionIso e ge ⟨Function.update K i ((K i)⟦r⟧), heNew⟩
    have hcanon :=
      (SynchronizedPair.basic g (R.completionIso e ge ⟨K, he⟩)
        (R.completionIso e ge ⟨Function.update K i ((K i)⟦r⟧), heNew⟩)).components
        l E o R.compositors R.openComparisons R.canonicalBridge R.properOpen
        R.ringedModels R.ringedOpenComparisons R.ringedProperOpen _ _ _ _
  · simpa only [GeneratorReduction.inverseOrZero, dif_pos (inferInstance :
      IsIso (e.completionMap l E R.ringedModels K))] using
      R.coherence e t ge gt ⟨K, he⟩ ht s _ hcanon.1
  · simpa only [GeneratorReduction.inverseOrZero, dif_pos (inferInstance :
      IsIso (e.completionMap l E R.ringedModels
        (Function.update K i ((K i)⟦r⟧))))] using
      R.coherence e t ge gt ⟨Function.update K i ((K i)⟦r⟧), heNew⟩ htNew sNew _ hcanon.2

/-- The actual canonical integral realization commutes with a shift in any one
independent leaf, naturally in all input objects, and with every specified
canonical map and every finite expression context.
Source: blueprint sec-smooth-purity, sk-thm-purity-transport, Step 2
(blueprint: lem-pur-integral-realization-shift-coherence).

Proof: apply realizationTreeShiftTransport with the supplied adjunction-insertion
and recursion equations and the collection selecting every synchronized basic map.
Its system-generator premise is canonicalTreeGeneratorSystemShift. The two integral
intertwining equations follow directly from R.coherence, because R.completionIso
identifies the basic transported map with its actual completion inverse at both
families. This proves the first clause and the intrinsic map transport for the tree
relation.

For the second clause, canonicalShiftSynchronization constructs the shifted map
using the original constructors. Every canonical constructor preserves the labelled
occurrence set; tensor associativity uses the associativity equivalence of sums.
Induction on CanonicalPair therefore propagates injectivity to the intermediate
expression of a composition. Induction on SynchronizedPair now places every witness
in the selected tree relation. Apply the tree transport theorem, retain its integral
square, and map its system square through coefficientSequenceLimit. Naturality of
the limit/shift comparison gives exactly the stated sourceShift square. -/
theorem integralRealizationShiftCoherence (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    (o : Operations l E) (R : Realizations l E D o) :
    (∀ {I : Type u} [Finite I] {X : I → Over (Spec (.of D.k))}
      {W : Over (Spec (.of D.k))} (e : IndependentExpression _ I X W)
      (ge : e.val.geometric) (K : (e.val.domain l E o).FullSubcategory) (i : I) (r : ℤ),
      RealizationShiftSquare l E D o R e ge K i r) ∧
    (∀ {I : Type u} [Finite I] {X : I → Over (Spec (.of D.k))}
      {W : Over (Spec (.of D.k))} (e t : IndependentExpression _ I X W)
      (_ge : e.val.geometric) (_gt : t.val.geometric)
      (K : (e.val.domain l E o).FullSubcategory) (_ht : t.val.domain l E o K.obj)
      (i : I) (r : ℤ), CanonicalMapShiftCoherence l E D o R e t K i r) := by
  classical
  have htree := realizationTreeShiftTransport l E D _hl o R
    (realizationAdjunctionInsertionShift l E D _hl o R)
    (Recursion.integralRealizationRecursion l E D _hl o R).2.1
    (canonicalTreeGenerators l E D o R)
    (canonicalTreeGeneratorShiftLaws l E D _hl o R)
  refine ⟨htree.1, ?_⟩
  intro I _ X W e t ge gt K ht i r s v hpair
  refine ⟨canonicalShiftSynchronization l E D _hl o R e t ge gt K ht i r s v hpair, ?_⟩
  intro sNew vNew hsync
  have hselected := synchronizedPair_selected l E o R.compositors R.openComparisons
    R.canonicalBridge R.properOpen R.ringedModels R.ringedOpenComparisons
    R.ringedProperOpen _ _ _ _ hsync e.property.injective
  obtain ⟨heNew, htNew, hs, hv, _⟩ :=
    htree.2.1 e t ge gt K.obj i r K.property ht s v sNew vNew hselected
  exact ⟨limit_systemShift_square l E o e t K.obj i r s sNew hs, hv⟩

end WeilConjectures.IntegralSystemRealization
