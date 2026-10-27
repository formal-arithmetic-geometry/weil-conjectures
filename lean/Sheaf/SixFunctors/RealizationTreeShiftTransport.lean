/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q40
-/
module

public import Sheaf.SixFunctors.RealizationTreeShiftData
public import Sheaf.SixFunctors.IntegralOperationShiftData
public import Sheaf.SixFunctors.IntegralRealizationRecursion
public import Sheaf.SixFunctors.SynchronizedCanonicalMaps
public import Sheaf.SixFunctors.RealizationAdjunctionInsertionShift
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.SixFunctors.IntegralCompactificationSystemRealization
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.FiniteTorAmplitudeSites

import Sheaf.SixFunctors.RealizationTreeSingleShift
import Sheaf.SixFunctors.RealizationTreeSystemSquare

/-! # Conditional transport of realization shift squares through finite trees

Source: current blueprint, sec-six-functors/sk-thm-sf-compatibility,
fix-prop-coherence.proof.md, coefficient-comparison and inherited-equations sentences;
the eight agent-written proof steps of lem-pur-realization-tree-shift-transport
(blueprint: lem-pur-realization-tree-shift-transport).

Every comparison below is assembled from the recorded operations, dependent input
updates and the designated tensor side. Generator squares are hypotheses, including
an equality in the derived system category before total limit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Forget selection and the additional independent-intermediate witness. -/
private theorem treePair_forget
    (o : Operations l E) (c : Compositors l E o) (a : OpenComparisons l E o c)
    (bridge : CanonicalBridge l E o) (h : ProperOpenCoherence l E o c a bridge)
    (d : RingedModels l E) (b : RingedOpenComparisons l E d)
    (q : RingedProperOpen l E d b)
    {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    (M : ∀ i, System l E (X i).left) (K : ∀ i, Integral l E (X i).left)
    (MNew : ∀ i, System l E (X i).left) (KNew : ∀ i, Integral l E (X i).left)
    (G : TreeGeneratorSelection l E o c a bridge h d b q M K MNew KNew)
    {W : Over B} {e t : Expression B I X W}
    {s : e.systemObj l E o M ⟶ t.systemObj l E o M}
    {v : (e.evaluate (integralInterpretation l E)).obj K ⟶
      (t.evaluate (integralInterpretation l E)).obj K}
    {sNew : e.systemObj l E o MNew ⟶ t.systemObj l E o MNew}
    {vNew : (e.evaluate (integralInterpretation l E)).obj KNew ⟶
      (t.evaluate (integralInterpretation l E)).obj KNew}
    (pair : TreeSynchronizedPair l E o c a bridge h d b q M K MNew KNew G
      e t s v sNew vNew) :
    SynchronizedPair l E o c a bridge h d b q M K MNew KNew e t s v sNew vNew := by
  induction pair with
  | basic g _ he heNew => exact .basic g he heNew
  | identity e => exact .identity e
  | comp gt _ ht htNew _ _ ih₁ ih₂ => exact .comp gt ht htNew ih₁ ih₂
  | pull f _ ih => exact .pull f ih
  | push f hf _ ih => exact .push f hf ih
  | shriek f hq _ ih => exact .shriek f hq ih
  | compactSupport f cf _ ih => exact .compactSupport f cf ih
  | tensor _ _ ih₁ ih₂ => exact .tensor ih₁ ih₂

/-- Pasting a system square with a natural total-limit shift. -/
private theorem map_shift_square
    {S C : Type*} [Category S] [Category C] [HasShift S ℤ] [HasShift C ℤ]
    (F : S ⥤ C) (σ : F.CommShift ℤ) (r : ℤ)
    {M N M' N' : S} (α : M' ≅ M⟦r⟧) (β : N' ≅ N⟦r⟧)
    (s : M ⟶ N) (s' : M' ⟶ N')
    (hs : s' ≫ β.hom = α.hom ≫ s⟦r⟧') :
    F.map s' ≫ (F.mapIso β ≪≫ (Functor.commShiftIso F (self := σ) r).app N).hom =
      (F.mapIso α ≪≫ (Functor.commShiftIso F (self := σ) r).app M).hom ≫
        (F.map s)⟦r⟧' := by
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← F.map_comp, hs, F.map_comp, Category.assoc]
  simpa only [Functor.comp_map, Iso.app_hom, Category.assoc] using
    congrArg (fun z ↦ F.map α.hom ≫ z)
      ((Functor.commShiftIso F (self := σ) r).hom.naturality s)

/-- A square transports through invertible realization components. -/
private theorem transport_square
    {C : Type*} [Category C] [HasShift C ℤ] (r : ℤ)
    {A B A' B' X Y X' Y' : C}
    (a : A ≅ X) (b : B ≅ Y) (a' : A' ≅ X') (b' : B' ≅ Y')
    (α : A' ≅ A⟦r⟧) (β : B' ≅ B⟦r⟧)
    (γ : X' ≅ X⟦r⟧) (δ : Y' ≅ Y⟦r⟧)
    (s : A ⟶ B) (s' : A' ⟶ B') (v : X ⟶ Y) (v' : X' ⟶ Y')
    (hs : s' ≫ β.hom = α.hom ≫ s⟦r⟧')
    (ha : a'.hom ≫ γ.hom = α.hom ≫ a.hom⟦r⟧')
    (hb : b'.hom ≫ δ.hom = β.hom ≫ b.hom⟦r⟧')
    (hv : s ≫ b.hom = a.hom ≫ v) (hv' : s' ≫ b'.hom = a'.hom ≫ v') :
    v' ≫ δ.hom = γ.hom ≫ v⟦r⟧' := by
  apply (cancel_epi a'.hom).mp
  calc
    a'.hom ≫ (v' ≫ δ.hom) = s' ≫ (b'.hom ≫ δ.hom) := by
      rw [← Category.assoc, ← hv', Category.assoc]
    _ = s' ≫ (β.hom ≫ b.hom⟦r⟧') := by rw [hb]
    _ = α.hom ≫ (s⟦r⟧' ≫ b.hom⟦r⟧') := by
      rw [← Category.assoc, hs, Category.assoc]
    _ = α.hom ≫ (a.hom⟦r⟧' ≫ v⟦r⟧') := by
      rw [← Functor.map_comp, hv, Functor.map_comp]
    _ = a'.hom ≫ (γ.hom ≫ v⟦r⟧') := by
      rw [← Category.assoc, ← ha, Category.assoc]

open Classical in
/-- Conditional recursion and transport for the specified realization comparisons.
The three hypotheses are exactly local insertion squares, actual recursion, and
local synchronized generator squares/intertwining. No such square is concluded
without these hypotheses.

Source: current blueprint sec-six-functors/sk-thm-sf-compatibility,
fix-prop-coherence.proof.md, coefficient-comparison and inherited-equations sentences;
agent-written conditional obligation, proof steps 1--8
(blueprint: lem-pur-realization-tree-shift-transport).

Proof:
1. Shifts preserve integral completeness and constructibility by
lem-weil-integral-constructible-triangulated. Shift each strict normalized transition
and its scalar-extension adjoint, preserving invertibility. Shift the retained etale
antecedents and their actual transition squares. The cohomology and Tor intervals
translate by -r, using lem-weil-proetale-tor-interval-shift. Along the unique selected
path each intermediate is the old one shifted, and every other intermediate is
unchanged. Include the hidden open-extension intermediate of compact support.
Finitely many endpoints give common finite intervals by taking minima and maxima.
2. Induct on the finite tree. At a leaf the recursion identifies c with u inverse,
so the assumed inverse-unit square is exactly the desired comparison square.
3. At a unary vertex substitute c_AX=a_A followed by A_int(c_X). Apply the child
square, naturality of the designated A shift, and the assumed insertion square.
Compact support is the recorded open/proper composite, with its same intermediate.
4. At a left tensor occurrence apply the child square in that slot, naturality of
the unsigned first-slot comparison, then the first insertion square. At a right
occurrence use the signed second-slot comparison throughout, with coefficient
(-1)^(rj) on first degree j. The other child is fixed, and no symmetry is inserted.
The supplied c and shift isomorphisms are natural in the entire input family.
5. For an intertwining pair f, substitute the recursion at a unary outer vertex
and use naturality of a_A. For a left or right tensor context use binary naturality
of a_tensor in that same slot. This preserves equality for the actual integral map.
6. For composition cancel the intervening inverse realization comparisons; identity
is immediate. Two tensor changes factor as (f,1) followed by (1,g), by bifunctoriality.
Retain both intermediate geometric/admissibility witnesses from SynchronizedPair.
7. Paste system shift squares under composition and unary contexts. At a tensor
context use the designated slot comparison's naturality in both operands; this also
covers a selected leaf in the spectator operand. Thus the square holds inside D(S),
without using finite evaluations to detect equality.
8. Apply total limit to that system square, use naturality of its fixed shift, and
substitute the two expression squares and actual intertwining equalities. Cancel
the realization isomorphisms to obtain the integral square. Finally induct on the
finite list of independent input changes, shifting each preceding equality by the
remaining output shifts. This gives exactly the displayed successive comparisons;
distinct dependent updates commute. Zero and negative integers use the same formulas.
-/
theorem realizationTreeShiftTransport (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    (o : Operations l E) (R : Realizations l E D o)
    (_hInsertion : RealizationAdjunctionInsertionShift l E D o R)
    (_hRecursion : ∀ {I : Type u} [Finite I]
      {X : I → Over (Spec (.of D.k))} {W : Over (Spec (.of D.k))}
      (e : Expression _ I X W) (ge : e.geometric) (K : (e.domain l E o).FullSubcategory),
      Recursion.BasicTree e → Recursion.Equations l E R R.comparison e ge K)
    (G : TreeGenerators l E D o R)
    (_hGenerators : TreeGeneratorShiftLaws l E D o R G) :
    (∀ {I : Type u} [Finite I] {X : I → Over (Spec (.of D.k))}
      {W : Over (Spec (.of D.k))} (e : IndependentExpression _ I X W)
      (ge : e.val.geometric) (K : (e.val.domain l E o).FullSubcategory) (i : I) (r : ℤ),
      ∃ h : e.val.domain l E o (Function.update K.obj i ((K.obj i)⟦r⟧)),
        (R.comparison e.val ge).hom.app ⟨Function.update K.obj i ((K.obj i)⟦r⟧), h⟩ ≫
            (e.integralShift l E K.obj i r).hom =
          (e.sourceShift l E o K.obj i r).hom ≫
            ((R.comparison e.val ge).hom.app K)⟦r⟧') ∧
    (∀ {I : Type u} [Finite I] {X : I → Over (Spec (.of D.k))}
      {W : Over (Spec (.of D.k))} (e t : IndependentExpression _ I X W)
      (ge : e.val.geometric) (gt : t.val.geometric)
      (K : ∀ i, Integral l E (X i).left) (i : I) (r : ℤ)
      (he : e.val.domain l E o K) (ht : t.val.domain l E o K)
      (s : e.val.systemObj l E o ((inputReduction l E X).obj K) ⟶
        t.val.systemObj l E o ((inputReduction l E X).obj K))
      (v : (e.val.evaluate (integralInterpretation l E)).obj K ⟶
        (t.val.evaluate (integralInterpretation l E)).obj K)
      (sNew : e.val.systemObj l E o ((inputReduction l E X).obj
          (Function.update K i ((K i)⟦r⟧))) ⟶
        t.val.systemObj l E o ((inputReduction l E X).obj
          (Function.update K i ((K i)⟦r⟧))))
      (vNew : (e.val.evaluate (integralInterpretation l E)).obj
          (Function.update K i ((K i)⟦r⟧)) ⟶
        (t.val.evaluate (integralInterpretation l E)).obj
          (Function.update K i ((K i)⟦r⟧))),
      TreeSynchronizedPair l E o R.compositors R.openComparisons R.canonicalBridge R.properOpen
        R.ringedModels R.ringedOpenComparisons R.ringedProperOpen
        ((inputReduction l E X).obj K) K
        ((inputReduction l E X).obj (Function.update K i ((K i)⟦r⟧)))
        (Function.update K i ((K i)⟦r⟧))
        (G.selected ((inputReduction l E X).obj K) K
          ((inputReduction l E X).obj (Function.update K i ((K i)⟦r⟧)))
          (Function.update K i ((K i)⟦r⟧))) e.val t.val s v sNew vNew →
      ∃ (heNew : e.val.domain l E o (Function.update K i ((K i)⟦r⟧)))
        (htNew : t.val.domain l E o (Function.update K i ((K i)⟦r⟧))),
        TreeMapTransport l E D o R e t ge gt K i r he ht heNew htNew s v sNew vNew) ∧
    (∀ {I : Type u} [Finite I] {X : I → Over (Spec (.of D.k))}
      {W : Over (Spec (.of D.k))} (e : IndependentExpression _ I X W)
      (ge : e.val.geometric) (K : (e.val.domain l E o).FullSubcategory)
      (q : List (I × ℤ)) (_hq : (q.map Prod.fst).Nodup),
      ∃ h : e.val.domain l E o (treeShiftInputs l E X q K.obj),
        (R.comparison e.val ge).hom.app ⟨treeShiftInputs l E X q K.obj, h⟩ ≫
            (treeIntegralShifts l E e q K.obj).hom =
          (treeSourceShifts l E o e q K.obj).hom ≫
            (treeOutputShifts l E W.left q).map ((R.comparison e.val ge).hom.app K)) := by
  classical
  have single : (∀ {I : Type u} [Finite I] {X : I → Over (Spec (.of D.k))}
      {W : Over (Spec (.of D.k))} (e : IndependentExpression _ I X W)
      (ge : e.val.geometric) (K : (e.val.domain l E o).FullSubcategory) (i : I) (r : ℤ),
      ∃ h : e.val.domain l E o (Function.update K.obj i ((K.obj i)⟦r⟧)),
        (R.comparison e.val ge).hom.app ⟨Function.update K.obj i ((K.obj i)⟦r⟧), h⟩ ≫
            (e.integralShift l E K.obj i r).hom =
          (e.sourceShift l E o K.obj i r).hom ≫
            ((R.comparison e.val ge).hom.app K)⟦r⟧') :=
    realizationTreeSingleShift l E D _hl o R _hInsertion _hRecursion
  refine ⟨single, ?_, ?_⟩
  · intro I _ X W e t ge gt K i r he ht s v sNew vNew pair
    obtain ⟨heNew, heSquare⟩ := single e ge ⟨K, he⟩ i r
    obtain ⟨htNew, htSquare⟩ := single t gt ⟨K, ht⟩ i r
    have hs := realizationTreeSystemSquare l E D _hl o R G _hGenerators
      e t ge gt K i r he ht s v sNew vNew pair heNew htNew
    have pair' := treePair_forget l E o R.compositors R.openComparisons
      R.canonicalBridge R.properOpen R.ringedModels R.ringedOpenComparisons
      R.ringedProperOpen _ K _ (Function.update K i ((K i)⟦r⟧)) _ pair
    obtain ⟨oldPair, newPair⟩ := pair'.components
    have hv := R.coherence e.val t.val ge gt ⟨K, he⟩ ht s v oldPair
    have hvNew := R.coherence e.val t.val ge gt
      ⟨Function.update K i ((K i)⟦r⟧), heNew⟩ htNew sNew vNew newPair
    have hsource := map_shift_square (coefficientSequenceLimit l E W.left)
      (limitShift l E W.left) r (treeSystemShift l E o e K i r)
      (treeSystemShift l E o t K i r) s sNew hs
    change (coefficientSequenceLimit l E W.left).map sNew ≫
        (t.sourceShift l E o K i r).hom =
      (e.sourceShift l E o K i r).hom ≫
        ((coefficientSequenceLimit l E W.left).map s)⟦r⟧' at hsource
    refine ⟨heNew, htNew, hs, ?_, hv, hvNew⟩
    exact transport_square r
      ((R.comparison e.val ge).app ⟨K, he⟩)
      ((R.comparison t.val gt).app ⟨K, ht⟩)
      ((R.comparison e.val ge).app ⟨Function.update K i ((K i)⟦r⟧), heNew⟩)
      ((R.comparison t.val gt).app ⟨Function.update K i ((K i)⟦r⟧), htNew⟩)
      (e.sourceShift l E o K i r) (t.sourceShift l E o K i r)
      (e.integralShift l E K i r) (t.integralShift l E K i r)
      _ _ v vNew hsource heSquare htSquare hv hvNew
  · intro I _ X W e ge K q _hq
    -- The ordered composite works even when a label occurs more than once in q.
    have allLists (q : List (I × ℤ)) :
        ∀ K : (e.val.domain l E o).FullSubcategory,
        ∃ h : e.val.domain l E o (treeShiftInputs l E X q K.obj),
          (R.comparison e.val ge).hom.app ⟨treeShiftInputs l E X q K.obj, h⟩ ≫
              (treeIntegralShifts l E e q K.obj).hom =
            (treeSourceShifts l E o e q K.obj).hom ≫
              (treeOutputShifts l E W.left q).map ((R.comparison e.val ge).hom.app K) := by
      induction q with
      | nil =>
        intro K
        refine ⟨K.property, ?_⟩
        change (R.comparison e.val ge).hom.app K ≫ 𝟙 _ =
          𝟙 _ ≫ (R.comparison e.val ge).hom.app K
        simp only [Category.comp_id, Category.id_comp]
      | cons ir q ih =>
        obtain ⟨i, r⟩ := ir
        intro K
        obtain ⟨hNew, hsingle⟩ := single e ge K i r
        obtain ⟨hFinal, htail⟩ := ih ⟨Function.update K.obj i ((K.obj i)⟦r⟧), hNew⟩
        refine ⟨hFinal, ?_⟩
        simp only [treeShiftInputs, treeIntegralShifts, treeSourceShifts, treeOutputShifts,
          Iso.trans_hom, Functor.mapIso_hom, Functor.comp_map]
        rw [← Category.assoc, htail, Category.assoc, ← Functor.map_comp,
          hsingle, Functor.map_comp, Category.assoc]
    exact allLists q K

end WeilConjectures.IntegralSystemRealization
