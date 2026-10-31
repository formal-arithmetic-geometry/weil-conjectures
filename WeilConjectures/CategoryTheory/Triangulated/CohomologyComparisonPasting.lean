/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.TExactTruncationComparison
public import Mathlib.CategoryTheory.Triangulated.TStructure.Heart

/-! # Pasting canonical truncation and cohomology comparisons

Source: BBD, Proposition 1.3.3(i)--(ii), Theorem 1.3.6, printed pp. 29--31.
The transformation, composition and pasting calculations are the agent argument extracted
from the coefficient-stage descent proof, rather than a verbatim BBD theorem
(blueprint: lem-a1-cohomology-comparison-pasting).

Cohomology is written using the existing `truncGELE j j` followed by the j-shift.
All equations are in the ambient category; the heart is a full subcategory.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe uC vC uD vD uB vB uE vE uA vA uZ vZ

namespace CategoryTheory.Triangulated.TStructure

open Limits

variable {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [triC : IsTriangulated C]
  {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [triD : IsTriangulated D]
  {B : Type uB} [Category.{vB} B] [Preadditive B] [HasZeroObject B]
  [HasShift B ℤ] [∀ n : ℤ, (shiftFunctor B n).Additive]
  [Pretriangulated B] [triB : IsTriangulated B]
  {E : Type uE} [Category.{vE} E] [Preadditive E] [HasZeroObject E]
  [HasShift E ℤ] [∀ n : ℤ, (shiftFunctor E n).Additive]
  [Pretriangulated E] [triE : IsTriangulated E]
  {A : Type uA} [Category.{vA} A] [Preadditive A] [HasZeroObject A]
  [HasShift A ℤ] [∀ n : ℤ, (shiftFunctor A n).Additive]
  [Pretriangulated A] [triA : IsTriangulated A]
  {Z : Type uZ} [Category.{vZ} Z] [Preadditive Z] [HasZeroObject Z]
  [HasShift Z ℤ] [∀ n : ℤ, (shiftFunctor Z n).Additive]
  [Pretriangulated Z] [triZ : IsTriangulated Z]

set_option linter.unusedSectionVars false in
/-- The identity preserves both halves at every cutoff. This is the typeclass data
needed to evaluate its canonical comparison, not a new t-exactness predicate.
Proof: the two fields return the given bounds unchanged (agent Step 5).
Source: BBD 1.3.3, agent identity calculation, Step 5
(blueprint: lem-a1-cohomology-comparison-pasting). -/
theorem cohomologyComparison_idTExact (t : TStructure C) : (𝟭 C).IsTExact t t := by
  exact ⟨fun X n h ↦ h, fun X n h ↦ h⟩

set_option linter.unusedSectionVars false in
/-- Composite t-exactness uses successive applications of the existing two fields.
Proof: apply F preservation at n, then H preservation at n, for each half.
Source: BBD 1.3.3, agent composition calculation, Steps 4--5
(blueprint: lem-a1-cohomology-comparison-pasting). -/
theorem cohomologyComparison_compTExact
    (tC : TStructure C) (tD : TStructure D) (tB : TStructure B)
    (F : C ⥤ D) (H : D ⥤ B) [F.IsTExact tC tD] [H.IsTExact tD tB] :
    (F ⋙ H).IsTExact tC tB := by
  constructor
  · intro X n h
    have := Functor.IsTExact.isLE_obj tC tD F X n
    exact Functor.IsTExact.isLE_obj tD tB H (F.obj X) n
  · intro X n h
    have := Functor.IsTExact.isGE_obj tC tD F X n
    exact Functor.IsTExact.isGE_obj tD tB H (F.obj X) n

variable (tC : TStructure C) (tD : TStructure D)
  (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] [hF : F.IsTExact tC tD]

/-- The actual q of the node: first commute F with the j-shift, then shift the
lower comparison at the upper truncation, and finally shift the lower truncation
of the upper comparison. All factors are the recorded canonical isomorphisms.
Source: BBD 1.3.3 and 1.3.6, agent Step 2
(blueprint: lem-a1-cohomology-comparison-pasting). -/
def truncationCohomologyComparison (j : ℤ) :
    (tC.truncGELE j j ⋙ shiftFunctor C j) ⋙ F ≅
      F ⋙ (tD.truncGELE j j ⋙ shiftFunctor D j) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (tC.truncGELE j j) (F.commShiftIso j) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (tC.truncLE j) (F.eTruncGEIso tC tD (j : ℤ)) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (F.eTruncLTIso tC tD (j + 1 : ℤ)) (tD.truncGE j) ≪≫
        Functor.associator _ _ _) (shiftFunctor D j) ≪≫
    Functor.associator _ _ _

omit triC in
private lemma comparison_hom_app (j : ℤ) (K : C) :
    (truncationCohomologyComparison tC tD F j).hom.app K =
      (F.commShiftIso j).hom.app ((tC.truncGELE j j).obj K) ≫
        (shiftFunctor D j).map
          ((F.eTruncGEIso tC tD (j : ℤ)).hom.app ((tC.truncLE j).obj K) ≫
            (tD.truncGE j).map ((F.eTruncLTIso tC tD (j + 1 : ℤ)).hom.app K)) := by
  simp [truncationCohomologyComparison, Functor.map_comp, truncLE]

include triC triD triB in
private lemma truncation_comparison_comp
    (hC : tC.bounded = ⊤) (hD : tD.bounded = ⊤)
    (tB : TStructure B) (hB : tB.bounded = ⊤)
    (H : D ⥤ B) [H.CommShift ℤ] [H.IsTriangulated] [H.IsTExact tD tB]
    (m : ℤ) (K : C) :
    let := cohomologyComparison_compTExact tC tD tB F H
    ((F ⋙ H).eTruncLTIso tC tB (m + 1 : ℤ)).hom.app K =
      H.map ((F.eTruncLTIso tC tD (m + 1 : ℤ)).hom.app K) ≫
        (H.eTruncLTIso tD tB (m + 1 : ℤ)).hom.app (F.obj K) ∧
    ((F ⋙ H).eTruncGEIso tC tB (m : ℤ)).hom.app K =
      H.map ((F.eTruncGEIso tC tD (m : ℤ)).hom.app K) ≫
        (H.eTruncGEIso tD tB (m : ℤ)).hom.app (F.obj K) := by
  let := cohomologyComparison_compTExact tC tD tB F H
  apply (texact_truncation_comparison.{uC, vC, uD, vD, uB, vB}
    tC tD hC hD F m).2.2.2.2.2 B tB hB H
    ((F ⋙ H).eTruncLTIso tC tB (m + 1 : ℤ))
    ((F ⋙ H).eTruncGEIso tC tB (m : ℤ))
  · intro X
    exact (F ⋙ H).eTruncLTIsoApp_hom_eTruncLTι_app tC tB (m + 1 : ℤ) X
  · intro X
    exact (F ⋙ H).eTruncGEπ_app_eTruncGEIsoApp_hom tC tB m X

include triC triD in
/-- The formula defines a natural isomorphism with heart-valued source and target.
Source: BBD 1.3.3, 1.3.5, 1.3.6; agent Steps 1--2
(blueprint: lem-a1-cohomology-comparison-pasting).

Proof: apply lem-weil-heart-short-exact-triangles(1) at the translated cutoff j.
The double truncation has both bounds j, so shifting by j puts it in the heart.
T-exactness preserves the heart. Compose the lower and upper natural truncation
isomorphisms from lem-pod-texact-truncation-comparison, then the specified shift
comparison. Naturality and invertibility of the factors give the asserted natural
isomorphism, and expansion of their components gives precisely the displayed formula. -/
theorem cohomology_comparison_pasting
    (_hC : tC.bounded = ⊤) (_hD : tD.bounded = ⊤) (j : ℤ) (K : C) :
    tC.heart ((tC.truncGELE j j ⋙ shiftFunctor C j).obj K) ∧
    tD.heart (F.obj ((tC.truncGELE j j ⋙ shiftFunctor C j).obj K)) ∧
    tD.heart ((tD.truncGELE j j ⋙ shiftFunctor D j).obj (F.obj K)) ∧
    (truncationCohomologyComparison tC tD F j).hom.app K =
      (F.commShiftIso j).hom.app ((tC.truncGELE j j).obj K) ≫
        (shiftFunctor D j).map
          ((F.eTruncGEIso tC tD (j : ℤ)).hom.app ((tC.truncLE j).obj K) ≫
            (tD.truncGE j).map ((F.eTruncLTIso tC tD (j + 1 : ℤ)).hom.app K)) := by
  have heartC : tC.heart ((tC.truncGELE j j ⋙ shiftFunctor C j).obj K) := by
    apply (tC.mem_heart_iff _).2
    exact ⟨tC.isLE_shift _ j j 0, tC.isGE_shift _ j j 0⟩
  have heartD : tD.heart ((tD.truncGELE j j ⋙ shiftFunctor D j).obj (F.obj K)) := by
    apply (tD.mem_heart_iff _).2
    exact ⟨tD.isLE_shift _ j j 0, tD.isGE_shift _ j j 0⟩
  obtain ⟨hLE, hGE⟩ := (tC.mem_heart_iff _).1 heartC
  refine ⟨heartC, (tD.mem_heart_iff _).2 ⟨?_, ?_⟩, heartD, ?_⟩
  · exact Functor.IsTExact.isLE_obj tC tD F _ 0
  · exact Functor.IsTExact.isGE_obj tC tD F _ 0
  · exact comparison_hom_app tC tD F j K

include triC triD in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Naturality in a shift-compatible transformation; eta need not be invertible.
Source: BBD 1.3.3, agent Step 3
(blueprint: lem-a1-cohomology-comparison-pasting).

Proof: use the transformation clause of lem-pod-texact-truncation-comparison
first for the lower truncation on the upper-truncated object, then for the upper
truncation. Combine by functoriality. Shift the resulting equation and use the
assumed shift compatibility of eta. This also handles any specified shift-compatible
associator, without silently identifying parenthesized functors. -/
theorem truncationCohomologyComparison_naturality
    (_hC : tC.bounded = ⊤) (_hD : tD.bounded = ⊤)
    (G : C ⥤ D) [G.CommShift ℤ] [G.IsTriangulated] [G.IsTExact tC tD]
    (η : F ⟶ G) [NatTrans.CommShift η ℤ] (j : ℤ) (K : C) :
    η.app ((tC.truncGELE j j ⋙ shiftFunctor C j).obj K) ≫
        (truncationCohomologyComparison tC tD G j).hom.app K =
      (truncationCohomologyComparison tC tD F j).hom.app K ≫
        (tD.truncGELE j j ⋙ shiftFunctor D j).map (η.app K) := by
  have hLE := ((texact_truncation_comparison.{uC, vC, uD, vD, uD, vD}
    tC tD _hC _hD F j).2.2.2.1 G η K).1
  have hGE := ((texact_truncation_comparison.{uC, vC, uD, vD, uD, vD}
    tC tD _hC _hD F j).2.2.2.1 G η ((tC.truncLE j).obj K)).2
  have hdouble : η.app ((tC.truncGELE j j).obj K) ≫
      (G.eTruncGEIso tC tD (j : ℤ)).hom.app ((tC.truncLE j).obj K) ≫
      (tD.truncGE j).map ((G.eTruncLTIso tC tD (j + 1 : ℤ)).hom.app K) =
    (F.eTruncGEIso tC tD (j : ℤ)).hom.app ((tC.truncLE j).obj K) ≫
      (tD.truncGE j).map ((F.eTruncLTIso tC tD (j + 1 : ℤ)).hom.app K) ≫
      (tD.truncGELE j j).map (η.app K) := by
    erw [← Category.assoc, hGE, Category.assoc, ← Functor.map_comp, hLE,
      Functor.map_comp, Category.assoc]
  have hs := congrArg ((shiftFunctor D j).map) hdouble
  simp only [Functor.map_comp] at hs
  simp only [truncationCohomologyComparison, Iso.trans_hom, Iso.symm_hom,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.comp_app, Functor.comp_obj, Category.id_comp, Category.comp_id,
    Functor.map_comp, Category.assoc]
  rw [← Category.assoc, ← NatTrans.shift_app_comm η j,
    Category.assoc]
  erw [hs]
  rfl

include triC triD triB in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Comparison for a composite, equipped with the standard composite shift structure.
Source: BBD 1.3.3, agent Steps 4--5
(blueprint: lem-a1-cohomology-comparison-pasting).

Proof: expand the two composite truncation comparisons by
lem-pod-texact-truncation-comparison. Naturality of the lower comparison at the
upper comparison gives the composite law before shifting. Expand the composite
shift structure and use naturality of H's shift comparison at that double-truncation
comparison. This yields q_HF = H(q_F) followed by q_H. -/
theorem truncationCohomologyComparison_comp
    (_hC : tC.bounded = ⊤) (_hD : tD.bounded = ⊤)
    (tB : TStructure B) (_hB : tB.bounded = ⊤)
    (H : D ⥤ B) [H.CommShift ℤ] [H.IsTriangulated] [H.IsTExact tD tB]
    (j : ℤ) (K : C) :
    (truncationCohomologyComparison tC tB (F ⋙ H)
      (hF := cohomologyComparison_compTExact tC tD tB F H) j).hom.app K =
      H.map ((truncationCohomologyComparison tC tD F j).hom.app K) ≫
        (truncationCohomologyComparison tD tB H j).hom.app (F.obj K) := by
  let := cohomologyComparison_compTExact tC tD tB F H
  have hLE := (truncation_comparison_comp tC tD F _hC _hD tB _hB H j K).1
  have hGE := (truncation_comparison_comp tC tD F _hC _hD tB _hB H j
    ((tC.truncLE j).obj K)).2
  have hn := (H.eTruncGEIso tD tB (j : ℤ)).hom.naturality
    ((F.eTruncLTIso tC tD (j + 1 : ℤ)).hom.app K)
  simp only [Functor.comp_map] at hn
  have hdouble :
      ((F ⋙ H).eTruncGEIso tC tB (j : ℤ)).hom.app ((tC.truncLE j).obj K) ≫
        (tB.truncGE j).map (((F ⋙ H).eTruncLTIso tC tB (j + 1 : ℤ)).hom.app K) =
      H.map ((F.eTruncGEIso tC tD (j : ℤ)).hom.app ((tC.truncLE j).obj K) ≫
        (tD.truncGE j).map ((F.eTruncLTIso tC tD (j + 1 : ℤ)).hom.app K)) ≫
      (H.eTruncGEIso tD tB (j : ℤ)).hom.app ((tD.truncLE j).obj (F.obj K)) ≫
        (tB.truncGE j).map ((H.eTruncLTIso tD tB (j + 1 : ℤ)).hom.app (F.obj K)) := by
    rw [hLE, hGE, Functor.map_comp, Category.assoc, ← Category.assoc
      ((H.eTruncGEIso tD tB (j : ℤ)).hom.app _)]
    erw [← hn]
    simp only [Functor.map_comp, Category.assoc]
    rfl
  rw [comparison_hom_app, hdouble]
  simp only [comparison_hom_app, Functor.commShiftIso_comp_hom_app,
    Functor.map_comp, Category.assoc]
  rw [← H.commShiftIso_hom_naturality_assoc]
  rw [← H.commShiftIso_hom_naturality_assoc]
  rfl

include triC in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The identity comparison uses the identity shift structure.
Source: BBD 1.3.3, agent Steps 5 and 8
(blueprint: lem-a1-cohomology-comparison-pasting).

Proof: the unit/counit characterizations in lem-pod-texact-truncation-comparison
make both truncation comparisons identities. The identity shift comparison then
makes their shifted composite the identity as well. -/
theorem truncationCohomologyComparison_id
    (t : TStructure C) (_ht : t.bounded = ⊤) (j : ℤ) (K : C) :
    (truncationCohomologyComparison t t (𝟭 C)
      (hF := cohomologyComparison_idTExact t) j).hom.app K = 𝟙 _ := by
  let := cohomologyComparison_idTExact t
  have hid := (texact_truncation_comparison.{uC, vC, uC, vC, uC, vC}
    t t _ht _ht (𝟭 C) j).2.2.2.2.1
    ((𝟭 C).eTruncLTIso t t (j + 1 : ℤ)) ((𝟭 C).eTruncGEIso t t (j : ℤ))
    (fun X ↦ (𝟭 C).eTruncLTIsoApp_hom_eTruncLTι_app t t (j + 1 : ℤ) X)
    (fun X ↦ (𝟭 C).eTruncGEπ_app_eTruncGEIsoApp_hom t t j X)
  rw [comparison_hom_app, (hid K).1, (hid ((t.truncLE j).obj K)).2]
  simp [truncLE]

include triC triD triB triE in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Both truncation squares and the cohomology square, including successive pasting.
Source: BBD 1.3.3 and 1.3.6, agent Steps 6--8
(blueprint: lem-a1-cohomology-comparison-pasting).

Proof: apply the transformation clause of lem-pod-texact-truncation-comparison
and the cohomology transformation equation to b. Expand the two composite comparisons
to obtain the three displayed squares. For successive squares d and b, naturality of d
at the U-comparison moves that comparison across d. Apply the square for d, then W of
the square for b. Naturality of W's comparison at b combines the right boundary, and
the comparison composition law combines the outer functors. This gives the displayed
pasted square. Repetition handles any finite succession. Identity squares follow by
substituting identity transformations; shift-compatible associators are included by
the transformation equation, so no parenthesized functors are identified silently. -/
theorem truncationCohomologyComparison_square
    (_hC : tC.bounded = ⊤) (_hD : tD.bounded = ⊤)
    (tB : TStructure B) (tE : TStructure E)
    (_hB : tB.bounded = ⊤) (_hE : tE.bounded = ⊤)
    (U : C ⥤ B) (V : D ⥤ E) (F' : B ⥤ E)
    [U.CommShift ℤ] [V.CommShift ℤ] [F'.CommShift ℤ]
    [U.IsTriangulated] [V.IsTriangulated] [F'.IsTriangulated]
    [U.IsTExact tC tB] [V.IsTExact tD tE] [F'.IsTExact tB tE]
    (b : F ⋙ V ≅ U ⋙ F') [NatTrans.CommShift b.hom ℤ]
    (m j : ℤ) (K : C) :
    b.hom.app ((tC.truncLE m).obj K) ≫
        F'.map ((U.eTruncLTIso tC tB (m + 1 : ℤ)).hom.app K) ≫
        (F'.eTruncLTIso tB tE (m + 1 : ℤ)).hom.app (U.obj K) =
      V.map ((F.eTruncLTIso tC tD (m + 1 : ℤ)).hom.app K) ≫
        (V.eTruncLTIso tD tE (m + 1 : ℤ)).hom.app (F.obj K) ≫
        (tE.truncLE m).map (b.hom.app K) ∧
    b.hom.app ((tC.truncGE m).obj K) ≫
        F'.map ((U.eTruncGEIso tC tB (m : ℤ)).hom.app K) ≫
        (F'.eTruncGEIso tB tE (m : ℤ)).hom.app (U.obj K) =
      V.map ((F.eTruncGEIso tC tD (m : ℤ)).hom.app K) ≫
        (V.eTruncGEIso tD tE (m : ℤ)).hom.app (F.obj K) ≫
        (tE.truncGE m).map (b.hom.app K) ∧
    b.hom.app ((tC.truncGELE j j ⋙ shiftFunctor C j).obj K) ≫
        F'.map ((truncationCohomologyComparison tC tB U j).hom.app K) ≫
        (truncationCohomologyComparison tB tE F' j).hom.app (U.obj K) =
      V.map ((truncationCohomologyComparison tC tD F j).hom.app K) ≫
        (truncationCohomologyComparison tD tE V j).hom.app (F.obj K) ≫
        (tE.truncGELE j j ⋙ shiftFunctor E j).map (b.hom.app K) := by
  let := cohomologyComparison_compTExact tC tD tE F V
  let := cohomologyComparison_compTExact tC tB tE U F'
  have hn := (texact_truncation_comparison.{uC, vC, uE, vE, uE, vE}
    tC tE _hC _hE (F ⋙ V) m).2.2.2.1 (U ⋙ F') b.hom K
  have hFV := truncation_comparison_comp tC tD F _hC _hD tE _hE V m K
  have hUF := truncation_comparison_comp tC tB U _hC _hB tE _hE F' m K
  refine ⟨?_, ?_, ?_⟩
  · simpa only [truncLE, hFV.1, hUF.1, Category.assoc] using hn.1
  · simpa only [hFV.2, hUF.2, Category.assoc] using hn.2
  · have hq := truncationCohomologyComparison_naturality tC tE (F ⋙ V)
      _hC _hE (U ⋙ F') b.hom j K
    simpa only [truncationCohomologyComparison_comp tC tD F _hC _hD tE _hE V,
      truncationCohomologyComparison_comp tC tB U _hC _hB tE _hE F',
      Category.assoc] using hq

include triC triD triB triE triA triZ in
/-- Both truncation squares and the cohomology square, including successive pasting.
Source: BBD 1.3.3 and 1.3.6, agent Steps 6--8
(blueprint: lem-a1-cohomology-comparison-pasting).

Proof: apply the transformation clause of lem-pod-texact-truncation-comparison
and the cohomology transformation equation to b. Expand the two composite comparisons
to obtain the three displayed squares. For successive squares d and b, naturality of d
at the U-comparison moves that comparison across d. Apply the square for d, then W of
the square for b. Naturality of W's comparison at b combines the right boundary, and
the comparison composition law combines the outer functors. This gives the displayed
pasted square. Repetition handles any finite succession. Identity squares follow by
substituting identity transformations; shift-compatible associators are included by
the transformation equation, so no parenthesized functors are identified silently. -/
theorem truncationCohomologyComparison_paste
    (_hC : tC.bounded = ⊤) (_hD : tD.bounded = ⊤)
    (tB : TStructure B) (tE : TStructure E)
    (_hB : tB.bounded = ⊤) (_hE : tE.bounded = ⊤)
    (U : C ⥤ B) (V : D ⥤ E) (F' : B ⥤ E)
    [U.CommShift ℤ] [V.CommShift ℤ] [F'.CommShift ℤ]
    [U.IsTriangulated] [V.IsTriangulated] [F'.IsTriangulated]
    [U.IsTExact tC tB] [V.IsTExact tD tE] [F'.IsTExact tB tE]
    (b : F ⋙ V ≅ U ⋙ F') [NatTrans.CommShift b.hom ℤ]
    (tA : TStructure A) (tZ : TStructure Z)
    (_hA : tA.bounded = ⊤) (_hZ : tZ.bounded = ⊤)
    (S : B ⥤ A) (W : E ⥤ Z) (F'' : A ⥤ Z)
    [S.CommShift ℤ] [W.CommShift ℤ] [F''.CommShift ℤ]
    [S.IsTriangulated] [W.IsTriangulated] [F''.IsTriangulated]
    [S.IsTExact tB tA] [W.IsTExact tE tZ] [F''.IsTExact tA tZ]
    (d : F' ⋙ W ≅ S ⋙ F'') [NatTrans.CommShift d.hom ℤ]
    (m j : ℤ) (K : C) :
    W.map (b.hom.app ((tC.truncLE m).obj K)) ≫
        d.hom.app (U.obj ((tC.truncLE m).obj K)) ≫
        F''.map (S.map ((U.eTruncLTIso tC tB (m + 1 : ℤ)).hom.app K)) ≫
        F''.map ((S.eTruncLTIso tB tA (m + 1 : ℤ)).hom.app (U.obj K)) ≫
        (F''.eTruncLTIso tA tZ (m + 1 : ℤ)).hom.app (S.obj (U.obj K)) =
      W.map (V.map ((F.eTruncLTIso tC tD (m + 1 : ℤ)).hom.app K)) ≫
        W.map ((V.eTruncLTIso tD tE (m + 1 : ℤ)).hom.app (F.obj K)) ≫
        (W.eTruncLTIso tE tZ (m + 1 : ℤ)).hom.app (V.obj (F.obj K)) ≫
        (tZ.truncLE m).map (W.map (b.hom.app K) ≫ d.hom.app (U.obj K)) ∧
    W.map (b.hom.app ((tC.truncGE m).obj K)) ≫
        d.hom.app (U.obj ((tC.truncGE m).obj K)) ≫
        F''.map (S.map ((U.eTruncGEIso tC tB (m : ℤ)).hom.app K)) ≫
        F''.map ((S.eTruncGEIso tB tA (m : ℤ)).hom.app (U.obj K)) ≫
        (F''.eTruncGEIso tA tZ (m : ℤ)).hom.app (S.obj (U.obj K)) =
      W.map (V.map ((F.eTruncGEIso tC tD (m : ℤ)).hom.app K)) ≫
        W.map ((V.eTruncGEIso tD tE (m : ℤ)).hom.app (F.obj K)) ≫
        (W.eTruncGEIso tE tZ (m : ℤ)).hom.app (V.obj (F.obj K)) ≫
        (tZ.truncGE m).map (W.map (b.hom.app K) ≫ d.hom.app (U.obj K)) ∧
    W.map (b.hom.app ((tC.truncGELE j j ⋙ shiftFunctor C j).obj K)) ≫
        d.hom.app (U.obj ((tC.truncGELE j j ⋙ shiftFunctor C j).obj K)) ≫
        F''.map (S.map ((truncationCohomologyComparison tC tB U j).hom.app K)) ≫
        F''.map ((truncationCohomologyComparison tB tA S j).hom.app (U.obj K)) ≫
        (truncationCohomologyComparison tA tZ F'' j).hom.app (S.obj (U.obj K)) =
      W.map (V.map ((truncationCohomologyComparison tC tD F j).hom.app K)) ≫
        W.map ((truncationCohomologyComparison tD tE V j).hom.app (F.obj K)) ≫
        (truncationCohomologyComparison tE tZ W j).hom.app (V.obj (F.obj K)) ≫
        (tZ.truncGELE j j ⋙ shiftFunctor Z j).map (W.map (b.hom.app K) ≫ d.hom.app (U.obj K)) := by
  let := cohomologyComparison_compTExact tC tB tA U S
  let := cohomologyComparison_compTExact tD tE tZ V W
  let e : F ⋙ (V ⋙ W) ≅ (U ⋙ S) ⋙ F'' :=
    (Functor.associator F V W).symm ≪≫ Functor.isoWhiskerRight b W ≪≫
      Functor.associator U F' W ≪≫ Functor.isoWhiskerLeft U d ≪≫
      (Functor.associator U S F'').symm
  have : NatTrans.CommShift e.hom ℤ := by
    dsimp [e]
    infer_instance
  have he := truncationCohomologyComparison_square tC tD F _hC _hD tA tZ
    _hA _hZ (U ⋙ S) (V ⋙ W) F'' e m j K
  have hUS := truncation_comparison_comp tC tB U _hC _hB tA _hA S m K
  have hVW := truncation_comparison_comp tD tE V _hD _hE tZ _hZ W m (F.obj K)
  simpa only [e, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_obj, Functor.comp_map, Category.id_comp, Category.comp_id,
    hUS.1, hUS.2, hVW.1, hVW.2,
    truncationCohomologyComparison_comp tC tB U _hC _hB tA _hA S,
    truncationCohomologyComparison_comp tD tE V _hD _hE tZ _hZ W,
    Functor.map_comp, Category.assoc] using he

include triC triD in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Vertical pasting of comparison squares, also for noninvertible transformations.
Source: BBD 1.3.3, agent Step 8
(blueprint: lem-a1-cohomology-comparison-pasting).

Proof: use the transformation equation twice, first for eta and then for theta;
functoriality combines their images. Identity transformations give identity squares.
Together with the preceding horizontal pasting equation this gives successive pasting,
and applies to any specified shift-compatible associators as well. -/
theorem truncationCohomologyComparison_vertical
    (_hC : tC.bounded = ⊤) (_hD : tD.bounded = ⊤)
    (G L : C ⥤ D) [G.CommShift ℤ] [L.CommShift ℤ]
    [G.IsTriangulated] [L.IsTriangulated] [G.IsTExact tC tD] [L.IsTExact tC tD]
    (η : F ⟶ G) (θ : G ⟶ L) [NatTrans.CommShift η ℤ] [NatTrans.CommShift θ ℤ]
    (m j : ℤ) (K : C) :
    η.app ((tC.truncLE m).obj K) ≫ θ.app ((tC.truncLE m).obj K) ≫
        (L.eTruncLTIso tC tD (m + 1 : ℤ)).hom.app K =
      (F.eTruncLTIso tC tD (m + 1 : ℤ)).hom.app K ≫
        (tD.truncLE m).map (η.app K ≫ θ.app K) ∧
    η.app ((tC.truncGE m).obj K) ≫ θ.app ((tC.truncGE m).obj K) ≫
        (L.eTruncGEIso tC tD (m : ℤ)).hom.app K =
      (F.eTruncGEIso tC tD (m : ℤ)).hom.app K ≫
        (tD.truncGE m).map (η.app K ≫ θ.app K) ∧
    η.app ((tC.truncGELE j j ⋙ shiftFunctor C j).obj K) ≫
        θ.app ((tC.truncGELE j j ⋙ shiftFunctor C j).obj K) ≫
        (truncationCohomologyComparison tC tD L j).hom.app K =
      (truncationCohomologyComparison tC tD F j).hom.app K ≫
        (tD.truncGELE j j ⋙ shiftFunctor D j).map (η.app K ≫ θ.app K) := by
  have hn := (texact_truncation_comparison.{uC, vC, uD, vD, uD, vD}
    tC tD _hC _hD F m).2.2.2.1 L (η ≫ θ) K
  refine ⟨?_, ?_, ?_⟩
  · simpa only [truncLE, NatTrans.comp_app, Category.assoc] using hn.1
  · simpa only [NatTrans.comp_app, Category.assoc] using hn.2
  · simpa only [NatTrans.comp_app, Category.assoc] using
      truncationCohomologyComparison_naturality tC tD F _hC _hD L (η ≫ θ) j K

end CategoryTheory.Triangulated.TStructure
