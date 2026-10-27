/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
public import Sheaf.CategoryTheory.Triangulated.TExactTruncationComparison

/-! # A t-exact functor preserves cohomology boundaries

Source: BBD, Proposition 1.3.3, Theorem 1.3.6 and §1.3.16, printed pp. 29–31, 36–37.
The boundary comparison is the formal consequence of these constructions recorded in the DAG
(blueprint: lem-zl-texact-cohomology-boundary-comparison).

The heart restriction is a full-subcategory lift. The degree-zero comparison is the composite
of the canonical lower and upper truncation comparisons, lifted through the full heart.
The degree-r comparison then uses the specified coherent shift comparison. Boundaries are
Mathlib's `homologySequenceδ`, with the tautological shift sequence on the existing `homology₀`.
-/

@[expose] public section

set_option autoImplicit false

universe uC vC uD vD

namespace CategoryTheory.Triangulated.TStructure

open Limits Pretriangulated

variable {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]
  {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [IsTriangulated D]
  (tC : TStructure C) (tD : TStructure D)
  (P : C ⥤ D) [P.CommShift ℤ] [P.IsTriangulated] [P.IsTExact tC tD]

/-- Restriction of a t-exact functor to the full hearts, with the original underlying maps.
Source: BBD §1.3.16 (blueprint: lem-zl-texact-cohomology-boundary-comparison). -/
def texactHeartRestriction : tC.heart.FullSubcategory ⥤ tD.heart.FullSubcategory :=
  tD.heart.lift (tC.heart.ι ⋙ P) (fun X ↦
    have : tC.IsLE X.obj 0 := ⟨X.property.1⟩
    have : tC.IsGE X.obj 0 := ⟨X.property.2⟩
    (tD.mem_heart_iff (P.obj X.obj)).2
      ⟨Functor.IsTExact.isLE_obj tC tD P X.obj 0,
        Functor.IsTExact.isGE_obj tC tD P X.obj 0⟩)

/-- The natural comparison `P♥ H⁰ ≅ H⁰ P`, constructed from `α⁺` on `τ≤0` followed by
`τ≥0(α⁻)`. Full faithfulness of the heart inclusion lifts this actual composite.
Source: BBD 1.3.3 and 1.3.16 (blueprint: lem-zl-texact-cohomology-boundary-comparison). -/
noncomputable def texactHomologyZeroComparison :
    tC.homology₀ ⋙ texactHeartRestriction tC tD P ≅ P ⋙ tD.homology₀ :=
  Functor.fullyFaithfulCancelRight tD.heart.ι
    (Functor.associator (tC.truncLE 0) (tC.truncGE 0) P ≪≫
      Functor.isoWhiskerLeft (tC.truncLE 0) (P.eTruncGEIso tC tD (0 : ℤ)) ≪≫
      (Functor.associator (tC.truncLE 0) P (tD.truncGE 0)).symm ≪≫
      Functor.isoWhiskerRight (P.eTruncLTIso tC tD (1 : ℤ)) (tD.truncGE 0) ≪≫
      Functor.associator P (tD.truncLE 0) (tD.truncGE 0))

/-- The canonical degree-r comparison: apply the degree-zero comparison to `M[r]`, then
apply `H⁰` to the specified shift comparison `P(M[r]) ≅ (PM)[r]`.
Source: BBD 1.3.6 and 1.3.16 (blueprint: lem-zl-texact-cohomology-boundary-comparison). -/
noncomputable def texactCohomologyComparison (r : ℤ) :
    (shiftFunctor C r ⋙ tC.homology₀) ⋙ texactHeartRestriction tC tD P ≅
      P ⋙ (shiftFunctor D r ⋙ tD.homology₀) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (shiftFunctor C r) (texactHomologyZeroComparison tC tD P) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (P.commShiftIso r) tD.homology₀ ≪≫
    Functor.associator _ _ _

/-- The standard heart-valued boundary, using `H^r = H⁰(-[r])` and the shift associator.
This is the existing `homologySequenceδ` with its tautological shift sequence, so it has
no extra rotation sign. Source: BBD 1.3.6 and Mathlib `Functor.homologySequenceδ`
(blueprint: lem-zl-texact-cohomology-boundary-comparison). -/
noncomputable def heartCohomologyBoundary (t : TStructure C) (T : Triangle C) (r : ℤ) :
    (shiftFunctor C r ⋙ t.homology₀).obj T.obj₃ ⟶
      (shiftFunctor C (r + 1) ⋙ t.homology₀).obj T.obj₁ :=
  letI : t.homology₀.ShiftSequence ℤ := Functor.ShiftSequence.tautological t.homology₀ ℤ
  t.homology₀.homologySequenceδ T r (r + 1) rfl

/-- The canonical cohomology comparison intertwines standard boundaries of a distinguished
triangle and its image, whose last arrow is `P(w) ≫ σ(A,1)`.
Source: BBD 1.3.3, 1.3.6, 1.3.16; formal consequence extracted in the DAG
(blueprint: lem-zl-texact-cohomology-boundary-comparison).

Proof: (1) Restrict P to the heart using preservation of both halves. Compose the canonical
truncation comparisons from lem-pod-texact-truncation-comparison at zero to obtain e.
(2) Naturality of both truncation comparisons gives naturality of e. (3) Evaluate e on M[r]
and compose with H⁰(σ(M,r)) to obtain the natural isomorphism c^r. (4) For the shifted third
arrow w_r, coherence of σ with addition and naturality at w give
P(w_r) ≫ σ(A,r+1) = σ(C,r) ≫ (Pw)_r. Exactness makes the image triangle distinguished.
(5) Apply naturality of e to w_r. The two boundaries are H⁰(w_r) and H⁰((Pw)_r), so the
coherence equation gives P♥(δ_T) ≫ c_A = c_C ≫ δ_PT. This argument works for every integer r,
without rotating the triangle or introducing a sign. Step (6), naturality in triangle
morphisms, is stated separately below. -/
theorem texact_cohomology_boundary_comparison
    (_hC : tC.bounded = ⊤) (_hD : tD.bounded = ⊤)
    (T : Triangle C) (_hT : T ∈ distTriang C) (r : ℤ) :
    (texactHeartRestriction tC tD P).map (heartCohomologyBoundary tC T r) ≫
        (texactCohomologyComparison tC tD P (r + 1)).hom.app T.obj₁ =
      (texactCohomologyComparison tC tD P r).hom.app T.obj₃ ≫
        heartCohomologyBoundary tD (P.mapTriangle.obj T) r := by
  have hadd : (1 : ℤ) + r = r + 1 := add_comm 1 r
  have hσ :
      P.map ((shiftFunctor C r).map T.mor₃ ≫
          (shiftFunctorAdd' C 1 r (r + 1) hadd).inv.app T.obj₁) ≫
        (P.commShiftIso (r + 1)).hom.app T.obj₁ =
      (P.commShiftIso r).hom.app T.obj₃ ≫
        (shiftFunctor D r).map (P.map T.mor₃ ≫ (P.commShiftIso 1).hom.app T.obj₁) ≫
          (shiftFunctorAdd' D 1 r (r + 1) hadd).inv.app (P.obj T.obj₁) := by
    rw [P.commShiftIso_add' hadd]
    simp only [Functor.CommShift.isoAdd'_hom_app, P.map_comp, Category.assoc]
    simp only [← P.map_comp_assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id, P.commShiftIso_hom_naturality_assoc]
    simp only [Functor.map_comp, Category.assoc]
  simp only [texactCohomologyComparison, Iso.trans_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.id_comp,
    Category.comp_id]
  simp only [heartCohomologyBoundary, Functor.homologySequenceδ, Functor.shiftMap,
    Functor.shift, Functor.shiftIso, Functor.ShiftSequence.tautological,
    Iso.trans_hom, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Iso.symm_hom,
    Category.id_comp]
  dsimp only [Functor.ShiftSequence.sequence, Functor.ShiftSequence.shiftIso]
  simp only [Category.id_comp]
  change (texactHeartRestriction tC tD P).map
      (tC.homology₀.map ((shiftFunctor C r).map T.mor₃) ≫
        tC.homology₀.map ((shiftFunctorAdd' C 1 r (r + 1) hadd).inv.app T.obj₁)) ≫
      ((texactHomologyZeroComparison tC tD P).hom.app _ ≫
        tD.homology₀.map ((P.commShiftIso (r + 1)).hom.app T.obj₁)) =
    ((texactHomologyZeroComparison tC tD P).hom.app _ ≫
      tD.homology₀.map ((P.commShiftIso r).hom.app T.obj₃)) ≫
      (tD.homology₀.map ((shiftFunctor D r).map
        (P.map T.mor₃ ≫ (P.commShiftIso 1).hom.app T.obj₁)) ≫
        tD.homology₀.map ((shiftFunctorAdd' D 1 r (r + 1) hadd).inv.app _))
  rw [← tC.homology₀.map_comp]
  erw [← Category.assoc, (texactHomologyZeroComparison tC tD P).hom.naturality]
  dsimp only [Functor.comp_map]
  simp only [Category.assoc, ← tD.homology₀.map_comp, hσ]

/-- Naturality of the boundary comparison square in a morphism of distinguished triangles:
the two boundary faces and the comparison faces on the first and third terms commute.
Source: BBD 1.1.1, 1.3.6, 1.3.16; formal consequence extracted in the DAG
(blueprint: lem-zl-texact-cohomology-boundary-comparison).

Proof, step (6) of the node: shift the third-arrow equation of the triangle morphism and use
naturality of the shift associator. Applying H⁰ gives the first boundary face. Apply P to the
triangle morphism and use naturality of σ(-,1) for its third-arrow equation; the same argument
in D gives the second boundary face. Naturality of c from steps (2)–(3) gives the remaining
faces at the first and third components. Together with step (5), these are the naturality
cube of the comparison squares. -/
theorem texact_cohomology_boundary_comparison_naturality
    (_hC : tC.bounded = ⊤) (_hD : tD.bounded = ⊤)
    (T T' : Triangle C) (_hT : T ∈ distTriang C) (_hT' : T' ∈ distTriang C)
    (φ : T ⟶ T') (r : ℤ) :
    (shiftFunctor C r ⋙ tC.homology₀).map φ.hom₃ ≫
        heartCohomologyBoundary tC T' r =
      heartCohomologyBoundary tC T r ≫
        (shiftFunctor C (r + 1) ⋙ tC.homology₀).map φ.hom₁ ∧
    (shiftFunctor D r ⋙ tD.homology₀).map (P.map φ.hom₃) ≫
        heartCohomologyBoundary tD (P.mapTriangle.obj T') r =
      heartCohomologyBoundary tD (P.mapTriangle.obj T) r ≫
        (shiftFunctor D (r + 1) ⋙ tD.homology₀).map (P.map φ.hom₁) ∧
    (texactHeartRestriction tC tD P).map
        ((shiftFunctor C (r + 1) ⋙ tC.homology₀).map φ.hom₁) ≫
        (texactCohomologyComparison tC tD P (r + 1)).hom.app T'.obj₁ =
      (texactCohomologyComparison tC tD P (r + 1)).hom.app T.obj₁ ≫
        (shiftFunctor D (r + 1) ⋙ tD.homology₀).map (P.map φ.hom₁) ∧
    (texactHeartRestriction tC tD P).map
        ((shiftFunctor C r ⋙ tC.homology₀).map φ.hom₃) ≫
        (texactCohomologyComparison tC tD P r).hom.app T'.obj₃ =
      (texactCohomologyComparison tC tD P r).hom.app T.obj₃ ≫
        (shiftFunctor D r ⋙ tD.homology₀).map (P.map φ.hom₃) := by
  let : tC.homology₀.ShiftSequence ℤ :=
    Functor.ShiftSequence.tautological tC.homology₀ ℤ
  let : tD.homology₀.ShiftSequence ℤ :=
    Functor.ShiftSequence.tautological tD.homology₀ ℤ
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact tC.homology₀.homologySequenceδ_naturality T T' φ r (r + 1) rfl
  · exact tD.homology₀.homologySequenceδ_naturality _ _ (P.mapTriangle.map φ)
      r (r + 1) rfl
  · exact (texactCohomologyComparison tC tD P (r + 1)).hom.naturality φ.hom₁
  · exact (texactCohomologyComparison tC tD P r).hom.naturality φ.hom₃

end CategoryTheory.Triangulated.TStructure
