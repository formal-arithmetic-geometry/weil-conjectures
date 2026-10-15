/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.Paper.ProfinitePointPullback
public import Sheaf.Paper.PointLanAffineEvaluation
import Sheaf.Paper.ProEtaleSheafificationWcontractibleSections

/-!
# The point-pullback formula on the weakly contractible affine basis

Source: Bhatt–Scholze, Lemma 4.2.13(1); Hemo–Richarz–Scholbach, Example 3.1;
RefactorInstruction, Section 4, Lemma point-eval
(blueprint: lem-weil-pbc-condensed-point-basis-evaluation).
-/

@[expose] public section

universe u v w

open CategoryTheory Opposite

namespace AlgebraicGeometry.ProEtale

/-- The commutative-ring inverse image is the geometric inverse image `π_X⁻¹ a*`,
constructed by left Kan extension and sheafification in commutative rings.
Source: RefactorInstruction, Section 4, prop:pX and Lemma point-eval
(blueprint: lem-weil-pbc-condensed-point-basis-evaluation). -/
noncomputable abbrev pointBasisRingInverseImage (X : Scheme.{u}) :=
  Functor.sheafPullbackConstruction.sheafPullback profiniteToProEt CommRingCat.{u + 1}
    (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ) ⋙
      Scheme.proEtaleSheafInverseImage (toSpecZ X) CommRingCat.{u + 1}

/-- The evaluation formula, simultaneously natural in the coefficient sheaf and in
morphisms of weakly contractible affine objects. Isomorphisms are taken in `C`, so
in the algebraic coefficient categories they preserve the corresponding operations.
`pointLanComponents` is the actual connected-component quotient, not a chosen space.
Source: RefactorInstruction, Section 4, Lemma point-eval
(blueprint: lem-weil-pbc-condensed-point-basis-evaluation). -/
def PointBasisEvaluationProperty (X : Scheme.{u}) (C : Type w) [Category.{v} C]
    (L : Sheaf (coherentTopology Profinite.{u}) C ⥤
      Sheaf (Scheme.ProEt.topology X) C) : Prop :=
  ∃ e : ∀ (F : Sheaf (coherentTopology Profinite.{u}) C)
      (U : X.ProEt) (hU : IsAffine U.left) (wU : PointLanWeaklyContractible X U),
      (L.obj F).obj.obj (op U) ≅ F.obj.obj (op (pointLanComponents X U hU wU)),
    (∀ (F G : Sheaf (coherentTopology Profinite.{u}) C) (α : F ⟶ G)
      (U : X.ProEt) (hU : IsAffine U.left) (wU : PointLanWeaklyContractible X U),
      (L.map α).hom.app (op U) ≫ (e G U hU wU).hom =
        (e F U hU wU).hom ≫ α.hom.app (op (pointLanComponents X U hU wU))) ∧
    (∀ (F : Sheaf (coherentTopology Profinite.{u}) C)
      (U V : X.ProEt) (hU : IsAffine U.left) (hV : IsAffine V.left)
      (wU : PointLanWeaklyContractible X U) (wV : PointLanWeaklyContractible X V)
      (a : V ⟶ U),
      (L.obj F).obj.map a.op ≫ (e F V hV wV).hom =
        (e F U hU wU).hom ≫ F.obj.map
          (ConcreteCategory.ofHom
            ⟨a.left.continuous.connectedComponentsMap,
              a.left.continuous.connectedComponentsMap_continuous⟩ :
            pointLanComponents X V hV wV ⟶ pointLanComponents X U hU wU).op)

private lemma pointBasis_of_relative (X : Scheme.{u}) (C : Type w)
    [Category.{u + 1} C] [Limits.HasColimitsOfSize.{u + 1, u + 1} C]
    [HasWeakSheafify (Scheme.ProEt.topology X) C]
    (hl : PointLanAffineEvaluationProperty X C)
    (hs : PointLanSheafificationProperty X C) :
    PointBasisEvaluationProperty X C
      (Functor.sheafPullbackConstruction.sheafPullback (profiniteToProEtOf X) C
        (coherentTopology Profinite.{u}) (Scheme.ProEt.topology X)) := by
  unfold PointBasisEvaluationProperty
  dsimp only [Functor.sheafPullbackConstruction.sheafPullback, Functor.comp_obj,
    Functor.comp_map, sheafToPresheaf, ObjectProperty.ι_obj, ObjectProperty.ι_map]
  rcases hl with ⟨_, _, _, ⟨e, _, hen⟩, _⟩
  let G := (profiniteToProEtOf X).op
  let P (F : Sheaf (coherentTopology Profinite.{u}) C) := G.lan.obj F.obj
  let η (F : Sheaf (coherentTopology Profinite.{u}) C) := G.leftKanExtensionUnit F.obj
  let hP (F : Sheaf (coherentTopology Profinite.{u}) C) :=
    Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit G F.obj
  have hi (F : Sheaf (coherentTopology Profinite.{u}) C)
      (U : X.ProEt) (hU : IsAffine U.left) (wU : PointLanWeaklyContractible X U) :
      IsIso ((toSheafify (Scheme.ProEt.topology X) (P F)).app (op U)) :=
    (hs F (P F) (η F) (hP F) U hU wU).1
  let d (F : Sheaf (coherentTopology Profinite.{u}) C)
      (U : X.ProEt) (hU : IsAffine U.left) (wU : PointLanWeaklyContractible X U) :=
    letI := hi F U hU wU
    (asIso ((toSheafify (Scheme.ProEt.topology X) (P F)).app (op U))).symm ≪≫
      e F (P F) (η F) (hP F) U hU wU
  refine ⟨d, ?_, ?_⟩
  · intro F H α U hU wU
    let := hi F U hU wU
    let := hi H U hU wU
    let β := G.lan.map α.hom
    have hβ : η F ≫ Functor.whiskerLeft G β = α.hom ≫ η H :=
      (G.lanUnit.naturality α.hom).symm
    have hn := hen F H (P F) (P H) (η F) (η H) (hP F) (hP H) α β hβ
      U U hU hU wU wU (𝟙 U)
    have hu := (hs F (P F) (η F) (hP F) U hU wU).2.2
      H (P H) (η H) (hP H) α β hβ
    have hc : (ConcreteCategory.ofHom
        ⟨(𝟙 U : U ⟶ U).left.continuous.connectedComponentsMap,
          (𝟙 U : U ⟶ U).left.continuous.connectedComponentsMap_continuous⟩ :
        pointLanComponents X U hU wU ⟶ pointLanComponents X U hU wU) = 𝟙 _ := by
      ext x
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe x
      rfl
    simp only [op_id, hc] at hn
    rw [(P F).map_id, F.obj.map_id] at hn
    simp only [Category.id_comp] at hn
    dsimp [d]
    change (sheafifyMap (Scheme.ProEt.topology X) β).app (op U) ≫
        inv ((toSheafify (Scheme.ProEt.topology X) (P H)).app (op U)) ≫
        (e H (P H) (η H) (hP H) U hU wU).hom = _
    apply (cancel_epi ((toSheafify (Scheme.ProEt.topology X) (P F)).app (op U))).1
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    rw [← reassoc_of% hu]
    simpa only [Category.assoc, IsIso.hom_inv_id_assoc, Category.comp_id] using hn
  · intro F U V hU hV wU wV a
    let := hi F U hU wU
    let := hi F V hV wV
    have hn := hen F F (P F) (P F) (η F) (η F) (hP F) (hP F)
      (𝟙 F) (𝟙 (P F)) (by simp) U V hU hV wU wV a
    change (P F).map a.op ≫ 𝟙 _ ≫ _ = _ ≫ _ ≫ 𝟙 _ at hn
    simp only [Category.id_comp, Category.comp_id] at hn
    have hu := (hs F (P F) (η F) (hP F) U hU wU).2.1 V hV wV a
    dsimp [d]
    apply (cancel_epi ((toSheafify (Scheme.ProEt.topology X) (P F)).app (op U))).1
    change (toSheafify (Scheme.ProEt.topology X) (P F)).app (op U) ≫
        (sheafify (Scheme.ProEt.topology X) (P F)).map a.op ≫ _ = _
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    rw [← reassoc_of% hu]
    simpa only [Category.assoc, IsIso.hom_inv_id_assoc] using hn

private lemma pointBasis_of_iso (X : Scheme.{u}) (C : Type w) [Category.{v} C]
    {L M : Sheaf (coherentTopology Profinite.{u}) C ⥤
      Sheaf (Scheme.ProEt.topology X) C}
    (i : L ≅ M) (h : PointBasisEvaluationProperty X C M) :
    PointBasisEvaluationProperty X C L := by
  rcases h with ⟨e, hF, hA⟩
  let d (F : Sheaf (coherentTopology Profinite.{u}) C)
      (U : X.ProEt) (hU : IsAffine U.left) (wU : PointLanWeaklyContractible X U) :=
    ((sheafToPresheaf (Scheme.ProEt.topology X) C).mapIso (i.app F)).app (op U) ≪≫
      e F U hU wU
  refine ⟨d, ?_, ?_⟩
  · intro F G α U hU wU
    have hn := congrArg (fun f ↦ f.hom.app (op U)) (i.hom.naturality α)
    dsimp at hn
    dsimp [d]
    change (L.map α).hom.app (op U) ≫ (i.hom.app G).hom.app (op U) ≫ _ = _
    rw [← Category.assoc, hn, Category.assoc, hF, Category.assoc]
  · intro F U V hU hV wU wV a
    have hn := (i.hom.app F).hom.naturality a.op
    dsimp [d]
    change (L.obj F).obj.map a.op ≫ (i.hom.app F).hom.app (op V) ≫ _ = _
    rw [← Category.assoc, hn, Category.assoc, hA F U V hU hV wU wV a, Category.assoc]

private lemma pointBasis_of_composite (X : Scheme.{u}) (C : Type w)
    [Category.{u + 1} C] [Limits.HasColimitsOfSize.{u + 1, u + 1} C]
    [HasWeakSheafify (Scheme.ProEt.topology specZ.{u}) C]
    [HasWeakSheafify (Scheme.ProEt.topology X) C]
    (hl : PointLanAffineEvaluationProperty X C)
    (hs : PointLanSheafificationProperty X C) :
    PointBasisEvaluationProperty X C
      (Functor.sheafPullbackConstruction.sheafPullback profiniteToProEt C
        (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ) ⋙
          Scheme.proEtaleSheafInverseImage (toSpecZ X) C) := by
  let : (profiniteToProEtOf X).IsContinuous (coherentTopology Profinite.{u})
      (Scheme.ProEt.topology X) :=
    Functor.isContinuous_comp profiniteToProEt (Scheme.proEtaleBaseChange (toSpecZ X))
      (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ)
      (Scheme.ProEt.topology X)
  let adj :=
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous profiniteToProEt C
      (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ)).comp
        (Scheme.proEtaleSheafAdjunction (toSpecZ X) C)
  let adj' := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (profiniteToProEtOf X) C (coherentTopology Profinite.{u}) (Scheme.ProEt.topology X)
  exact pointBasis_of_iso X C (adj.leftAdjointUniq adj')
    (pointBasis_of_relative X C hl hs)

/-- The geometric inverse image of a condensed set, abelian group, or commutative ring
on a weakly contractible affine is its value on the profinite component quotient.
The identifications are natural in both variables and preserve the algebraic operations.
The final clause records the quotient topology explicitly.

Source: Bhatt–Scholze, Lemma 4.2.13(1), inverse-image computation;
Hemo–Richarz–Scholbach, Example 3.1; RefactorInstruction, Section 4, Lemma point-eval
(blueprint: lem-weil-pbc-condensed-point-basis-evaluation).

Proof for stage 3:
1. Apply lem-weil-pbc-proetale-point-components-maps to obtain the profinite quotient
   and the natural bijection Hom_X(U,X[S]) = C(pi_0(U),S).
2. The left Kan extension is evaluation at this quotient: the identity of pi_0(U)
   gives a terminal object of the Kan indexing category. This is the computation in
   lem-weil-pbc-point-lan-affine-evaluation. Identify the relative inverse image with
   π_X⁻¹ a* using the inverse-image composition comparison of
   lem-weil-pbc-profinite-point-pullback.
3. By lem-weil-pbc-proetale-sheafification-wcontractible-sections, the sheafification
   unit on U is invertible. Compose its inverse with the Kan evaluation isomorphism.
   Naturality of the Kan comparison and the unit gives both naturality equations.
4. The same construction in abelian groups and commutative rings is an isomorphism
   in that category, so it preserves addition and multiplication when present.
   The topology of ConnectedComponents is the quotient topology by definition. -/
theorem condensed_point_basis_evaluation (X : Scheme.{u}) :
    PointBasisEvaluationProperty X (Type (u + 1))
      (profinitePointSetSchemeInverseImage X) ∧
    PointBasisEvaluationProperty X AddCommGrpCat.{u + 1} (upperStarFromPoint X) ∧
    PointBasisEvaluationProperty X CommRingCat.{u + 1} (pointBasisRingInverseImage X) ∧
    (∀ (U : X.ProEt) (hU : IsAffine U.left) (wU : PointLanWeaklyContractible X U),
      CompactSpace (pointLanComponents X U hU wU) ∧
      T2Space (pointLanComponents X U hU wU) ∧
      TotallyDisconnectedSpace (pointLanComponents X U hU wU) ∧
      ∀ s : Set (ConnectedComponents U.left),
        IsOpen s ↔ IsOpen (ConnectedComponents.mk ⁻¹' s)) := by
  have hl := point_lan_affine_evaluation X
  have hs := proEtale_sheafification_wcontractible_sections X
  have hset : PointBasisEvaluationProperty X (Type (u + 1))
      (profinitePointSetSchemeInverseImage X) :=
    pointBasis_of_composite X (Type (u + 1)) hl.1 hs.1
  have hab : PointBasisEvaluationProperty X AddCommGrpCat.{u + 1}
      (upperStarFromPoint X) := by
    exact pointBasis_of_composite X AddCommGrpCat.{u + 1} hl.2.1 hs.2.1
  have hring : PointBasisEvaluationProperty X CommRingCat.{u + 1}
      (pointBasisRingInverseImage X) :=
    pointBasis_of_composite X CommRingCat.{u + 1} hl.2.2 hs.2.2
  refine ⟨hset, hab, hring, ?_⟩
  intro U hU wU
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  intro s
  exact ConnectedComponents.isQuotientMap_coe.isCoinducing.isOpen_preimage

end AlgebraicGeometry.ProEtale
