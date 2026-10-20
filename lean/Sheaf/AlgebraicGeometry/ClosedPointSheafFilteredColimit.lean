/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FinitelyGeneratedEtaleSubsheaf
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Filtered.Basic
public import Sheaf.AlgebraicGeometry.EtaleSupport
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.CategoryTheory.Subobject.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Subobject.Lattice

/-! Filtered presentation by finitely generated étale subsheaves.
Source: Stacks Project, Tag 0F0N; blueprint (blueprint: lem-kun-cp-filtered-colimit).
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private instance sheafGrothendieck (X : Scheme.{v}) :
    IsGrothendieckAbelian.{v + 1}
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}) :=
  GrothendieckTopology.isGrothendieckAbelian_sheaf_smallEtaleTopology _ X

private instance sheafHasColimits (X : Scheme.{v}) :
    HasColimitsOfSize.{v + 1, v + 1}
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}) :=
  IsGrothendieckAbelian.hasColimits _

private noncomputable def sectionEquiv {X : Scheme.{v}} (U : X.Etale)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}) :
    ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}).obj
      (uliftYoneda.{v + 1}.obj U ⋙ AddCommGrpCat.free) ⟶ F) ≃ F.obj.obj (op U) :=
  ((sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{v + 1}).homEquiv _ _).trans
    ((AddCommGrpCat.adj.whiskerRight X.Etaleᵒᵖ).homEquiv _ _ |>.trans uliftYonedaEquiv)

private theorem sectionEquiv_comp {X : Scheme.{v}} (U : X.Etale)
    {F H : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}}
    (p : (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}).obj
      (uliftYoneda.{v + 1}.obj U ⋙ AddCommGrpCat.free) ⟶ F) (f : F ⟶ H) :
    sectionEquiv U H (p ≫ f) = f.hom.app (op U) (sectionEquiv U F p) := by
  simp only [sectionEquiv, Equiv.trans_apply, Adjunction.homEquiv_naturality_right]
  rfl

private theorem section_lifts_iff {X : Scheme.{v}}
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}}
    (G : Subobject F) (U : X.Etale) (s : F.obj.obj (op U)) :
    (∃ t : (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}).obj.obj (op U),
      G.arrow.hom.app (op U) t = s) ↔ G.Factors ((sectionEquiv U F).symm s) := by
  rw [Subobject.factors_iff]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨(sectionEquiv U _).symm t, ?_⟩
    apply (sectionEquiv U F).injective
    rw [sectionEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact ht
  · rintro ⟨t, ht⟩
    refine ⟨sectionEquiv U _ t, ?_⟩
    change t ≫ G.arrow = (sectionEquiv U F).symm s at ht
    rw [← sectionEquiv_comp, ht, Equiv.apply_symm_apply]

private theorem fg_bot {X : Scheme.{v}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}) :
    IsFinitelyGeneratedEtaleSubsheaf (⊥ : Subobject F) := by
  refine ⟨0, Fin.elim0, fun j ↦ Fin.elim0 j, fun j ↦ Fin.elim0 j,
    fun j ↦ Fin.elim0 j, fun _ _ ↦ bot_le⟩

private theorem lifts_of_le {X : Scheme.{v}}
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}}
    {G H : Subobject F} (h : G ≤ H) (U : X.Etale) (s : F.obj.obj (op U))
    (hs : ∃ t : (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}).obj.obj (op U),
      G.arrow.hom.app (op U) t = s) :
    ∃ t : (H : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}).obj.obj (op U),
      H.arrow.hom.app (op U) t = s := by
  obtain ⟨t, ht⟩ := hs
  refine ⟨(Subobject.ofLE G H h).hom.app (op U) t, ?_⟩
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
    ← ObjectProperty.FullSubcategory.comp_hom, Subobject.ofLE_arrow]
  exact ht

private theorem fg_of_finite {X : Scheme.{v}}
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}}
    (G : Subobject F) {I : Type} [Finite I] (U : I → X.Etale)
    (hU : ∀ j, IsAffine (U j).left) (s : (j : I) → F.obj.obj (op (U j)))
    (hs : ∀ j, ∃ t : (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}).obj.obj
      (op (U j)), G.arrow.hom.app (op (U j)) t = s j)
    (hmin : ∀ H : Subobject F,
      (∀ j, ∃ t : (H : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}).obj.obj
        (op (U j)), H.arrow.hom.app (op (U j)) t = s j) → G ≤ H) :
    IsFinitelyGeneratedEtaleSubsheaf G := by
  classical
  let _ := Fintype.ofFinite I
  let e := Fintype.equivFin I
  refine ⟨Fintype.card I, fun j ↦ U (e.symm j), fun j ↦ hU (e.symm j),
    fun j ↦ s (e.symm j), fun j ↦ hs (e.symm j), ?_⟩
  intro H hH
  apply hmin H
  intro j
  obtain ⟨k, rfl⟩ := e.symm.surjective j
  exact hH k

private theorem fg_sup {X : Scheme.{v}}
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}}
    (G H : Subobject F) (hG : IsFinitelyGeneratedEtaleSubsheaf G)
    (hH : IsFinitelyGeneratedEtaleSubsheaf H) :
    IsFinitelyGeneratedEtaleSubsheaf (G ⊔ H) := by
  obtain ⟨n, U, hU, s, hs, hmin⟩ := hG
  obtain ⟨m, V, hV, t, ht, hmin'⟩ := hH
  let W : Fin n ⊕ Fin m → X.Etale := Sum.elim U V
  let r : (j : Fin n ⊕ Fin m) → F.obj.obj (op (W j)) :=
    fun j ↦ Sum.rec s t j
  apply fg_of_finite (G ⊔ H) W (fun j ↦ Sum.rec hU hV j) r
  · intro j
    cases j with
    | inl j => exact lifts_of_le le_sup_left (U j) (s j) (hs j)
    | inr j => exact lifts_of_le le_sup_right (V j) (t j) (ht j)
  · intro Q hQ
    exact sup_le (hmin Q (fun j ↦ hQ (.inl j)))
      (hmin' Q (fun j ↦ hQ (.inr j)))

private theorem image_section_fg {X : Scheme.{v}}
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}}
    (U : X.Etale) (hU : IsAffine U.left) (s : F.obj.obj (op U)) :
    IsFinitelyGeneratedEtaleSubsheaf (imageSubobject ((sectionEquiv U F).symm s)) := by
  let p := (sectionEquiv U F).symm s
  refine ⟨1, fun _ ↦ U, fun _ ↦ hU, fun _ ↦ s, ?_, ?_⟩
  · intro _
    apply (section_lifts_iff _ U s).2
    rw [Subobject.factors_iff]
    exact ⟨factorThruImageSubobject p, imageSubobject_arrow_comp p⟩
  · intro H hH
    obtain ⟨t, ht⟩ := (Subobject.factors_iff _ _).1 ((section_lifts_iff H U s).1 (hH 0))
    exact imageSubobject_le p t ht

private theorem fg_filtered {X : Scheme.{v}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}) :
    IsFiltered (ObjectProperty.FullSubcategory
      (IsFinitelyGeneratedEtaleSubsheaf (F := F))) := by
  let P : ObjectProperty (Subobject F) := IsFinitelyGeneratedEtaleSubsheaf
  have : Nonempty P.FullSubcategory := ⟨⟨⊥, fg_bot F⟩⟩
  refine { nonempty := inferInstance, cocone_objs := ?_, cocone_maps := ?_ }
  · intro G H
    exact ⟨⟨G.obj ⊔ H.obj, fg_sup G.obj H.obj G.property H.property⟩,
      ObjectProperty.homMk (homOfLE le_sup_left),
      ObjectProperty.homMk (homOfLE le_sup_right), trivial⟩
  · intro G H f g
    refine ⟨H, 𝟙 H, ?_⟩
    apply ObjectProperty.hom_ext
    exact Subsingleton.elim _ _

private theorem fg_colimit {X : Scheme.{v}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}) :
    let P : ObjectProperty (Subobject F) := IsFinitelyGeneratedEtaleSubsheaf
    ∃ (c : Cocone (P.ι ⋙ Subobject.underlying)) (e : c.pt ≅ F),
      Nonempty (IsColimit c) ∧ ∀ G : P.FullSubcategory,
        c.ι.app G ≫ e.hom = G.obj.arrow := by
  classical
  let P : ObjectProperty (Subobject F) := IsFinitelyGeneratedEtaleSubsheaf
  let J := P.FullSubcategory
  let D := P.ι ⋙ Subobject.underlying
  have : IsFiltered J := fg_filtered F
  have : Small.{v + 1} (Subobject F) := inferInstance
  have : Small.{v + 1} J := inferInstance
  have : EssentiallySmall.{v + 1} J := inferInstance
  have : HasColimitsOfShape J (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}) :=
    hasColimitsOfShape_of_essentiallySmall _ _
  have : IsFiltered (SmallModel.{v + 1} J) :=
    IsFiltered.of_equivalence (equivSmallModel.{v + 1} J)
  have : HasExactColimitsOfShape J
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}) :=
    HasExactColimitsOfShape.of_domain_equivalence _ (equivSmallModel.{v + 1} J).symm
  let c : Cocone D :=
    { pt := F
      ι := { app G := G.obj.arrow
             naturality G H f := by
               dsimp [D]
               rw [Subobject.underlying_arrow, Category.comp_id] } }
  have : HasColimit D := HasColimitsOfShape.has_colimit D
  let f := (colimit.isColimit D).desc c
  have hf (G : J) : (colimit.cocone D).ι.app G ≫ f = G.obj.arrow :=
    (colimit.isColimit D).fac c G
  let α : D ⟶ (Functor.const J).obj F := c.ι
  have : ∀ G, Mono (α.app G) := fun G ↦ inferInstanceAs (Mono G.obj.arrow)
  have : Mono α := NatTrans.mono_of_mono_app α
  have : IsConnected J := IsFiltered.isConnected J
  have : Mono f := colim.map_mono' α (colimit.isColimit D)
    (isColimitConstCocone J F) f (by simpa using hf)
  have : Sheaf.IsLocallySurjective f := by
    constructor
    intro U s
    rw [Scheme.mem_smallEtaleTopology_iff]
    intro x
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, _⟩ :=
      U.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    have : Etale U.hom := U.prop
    let V : X.Etale := Etale.mk (Scheme.Opens.ι W ≫ U.hom)
    let g : V ⟶ U := MorphismProperty.Over.homMk (Scheme.Opens.ι W) (by simp [V])
    let t := F.obj.map g.op s
    let G : J := ⟨imageSubobject ((sectionEquiv V F).symm t),
      image_section_fg V hW t⟩
    obtain ⟨a, ha⟩ := (section_lifts_iff G.obj V t).mpr
      (by rw [Subobject.factors_iff];
          exact ⟨factorThruImageSubobject _, imageSubobject_arrow_comp _⟩)
    refine ⟨V, g, ?_, ⟨⟨x, hxW⟩, rfl⟩⟩
    refine ⟨((colimit.cocone D).ι.app G).hom.app (op V) a, ?_⟩
    change (f.hom.app (op V)) _ = t
    have he := congrArg (fun q : D.obj G ⟶ F ↦ q.hom.app (op V) a) (hf G)
    exact he.trans ha
  have : Epi f := inferInstance
  have : IsIso f := isIso_of_mono_of_epi f
  exact ⟨colimit.cocone D, asIso f, ⟨colimit.isColimit D⟩, hf⟩

/-- The finitely generated étale subsheaves form a filtered diagram whose colimit is `F`.
Source: Stacks Project, Tag 0F0N; blueprint `lem-kun-cp-approximation`, step 1
(blueprint: lem-kun-cp-filtered-colimit).

Proof: finite families of affine étale sections are closed under union, so sums give common
successors. Every étale section is locally represented on an affine étale chart, and the
resulting local epimorphism is an isomorphism because all transition maps are monomorphisms.
-/
theorem closedPointSheaf_finitelyGenerated_filteredColimit
    {K : Type v} [Field K] [IsSepClosed K] (X : Scheme.{v})
    [X.Over (Spec (.of K))] [LocallyOfFiniteType (X ↘ Spec (.of K))]
    [QuasiCompact (X ↘ Spec (.of K))]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})
    (_hF : etaleSheafSupport F ⊆ {x | IsClosed ({x} : Set X)}) :
    let P : ObjectProperty (Subobject F) := IsFinitelyGeneratedEtaleSubsheaf
    IsFiltered P.FullSubcategory ∧
      (∃ (c : Cocone (P.ι ⋙ Subobject.underlying)) (e : c.pt ≅ F),
        Nonempty (IsColimit c) ∧ ∀ G : P.FullSubcategory,
          c.ι.app G ≫ e.hom = G.obj.arrow) := by
  exact ⟨fg_filtered F, fg_colimit F⟩

end AlgebraicGeometry.Scheme
