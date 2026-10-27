/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P8
-/
module

public import Sheaf.CategoryTheory.Sites.OrientedProductLargeSiteData

/-! # Direct-image transformations from associated representables

Source: ILO Exposé XI §§1.3 and 1.6; adjunction and Yoneda.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe v w e ve
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.OrientedProduct

private noncomputable def sections {C : Type w} [Category.{v} C]
    (J : GrothendieckTopology C) (U : C) (M : Sheaf J (Type (max v w))) :
    ((largeAssociated J).obj U ⟶ M) ≃ M.obj.obj (.op U) :=
  ((sheafificationAdjunction J (Type (max v w))).homEquiv _ _).trans uliftYonedaEquiv

private theorem sections_precomp {C : Type w} [Category.{v} C]
    (J : GrothendieckTopology C) {U V : C} (r : U ⟶ V)
    (M : Sheaf J (Type (max v w))) (x : (largeAssociated J).obj V ⟶ M) :
    sections J U M ((largeAssociated J).map r ≫ x) =
      M.obj.map r.op (sections J V M x) := by
  exact (congrArg uliftYonedaEquiv
    ((sheafificationAdjunction J (Type (max v w))).homEquiv_naturality_left
      (uliftYoneda.map r) x)).trans (uliftYonedaEquiv_naturality _ r.op).symm

private theorem sections_postcomp {C : Type w} [Category.{v} C]
    (J : GrothendieckTopology C) (U : C) (M N : Sheaf J (Type (max v w)))
    (x : (largeAssociated J).obj U ⟶ M) (r : M ⟶ N) :
    sections J U N (x ≫ r) = r.hom.app (.op U) (sections J U M x) := by
  exact (congrArg uliftYonedaEquiv
    ((sheafificationAdjunction J (Type (max v w))).homEquiv_naturality_right x r)).trans
      (uliftYonedaEquiv_comp _ _)

private noncomputable def directSections {C : Type w} [Category.{v} C]
    {E : Type e} [Category.{ve} E] (J : GrothendieckTopology C)
    (a : GeometricMorphism E (Sheaf J (Type (max v w)))) (U : C) (M : E) :
    (a.inverse.obj ((largeAssociated J).obj U) ⟶ M) ≃
      (a.direct.obj M).obj.obj (.op U) :=
  (a.adj.homEquiv _ _).trans (sections J U (a.direct.obj M))

private theorem directSections_precomp {C : Type w} [Category.{v} C]
    {E : Type e} [Category.{ve} E] (J : GrothendieckTopology C)
    (a : GeometricMorphism E (Sheaf J (Type (max v w)))) {U V : C} (r : U ⟶ V)
    (M : E) (x : a.inverse.obj ((largeAssociated J).obj V) ⟶ M) :
    directSections J a U M (a.inverse.map ((largeAssociated J).map r) ≫ x) =
      (a.direct.obj M).obj.map r.op (directSections J a V M x) := by
  dsimp [directSections]
  rw [a.adj.homEquiv_naturality_left]
  exact sections_precomp J r _ _

private theorem directSections_postcomp {C : Type w} [Category.{v} C]
    {E : Type e} [Category.{ve} E] (J : GrothendieckTopology C)
    (a : GeometricMorphism E (Sheaf J (Type (max v w)))) (U : C)
    {M N : E} (x : a.inverse.obj ((largeAssociated J).obj U) ⟶ M) (r : M ⟶ N) :
    directSections J a U N (x ≫ r) =
      (a.direct.map r).hom.app (.op U) (directSections J a U M x) := by
  dsimp [directSections]
  rw [a.adj.homEquiv_naturality_right]
  exact sections_postcomp J U _ _ _ _

private noncomputable def directFromRepresentables {C : Type w} [Category.{v} C]
    {E : Type e} [Category.{ve} E] (J : GrothendieckTopology C)
    (a b : GeometricMorphism E (Sheaf J (Type (max v w))))
    (δ : largeAssociated J ⋙ b.inverse ⟶ largeAssociated J ⋙ a.inverse) :
    a.direct ⟶ b.direct where
  app M := ⟨
    { app := fun U ↦ ↾fun x ↦ directSections J b U.unop M
        (δ.app U.unop ≫ (directSections J a U.unop M).symm x)
      naturality := by
        intro U V r
        ext x
        obtain ⟨y, rfl⟩ := (directSections J a U.unop M).surjective x
        change directSections J b V.unop M
          (δ.app V.unop ≫ (directSections J a V.unop M).symm
            ((a.direct.obj M).obj.map r (directSections J a U.unop M y))) = _
        have hr := directSections_precomp J a r.unop M y
        simp only [Quiver.Hom.op_unop] at hr
        rw [← hr, Equiv.symm_apply_apply]
        have hn : b.inverse.map ((largeAssociated J).map r.unop) ≫ δ.app U.unop =
            δ.app V.unop ≫ a.inverse.map ((largeAssociated J).map r.unop) :=
          δ.naturality r.unop
        rw [← Category.assoc, ← hn, Category.assoc]
        change _ = (b.direct.obj M).obj.map r
          (directSections J b U.unop M
            (δ.app U.unop ≫ (directSections J a U.unop M).symm
              (directSections J a U.unop M y)))
        rw [Equiv.symm_apply_apply]
        simpa only [Quiver.Hom.op_unop] using
          directSections_precomp J b r.unop M (δ.app U.unop ≫ y) }⟩
  naturality := by
    intro M N r
    apply Sheaf.hom_ext
    ext U x
    obtain ⟨y, rfl⟩ := (directSections J a U.unop M).surjective x
    change directSections J b U.unop N
      (δ.app U.unop ≫ (directSections J a U.unop N).symm
        ((a.direct.map r).hom.app U (directSections J a U.unop M y))) = _
    rw [← directSections_postcomp, Equiv.symm_apply_apply, ← Category.assoc]
    change _ = (b.direct.map r).hom.app U
      (directSections J b U.unop M
        (δ.app U.unop ≫ (directSections J a U.unop M).symm
          (directSections J a U.unop M y)))
    rw [Equiv.symm_apply_apply]
    simpa only [Opposite.op_unop] using
      directSections_postcomp J b U.unop (δ.app U.unop ≫ y) r

private theorem directFromRepresentables_mate {C : Type w} [Category.{v} C]
    {E : Type e} [Category.{ve} E] (J : GrothendieckTopology C)
    (a b : GeometricMorphism E (Sheaf J (Type (max v w))))
    (δ : largeAssociated J ⋙ b.inverse ⟶ largeAssociated J ⋙ a.inverse) (U : C) :
    (GeometricMorphism.inverseMate (directFromRepresentables J a b δ)).app
      ((largeAssociated J).obj U) = δ.app U := by
  dsimp only [largeAssociated] at *
  apply (b.adj.homEquiv _ _).injective
  apply (sections J U _).injective
  have h := unit_conjugateEquiv_symm a.adj b.adj
    (directFromRepresentables J a b δ) ((largeAssociated J).obj U)
  have hh : b.adj.homEquiv _ _
      ((GeometricMorphism.inverseMate (directFromRepresentables J a b δ)).app
        ((largeAssociated J).obj U)) =
      a.adj.unit.app _ ≫ (directFromRepresentables J a b δ).app _ := h.symm
  exact (congrArg (sections J U _) hh).trans <| by
    rw [sections_postcomp]
    change directSections J b U (a.inverse.obj ((largeAssociated J).obj U))
      (δ.app U ≫ (directSections J a U _).symm
        (sections J U _ (a.adj.unit.app _))) = _
    have hid : sections J U _ (a.adj.unit.app _) = directSections J a U _ (𝟙 _) :=
      congrArg (sections J U _) (a.adj.homEquiv_id _).symm
    dsimp only [largeAssociated, Functor.comp_obj] at *
    rw [hid, Equiv.symm_apply_apply, Category.comp_id]
    rfl

private theorem mate_sections {C : Type w} [Category.{v} C]
    {E : Type e} [Category.{ve} E] (J : GrothendieckTopology C)
    (a b : GeometricMorphism E (Sheaf J (Type (max v w))))
    (τ : a.direct ⟶ b.direct) (U : C) (M : E)
    (y : a.inverse.obj ((largeAssociated J).obj U) ⟶ M) :
    (τ.app M).hom.app (.op U) (directSections J a U M y) =
      directSections J b U M
        ((GeometricMorphism.inverseMate τ).app ((largeAssociated J).obj U) ≫ y) := by
  have hu : a.adj.unit.app ((largeAssociated J).obj U) ≫
      τ.app (a.inverse.obj ((largeAssociated J).obj U)) =
      b.adj.unit.app ((largeAssociated J).obj U) ≫
        b.direct.map ((GeometricMorphism.inverseMate τ).app
          ((largeAssociated J).obj U)) :=
    unit_conjugateEquiv_symm a.adj b.adj τ _
  have hh : a.adj.homEquiv _ _ y ≫ τ.app M =
      b.adj.homEquiv _ _
        ((GeometricMorphism.inverseMate τ).app ((largeAssociated J).obj U) ≫ y) := by
    rw [a.adj.homEquiv_unit, b.adj.homEquiv_unit, b.direct.map_comp,
      ← Category.assoc, ← hu]
    rw [Category.assoc, τ.naturality, Category.assoc]
  exact (sections_postcomp J U _ _ _ _).symm.trans
    (congrArg (sections J U _) hh)

/-- A transformation of inverse images on associated representables extends uniquely,
by taking mates, to a transformation of the direct-image functors.

Source: ILO XI §§1.3 and 1.6 (the adjunction/Yoneda determination of direct images)
(blueprint: lem-trf-large-oriented-representable-comparison).

At an object M, identify sections of a_* M at U with maps a⁻¹(Uᵃ)→M.
Precomposition with delta(U) defines a map into sections of b_* M. Naturality
of delta and of these Hom equivalences gives a transformation of sheaves, natural
in M. The conjugate-unit identity shows that its mate at Uᵃ is delta(U).
For uniqueness, write every section as the adjunct of such a map and use the same
conjugate-unit identity and naturality of a proposed transformation. Thus its value
on every section is forced, proving equality of the direct-image transformations.
-/
theorem largeDirectImageFromRepresentables {C : Type w} [Category.{v} C]
    {E : Type e} [Category.{ve} E] (J : GrothendieckTopology C)
    (a b : GeometricMorphism E (Sheaf J (Type (max v w))))
    (δ : largeAssociated J ⋙ b.inverse ⟶ largeAssociated J ⋙ a.inverse) :
    ∃! τ : a.direct ⟶ b.direct, ∀ U : C,
      (GeometricMorphism.inverseMate τ).app ((largeAssociated J).obj U) = δ.app U := by
  refine ⟨directFromRepresentables J a b δ, directFromRepresentables_mate J a b δ, ?_⟩
  intro τ hτ
  apply NatTrans.ext
  funext M
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  ext x
  obtain ⟨y, rfl⟩ := (directSections J a U.unop M).surjective x
  have ht := mate_sections J a b τ U.unop M y
  rw [hτ] at ht
  have hd := mate_sections J a b (directFromRepresentables J a b δ) U.unop M y
  rw [directFromRepresentables_mate] at hd
  exact ht.trans hd.symm

private theorem directMate_ext {C : Type w} [Category.{v} C]
    {E : Type e} [Category.{ve} E] (J : GrothendieckTopology C)
    (a b : GeometricMorphism E (Sheaf J (Type (max v w))))
    (τ σ : a.direct ⟶ b.direct)
    (h : ∀ U : C, (GeometricMorphism.inverseMate τ).app ((largeAssociated J).obj U) =
      (GeometricMorphism.inverseMate σ).app ((largeAssociated J).obj U)) : τ = σ := by
  obtain ⟨_, _, hu⟩ := largeDirectImageFromRepresentables J a b
    (Functor.whiskerLeft (largeAssociated J) (GeometricMorphism.inverseMate σ))
  exact (hu τ h).trans (hu σ (fun _ ↦ rfl)).symm

/-- An isomorphism of inverse images on associated representables gives an isomorphism
of direct images with the prescribed mate.

Source: ILO XI §1.6, uniqueness, by adjunction and Yoneda
(blueprint: lem-trf-large-oriented-representable-comparison).

Extend the isomorphism and its inverse using largeDirectImageFromRepresentables.
The mate of their composite is the reversed composite of mates, hence the identity
on each associated representable. Uniqueness in that theorem identifies the composites
with identities, making the two extensions inverse isomorphisms.
-/
theorem largeDirectImageIsoFromRepresentables {C : Type w} [Category.{v} C]
    {E : Type e} [Category.{ve} E] (J : GrothendieckTopology C)
    (a b : GeometricMorphism E (Sheaf J (Type (max v w))))
    (δ : largeAssociated J ⋙ b.inverse ≅ largeAssociated J ⋙ a.inverse) :
    ∃ τ : a.direct ≅ b.direct, ∀ U : C,
      (GeometricMorphism.inverseMate τ.hom).app ((largeAssociated J).obj U) =
        δ.hom.app U := by
  obtain ⟨τ, hτ, _⟩ := largeDirectImageFromRepresentables J a b δ.hom
  obtain ⟨σ, hσ, _⟩ := largeDirectImageFromRepresentables J b a δ.inv
  have ht : τ ≫ σ = 𝟙 _ := by
    apply directMate_ext J a a
    intro U
    simp only [GeometricMorphism.inverseMate,
      ← conjugateEquiv_symm_comp a.adj b.adj a.adj, NatTrans.comp_app,
      conjugateEquiv_symm_id, NatTrans.id_app]
    change (GeometricMorphism.inverseMate σ).app _ ≫
      (GeometricMorphism.inverseMate τ).app _ = _
    rw [hσ, hτ]
    exact δ.inv_hom_id_app U
  have hs : σ ≫ τ = 𝟙 _ := by
    apply directMate_ext J b b
    intro U
    simp only [GeometricMorphism.inverseMate,
      ← conjugateEquiv_symm_comp b.adj a.adj b.adj, NatTrans.comp_app,
      conjugateEquiv_symm_id, NatTrans.id_app]
    change (GeometricMorphism.inverseMate τ).app _ ≫
      (GeometricMorphism.inverseMate σ).app _ = _
    rw [hτ, hσ]
    exact δ.hom_inv_id_app U
  exact ⟨⟨τ, σ, ht, hs⟩, hτ⟩

end CategoryTheory.OrientedProduct
