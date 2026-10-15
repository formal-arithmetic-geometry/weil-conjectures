/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Mathlib.Data.Finite.Sigma

/-!
# Coskeleta of truncated simplicial objects as finite limits

Source: literature/stacks-project/simplicial.tex, Lemmas 0183--0185 and
hypercovering.tex, Lemma 01GD (blueprint: lem-weil-pbc-truncated-coskeleton-finite-limits)
-/

@[expose] public section

universe u v w v'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Coskeleta exist as a functor, are computed by finite limits, and commute with
finite-limit-preserving functors, on objects and morphisms.

Source: literature/stacks-project/simplicial.tex, Lemmas 0183--0185 and
hypercovering.tex, Lemma 01GD (blueprint: lem-weil-pbc-truncated-coskeleton-finite-limits).

1. For each degree, there are finitely many arrows from truncated simplices to that
simplex, and finitely many arrows between them. Form the limit of the diagram
sending such an arrow to its truncated source term
(def-galois-finite-limits-colimits, def-weil-pbc-simplicial-set). Its projections
induce the simplicial operators by postcomposition; uniqueness proves their
identity and composition laws (def-weil-pbc-simplicial-object). Mathlib's
`RightExtension.coneAt` is exactly this cone, using the opposite-comma encoding.
2. Maps to these limits are compatible families. A map out of a simplicial object
is determined by the components at identity arrows. Conversely, a map from its
truncation gives the family by composing with each simplicial operator. These
constructions are inverse, proving the coskeleton mapping property
(def-weil-pbc-simplicial-coskeleton).
3. In a truncated degree the identity arrow is initial in the opposite indexing
category. Its projection is therefore an isomorphism, so the counit is an isomorphism
(Stacks 0184--0185).
4. A finite-limit-preserving functor sends each of these cones to a limit cone.
Their projection equations give the same simplicial operators after applying the
functor, hence the image object with the image counit is a coskeleton. The image
of a canonical coskeletality isomorphism is still an isomorphism and satisfies the
canonical counit equation, proving preservation of coskeletality.
5. A truncated morphism induces maps of the limit diagrams. Their unique induced
maps commute with simplicial operators and counits. The mapping property proves
uniqueness; applying it to identities and composites gives a functor, and applying
it to an inverse preserves isomorphisms. Applying the finite-limit-preserving
functor to the same equations gives precisely the induced map between image coskeleta.
6. Presheaf limits are computed objectwise and evaluations preserve finite limits
(lem-weil-pbc-presheaf-finite-limits-objectwise). Thus steps 4 and 5 apply to every
presheaf evaluation, including the canonical coskeletality isomorphism.
-/
theorem truncatedCoskeletonFiniteLimits
    (C : Type u) [Category.{v} C] [HasFiniteLimits C] (m : ℕ) :
    ∃ (R : SimplicialObject.Truncated C m ⥤ SimplicialObject C)
      (ε : R ⋙ SimplicialObject.truncation m ⟶ 𝟭 _),
      (∀ U, (R.obj U).IsRightKanExtension (ε.app U)) ∧
      (∀ U, Nonempty
        ((Functor.RightExtension.mk (R.obj U) (ε.app U)).IsPointwiseRightKanExtension)) ∧
      (∀ U, IsIso (ε.app U)) ∧
      (∀ (U U' : SimplicialObject.Truncated C m) (β : U ⟶ U') (b : R.obj U ⟶ R.obj U'),
        (SimplicialObject.truncation m).map b ≫ ε.app U' = ε.app U ≫ β →
          b = R.map β) ∧
      ∀ (D : Type w) [Category.{v'} D] (Φ : C ⥤ D),
        PreservesFiniteLimits Φ →
        (∀ U, (R.obj U ⋙ Φ).IsRightKanExtension (Functor.whiskerRight (ε.app U) Φ)) ∧
        (∀ (U U' : SimplicialObject.Truncated C m) (β : U ⟶ U')
          (b : R.obj U ⋙ Φ ⟶ R.obj U' ⋙ Φ),
          (SimplicialObject.truncation m).map b ≫ Functor.whiskerRight (ε.app U') Φ =
              Functor.whiskerRight (ε.app U) Φ ≫ Functor.whiskerRight β Φ →
            b = Functor.whiskerRight (R.map β) Φ) ∧
        (∀ (K : SimplicialObject C)
          (c : K ⟶ R.obj ((SimplicialObject.truncation m).obj K)),
          (SimplicialObject.truncation m).map c ≫
            ε.app ((SimplicialObject.truncation m).obj K) = 𝟙 _ →
          IsIso c →
          ∀ c' : K ⋙ Φ ⟶ R.obj ((SimplicialObject.truncation m).obj K) ⋙ Φ,
            (SimplicialObject.truncation m).map c' ≫
              Functor.whiskerRight (ε.app ((SimplicialObject.truncation m).obj K)) Φ = 𝟙 _ →
            IsIso c')
    := by
  classical
  let ι := (SimplexCategory.Truncated.inclusion m).op
  let (x y : SimplexCategoryᵒᵖ) : Finite (x ⟶ y) :=
    Finite.of_injective (fun f : x ⟶ y ↦ f.unop)
      (fun _ _ h ↦ Quiver.Hom.unop_inj h)
  have : Finite (SimplexCategory.Truncated m) := by
    apply Finite.of_injective (fun x : SimplexCategory.Truncated m ↦
      (⟨x.obj.len, Nat.lt_succ_of_le x.property⟩ : Fin (m + 1)))
    intro x y h
    apply ObjectProperty.FullSubcategory.ext
    exact SimplexCategory.ext (congrArg Fin.val h)
  have : Finite (SimplexCategory.Truncated m)ᵒᵖ :=
    Finite.of_injective Opposite.unop Opposite.unop_injective
  let (x y : (SimplexCategory.Truncated m)ᵒᵖ) : Finite (x ⟶ y) :=
    Finite.of_injective ι.map (Functor.map_injective _)
  have (n : SimplexCategoryᵒᵖ) : Finite (StructuredArrow n ι) := by
    apply Finite.of_surjective
      (fun z : Σ x : (SimplexCategory.Truncated m)ᵒᵖ, (n ⟶ ι.obj x) ↦
        StructuredArrow.mk z.2)
    rintro ⟨⟨⟨⟩⟩, x, f⟩
    exact ⟨⟨x, f⟩, rfl⟩
  let (n : SimplexCategoryᵒᵖ) (x y : StructuredArrow n ι) : Finite (x ⟶ y) :=
    Finite.of_injective (fun f : x ⟶ y ↦ f.right)
      (fun _ _ h ↦ StructuredArrow.hom_ext _ _ h)
  let (n : SimplexCategoryᵒᵖ) : FinCategory (StructuredArrow n ι) :=
    { fintypeObj := Fintype.ofFinite _
      fintypeHom := fun x y ↦ Fintype.ofFinite (x ⟶ y) }
  let (U : SimplicialObject.Truncated C m) : ι.HasPointwiseRightKanExtension U :=
    fun n ↦ inferInstance
  refine ⟨ι.ran, ι.ranCounit, ?_, ?_, ?_, ?_, ?_⟩
  · intro U
    infer_instance
  · intro U
    exact ⟨ι.isPointwiseRightKanExtensionRanCounit U⟩
  · intro U
    exact (ι.isPointwiseRightKanExtensionRanCounit U).isIso_hom
  · intro U U' β b hb
    apply Functor.hom_ext_of_isRightKanExtension _ (ι.ranCounit.app U')
    exact hb.trans (ι.ranCounit.naturality β).symm
  · intro D _ Φ hΦ
    let := hΦ
    have hkan (U : SimplicialObject.Truncated C m) :
        (ι.ran.obj U ⋙ Φ).IsRightKanExtension
          (Functor.whiskerRight (ι.ranCounit.app U) Φ) := by
      have h := Functor.PreservesRightKanExtension.preserves (G := Φ) (F := U) (L := ι)
        (ι.ran.obj U) (ι.ranCounit.app U)
      convert h using 1 <;> first | rfl | (ext x; simp)
    refine ⟨hkan, ?_, ?_⟩
    · intro U U' β b hb
      let := hkan U'
      apply Functor.hom_ext_of_isRightKanExtension (ι.ran.obj U' ⋙ Φ)
        (Functor.whiskerRight (ι.ranCounit.app U') Φ)
      change Functor.whiskerLeft ι b ≫ _ = _ at hb
      rw [hb]
      ext x
      have hβ := NatTrans.congr_app (ι.ranCounit.naturality β) x
      change (ι.ran.map β).app (ι.obj x) ≫ (ι.ranCounit.app U').app x =
        (ι.ranCounit.app U).app x ≫ β.app x at hβ
      change Φ.map ((ι.ranCounit.app U).app x) ≫ Φ.map (β.app x) =
        Φ.map ((ι.ran.map β).app (ι.obj x)) ≫ Φ.map ((ι.ranCounit.app U').app x)
      rw [← Φ.map_comp, ← Φ.map_comp, hβ]
    · intro K c hc hiso c' hc'
      let := hiso
      have hcc' : c' = Functor.whiskerRight c Φ := by
        let := hkan ((SimplicialObject.truncation m).obj K)
        apply Functor.hom_ext_of_isRightKanExtension
          (ι.ran.obj ((SimplicialObject.truncation m).obj K) ⋙ Φ)
          (Functor.whiskerRight (ι.ranCounit.app _) Φ)
        change Functor.whiskerLeft ι c' ≫ _ = _ at hc'
        rw [hc']
        ext x
        have hcx := NatTrans.congr_app hc x
        change c.app (ι.obj x) ≫ (ι.ranCounit.app _).app x = 𝟙 _ at hcx
        change 𝟙 _ = Φ.map (c.app (ι.obj x)) ≫ Φ.map ((ι.ranCounit.app _).app x)
        rw [← Φ.map_comp, hcx, Φ.map_id]
      rw [hcc']
      infer_instance

end CategoryTheory
