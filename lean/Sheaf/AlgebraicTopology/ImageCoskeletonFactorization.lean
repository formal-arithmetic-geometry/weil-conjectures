/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S4
-/
module
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.AlgebraicTopology.SimplicialObject.Coskeletal
public import Mathlib.CategoryTheory.Sites.LeftExact
import Sheaf.AlgebraicTopology.CoskeletalMapTrivialKan
import Sheaf.CategoryTheory.TruncatedCoskeletonFiniteLimits
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
/-!
# Factoring a coskeletal comparison through its image coskeleton

Source: Stacks Project, Hypercoverings, Lemma 01GD, first paragraph, and
Simplicial Methods, Lemma 01A6.
(blueprint: lem-weil-pbc-image-coskeleton-factorization)
-/

@[expose] public section
universe u v w t
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open scoped Simplicial
namespace CategoryTheory.SimplicialObject

section Image

variable {B : Type u} [Category.{v} B] {C : Type w} [Category C]
  {L K : B ⥤ C ⥤ Type t}

private def imageObject (f : L ⟶ K) : B ⥤ C ⥤ Type t :=
  curry.obj (Subfunctor.range (uncurry.map f)).toFunctor

private def imageι (f : L ⟶ K) : imageObject f ⟶ K :=
  curry.map (Subfunctor.range (uncurry.map f)).ι ≫ (currying.unitIso.app K).inv

private def imageπ (f : L ⟶ K) : L ⟶ imageObject f :=
  (currying.unitIso.app L).hom ≫ curry.map (Subfunctor.toRange (uncurry.map f))

private theorem image_fac (f : L ⟶ K) : imageπ f ≫ imageι f = f := by
  ext b c x
  rfl

private theorem imageπ_epi (f : L ⟶ K) (b : B) : Epi ((imageπ f).app b) := by
  rw [NatTrans.epi_iff_epi_app]
  intro c
  rw [epi_iff_surjective]
  rintro ⟨x, y, rfl⟩
  exact ⟨y, rfl⟩

private theorem imageι_mono (f : L ⟶ K) (b : B) : Mono ((imageι f).app b) := by
  rw [NatTrans.mono_iff_mono_app]
  intro c
  rw [mono_iff_injective]
  exact fun x y h ↦ Subtype.ext h

end Image

set_option backward.isDefEq.respectTransparency false in
private theorem preserves_truncated_ran
    {A : Type u} [Category.{v} A] [HasFiniteLimits A]
    {D : Type w} [Category D]
    (Φ : A ⥤ D) [PreservesFiniteLimits Φ] (n : ℕ) :
    Φ.PreservesRightKanExtensions (SimplexCategory.Truncated.inclusion n).op := by
  obtain ⟨T, ε, hT, _, _, _, hΦ⟩ := truncatedCoskeletonFiniteLimits A n
  intro U
  have := hT U
  apply Functor.PreservesRightKanExtension.mk_of_preserves_isRightKanExtension
    Φ U (SimplexCategory.Truncated.inclusion n).op (T.obj U) (ε.app U)
  convert (hΦ D Φ inferInstance).1 U using 1 <;> first | rfl | (ext a; simp)

set_option backward.isDefEq.respectTransparency false in
private theorem preserves_coskeletal
    {A : Type u} [Category.{v} A] [HasLimitsOfSize.{0, 0} A] [HasFiniteLimits A]
    {D : Type w} [Category D] [HasLimitsOfSize.{0, 0} D]
    (Φ : A ⥤ D) [PreservesFiniteLimits Φ] (n : ℕ) (X : SimplicialObject A)
    (hX : IsIso ((coskAdj n).unit.app X)) :
    IsIso ((coskAdj n).unit.app (X ⋙ Φ)) := by
  have hpres : Φ.PreservesRightKanExtension
      ((SimplexCategory.Truncated.inclusion n).op ⋙ X)
      (SimplexCategory.Truncated.inclusion n).op := preserves_truncated_ran Φ n _
  have hX' : X.IsCoskeletal n := (isCoskeletal_iff_isIso X n).mpr hX
  have hh := Functor.PreservesRightKanExtension.preserves
    (G := Φ) X (𝟙 ((SimplexCategory.Truncated.inclusion n).op ⋙ X))
  apply (isCoskeletal_iff_isIso (X ⋙ Φ) n).mp
  constructor
  convert hh using 1 <;> first | rfl | (ext a; simp)

/-- Image-coskeleton factorization of a locally surjective comparison.
(blueprint: lem-weil-pbc-image-coskeleton-factorization)

Source: Stacks Project, Hypercoverings, Lemma 01GD, first paragraph.
Take the degreewise image of `f` and truncate at `n`. Below degree `n` the inclusion
is an isomorphism, so this is the image truncation of the source. Coskeletonizing gives `M`
and the adjunction gives `p`, `q`, and the factorization identity. The inclusion of the
image is mono and becomes epi after sheafification; hence it becomes an isomorphism.
Sheafification preserves finite limits, so all degrees of `q` become isomorphisms.
Evaluation also preserves those finite limits. The map `p` is bijective below `n`
and surjective in degree `n` at every object. Both its source and target are
`n`-coskeletal, so the coskeletal boundary lifting criterion applies.
-/
theorem exists_imageCoskeleton_factorization
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (n : ℕ) (_hn : 1 ≤ n)
    {L K : SimplicialObject (Cᵒᵖ ⥤ Type (max u v w))} (f : L ⟶ K)
    (hlow : ∀ i : ℕ, i < n → IsIso (f.app (Opposite.op ⦋i⦌)))
    (hsurj : Epi ((presheafToSheaf J (Type (max u v w))).map
      (f.app (Opposite.op ⦋n⦌))))
    (hL : IsIso ((coskAdj n).unit.app L))
    (hK : IsIso ((coskAdj n).unit.app K)) :
    ∃ (M : SimplicialObject (Cᵒᵖ ⥤ Type (max u v w)))
      (p : L ⟶ M) (q : M ⟶ K), p ≫ q = f ∧
      (∀ V : C, SSet.modelCategoryQuillen.I.rlp
        (((whiskeringRight _ _ _).obj
          ((evaluation (Cᵒᵖ) (Type (max u v w))).obj (Opposite.op V))).map p)) ∧
      (∀ i : ℕ, IsIso ((presheafToSheaf J (Type (max u v w))).map
        (q.app (Opposite.op ⦋i⦌)))) := by
  let S := imageObject f
  let a : L ⟶ S := imageπ f
  let b : S ⟶ K := imageι f
  have hab : a ≫ b = f := image_fac f
  have hb (i : ℕ) (hi : i < n) : IsIso (b.app (Opposite.op ⦋i⦌)) := by
    have := imageι_mono f (Opposite.op ⦋i⦌)
    have := hlow i hi
    have := epi_of_epi_fac (NatTrans.congr_app hab (Opposite.op ⦋i⦌))
    exact isIso_of_mono_of_epi _
  have ha (i : ℕ) (hi : i < n) : IsIso (a.app (Opposite.op ⦋i⦌)) := by
    have := hb i hi
    have := hlow i hi
    exact IsIso.of_isIso_fac_right (NatTrans.congr_app hab (Opposite.op ⦋i⦌))
  let U := (truncation n).obj S
  let T := Truncated.cosk (C := Cᵒᵖ ⥤ Type (max u v w)) n
  let M := T.obj U
  let p : L ⟶ M := (coskAdj n).unit.app L ≫ T.map ((truncation n).map a)
  let q : M ⟶ K := T.map ((truncation n).map b) ≫ inv ((coskAdj n).unit.app K)
  have hpε : (truncation n).map p ≫ (coskAdj n).counit.app U =
      (truncation n).map a := by
    simp only [p, Functor.map_comp, Category.assoc]
    have he := (coskAdj n).counit.naturality ((truncation n).map a)
    change (truncation n).map (T.map ((truncation n).map a)) ≫
      (coskAdj n).counit.app U = _ at he
    rw [he, ← Category.assoc, (coskAdj n).left_triangle_components,
      Category.id_comp, Functor.id_map]
  refine ⟨M, p, q, ?_, ?_, ?_⟩
  · dsimp only [p, q]
    rw [Category.assoc, ← T.map_comp_assoc, ← Functor.map_comp, hab]
    have he := (coskAdj n).unit.naturality f
    change f ≫ (coskAdj n).unit.app K =
      (coskAdj n).unit.app L ≫ T.map ((truncation n).map f) at he
    rw [← Category.assoc, ← he]
    simp
  · intro V
    apply SSet.rlp_boundaries_of_coskeletal_map _ n
    · intro i hi
      let j : (SimplexCategory.Truncated n)ᵒᵖ := Opposite.op ⟨⦋i⦌, hi.le⟩
      have he := NatTrans.congr_app hpε j
      change p.app (Opposite.op ⦋i⦌) ≫ ((coskAdj n).counit.app U).app j =
        a.app (Opposite.op ⦋i⦌) at he
      have := ha i hi
      have hpi : IsIso (p.app (Opposite.op ⦋i⦌)) := IsIso.of_isIso_fac_right he
      exact (isIso_iff_bijective _).mp
        (inferInstanceAs (IsIso ((p.app (Opposite.op ⦋i⦌)).app (Opposite.op V))))
    · let j : (SimplexCategory.Truncated n)ᵒᵖ := Opposite.op ⟨⦋n⦌, le_rfl⟩
      have he := NatTrans.congr_app hpε j
      change p.app (Opposite.op ⦋n⦌) ≫ ((coskAdj n).counit.app U).app j =
        a.app (Opposite.op ⦋n⦌) at he
      have := imageπ_epi f (Opposite.op ⦋n⦌)
      have hpE : Epi (p.app (Opposite.op ⦋n⦌)) := by
        have he' : p.app (Opposite.op ⦋n⦌) = a.app (Opposite.op ⦋n⦌) ≫
            inv (((coskAdj n).counit.app U).app j) := by
          rw [← he, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
        rw [he']
        infer_instance
      exact (epi_iff_surjective _).mp
        (inferInstanceAs (Epi ((p.app (Opposite.op ⦋n⦌)).app (Opposite.op V))))
    · apply preserves_coskeletal _ n M
      exact (coskAdj n).isIso_unit_app_of_iso (Iso.refl M)
    · exact preserves_coskeletal _ n L hL
  · let A := presheafToSheaf J (Type (max u v w))
    have hbA : IsIso (Functor.whiskerRight ((truncation n).map b) A) := by
      rw [NatTrans.isIso_iff_isIso_app]
      rintro ⟨⟨⟨i⟩, hi⟩⟩
      change IsIso (A.map (b.app (Opposite.op ⦋i⦌)))
      by_cases hil : i < n
      · have := hb i hil
        exact A.map_isIso _
      · have hin : i = n := Nat.le_antisymm hi (Nat.le_of_not_lt hil)
        subst i
        have := imageι_mono f (Opposite.op ⦋n⦌)
        have he := congrArg A.map (NatTrans.congr_app hab (Opposite.op ⦋n⦌))
        rw [NatTrans.comp_app, A.map_comp] at he
        have hE : Epi (A.map (b.app (Opposite.op ⦋n⦌))) := epi_of_epi_fac he
        exact isIso_of_mono_of_epi _
    have hpres : A.PreservesRightKanExtensions
        (SimplexCategory.Truncated.inclusion n).op := preserves_truncated_ran A n
    let e := A.ranCompIsoOfPreserves (SimplexCategory.Truncated.inclusion n).op
    have hT : IsIso (Functor.whiskerRight (T.map ((truncation n).map b)) A) := by
      apply (NatIso.isIso_map_iff e ((truncation n).map b)).mpr
      change IsIso ((Truncated.cosk n).map
        (Functor.whiskerRight ((truncation n).map b) A))
      infer_instance
    have hqA : IsIso (Functor.whiskerRight q A) := by
      change IsIso (((whiskeringRight _ _ _).obj A).map
        (T.map ((truncation n).map b) ≫ inv ((coskAdj n).unit.app K)))
      rw [Functor.map_comp]
      change IsIso (Functor.whiskerRight (T.map ((truncation n).map b)) A ≫
        ((whiskeringRight _ _ _).obj A).map (inv ((coskAdj n).unit.app K)))
      infer_instance
    intro i
    exact (NatTrans.isIso_iff_isIso_app _).mp hqA (Opposite.op ⦋i⦌)

end CategoryTheory.SimplicialObject
