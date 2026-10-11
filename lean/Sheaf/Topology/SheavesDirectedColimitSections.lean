module

public import Mathlib.Topology.Sheaves.Sheaf

/-!
# Sections of directed colimits of sheaves over quasi-compact opens

Source: Stacks Project, Sheaves, Lemma 009F (parts (2) and (4));
(blueprint: lem-weil-pbc-sheaves-directed-colimit-sections).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace TopCat

/-- Source: Stacks Project, Sheaves, Lemma 009F, parts (2) and (4)
(blueprint: lem-weil-pbc-sheaves-directed-colimit-sections).
The proof identifies the sheaf colimit with the sheafification of the
sectionwise presheaf colimit.  Equality in a sheafification is local; on a
quasi-compact open a finite subcover and directedness give eventual equality.
For surjectivity, refine local lifts by the stated finite cofinal coverings,
use injectivity on quasi-compact pairwise intersections, and glue in one
stage of the directed system.
-/
theorem sheaves_directedColimit_sections
    (X : TopCat.{u}) (I : Type u) [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)]
    (D : I ⥤ TopCat.Sheaf (Type u) X) [HasColimit D] :
    ∃ Ψ : ∀ (U : Opens X),
        colimit (D ⋙ (TopCat.Sheaf.forget (Type u) X) ⋙
          (evaluation (Opens X)ᵒᵖ (Type u)).obj (op U)) ⟶
          (colimit D).obj.obj (op U),
      (∀ (U : Opens X) (i : I) (s : (D.obj i).obj.obj (op U)),
        Ψ U (colimit.ι (D ⋙ (TopCat.Sheaf.forget (Type u) X) ⋙
          (evaluation (Opens X)ᵒᵖ (Type u)).obj (op U)) i s) =
          (colimit.ι D i).1.app (op U) s) ∧
      (∀ (U : Opens X), IsCompact (U : Set X) →
        Function.Injective (Ψ U) ∧
        (∀ (i i' : I) (s : (D.obj i).obj.obj (op U))
            (s' : (D.obj i').obj.obj (op U)),
          (colimit.ι D i).1.app (op U) s =
              (colimit.ι D i').1.app (op U) s' →
            ∃ (i'' : I) (hi : i ≤ i'') (hi' : i' ≤ i''),
              (D.map (homOfLE hi)).1.app (op U) s =
                (D.map (homOfLE hi')).1.app (op U) s')) ∧
      (∀ (U : Opens X),
        (∀ (K : Type u) (V : K → Opens X),
          (∀ x : X, x ∈ U → ∃ k, x ∈ V k) →
          ∃ (J : Type u) (_ : Fintype J) (W : J → Opens X),
            (∀ x : X, x ∈ U → ∃ j, x ∈ W j) ∧
            (∀ j, ∃ k, W j ≤ V k) ∧
            (∀ j j', IsCompact (((W j ⊓ W j') : Opens X) : Set X))) →
        Function.Bijective (Ψ U) ∧
          (∀ t, ∃ (i : I) (s : (D.obj i).obj.obj (op U)),
            Ψ U (colimit.ι (D ⋙ (TopCat.Sheaf.forget (Type u) X) ⋙
              (evaluation (Opens X)ᵒᵖ (Type u)).obj (op U)) i s) = t)) := by
  sorry

end TopCat
