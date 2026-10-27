/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q42
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.Sites.CoherentTopos
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Yoneda
import Sheaf.CategoryTheory.Sites.EpimorphicFamilyCoverLifts
import Sheaf.CategoryTheory.Sites.SheafifiedArrowsCoverRefinement

/-!
# Quasi-compactness of a site object and its sheafified representable

Source: Stacks Project, `sites.tex`, Tag 0D06 and Definition 090H
(blueprint: lem-trf-site-quasicompact-sheafification-criterion).
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private theorem quasiCompact_iso_iff {E : Type*} [Category E]
    [HasCoproducts.{w} E] {A B : E} (e : A ≅ B) :
    IsQuasiCompactObject.{w} A ↔ IsQuasiCompactObject.{w} B := by
  have transfer {A B : E} (e : A ≅ B) (h : IsQuasiCompactObject.{w} A) :
      IsQuasiCompactObject.{w} B := by
    intro I F p hp
    have := hp
    have hdesc (T : Type w) (G : T → E) (q : ∀ i, G i ⟶ B) :
        Sigma.desc (fun i ↦ q i ≫ e.inv) = Sigma.desc q ≫ e.inv := by
      ext i
      simp only [Sigma.ι_desc, Sigma.ι_desc_assoc]
    have hepi : Epi (Sigma.desc (fun i ↦ p i ≫ e.inv)) := by
      rw [hdesc]
      infer_instance
    obtain ⟨s, hs⟩ := h I F (fun i ↦ p i ≫ e.inv) hepi
    refine ⟨s, ?_⟩
    rw [hdesc] at hs
    exact (epi_comp_iff_of_isIso _ _).mp hs
  exact ⟨transfer e, transfer e.symm⟩

/-
The site condition is expressed using covering presieves of arrows.  The
finite-image requirement is the condition that the refinement uses only
finitely many members of the original covering family.
-/
/--
Source: Stacks Project, `sites.tex`, Tag 0D06 and Definition 090H
(blueprint: lem-trf-site-quasicompact-sheafification-criterion).

Proof plan (the two steps of the node).
1. Assume the finite-image refinement property.  Given an epimorphic
   coproduct of sheaves onto the sheafified representable, use
   lem-weil-pbc-site-sheaf-sets-epi-locally-surjective to lift the identity
   section on a covering.  A coproduct is the sheafification of the
   objectwise disjoint union, by def-weil-pbc-sheafification and its
   adjunction.  The local representation clause of
   lem-weil-pbc-site-sheafification-sections-local refines this covering so
   that every lift is a section of one summand.  Compose these coverings
   using def-weil-pbc-sites-and-cohomology.  Apply the finite-image
   refinement property, and restrict the chosen sections to its members.
   The summand indices now have finite image.  The corresponding maps from
   sheafified representables factor through these finitely many summands.
   To see that their family is epimorphic, locally represent any section of
   the sheafified representable by arrows to U, pull the refinement back
   along those arrows, and compose the covers.  Each restriction then
   lifts through the representable of a refinement member.  The local
   surjectivity criterion proves that the finite sub-coproduct is epi.
2. Conversely, given a covering, the sheafified representables of its
   members form an epimorphic family: represent sections locally by arrows
   to U and pull the covering back.  Quasi-compactness gives a finite
   sub-coproduct that is still epi.  Lift the identity locally using the
   same local-surjectivity criterion.  Refine the lifted coproduct sections
   to sections of individual sheafified representables, and then to actual
   arrows using the local representation clause of
   lem-weil-pbc-site-sheafification-sections-local twice.  The composite
   arrow to U and the structure arrow have the same sheafified image;
   its local equality clause gives one further covering where they agree.
   Compose all these coverings using def-weil-pbc-sites-and-cohomology.
   Their arrows lie over U, and their original-cover indices range inside
   the finite subfamily.  This is the required finite-image refinement.
-/
theorem site_quasiCompact_iff_sheafifiedYoneda_quasiCompact
    {C : Type u} [Category.{v} C]
    (J : Precoverage C) (_hJ : J.IsSiteForCoverings) (U : C) :
    (∀ (I : Type (max u v)) (U_i : I → C) (a : ∀ i, U_i i ⟶ U),
      Presieve.ofArrows U_i a ∈ J U →
        ∃ (K : Type (max u v)) (V : K → C) (b : ∀ k, V k ⟶ U)
          (α : K → I) (c : ∀ k, V k ⟶ U_i (α k)),
          Set.Finite (Set.range α) ∧
            (∀ k, c k ≫ a (α k) = b k) ∧
              Presieve.ofArrows V b ∈ J U) ↔
      IsQuasiCompactObject.{max u v}
        ((presheafToSheaf J.toGrothendieck (Type (max u v))).obj
          (uliftYoneda.{u}.obj U)) := by
  classical
  let e : uliftYoneda.{u}.obj U ≅ uliftYoneda.{max u v}.obj U :=
    NatIso.ofComponents (fun _ ↦ (Equiv.ulift.trans Equiv.ulift.symm).toIso)
      (by intros; rfl)
  rw [quasiCompact_iso_iff
    ((presheafToSheaf J.toGrothendieck (Type (max u v))).mapIso e)]
  constructor
  · intro hcompact I F p hepi
    obtain ⟨A, V, a, ι, s, ha, hs⟩ :=
      (site_epimorphic_family_iff_cover_lifts J _hJ U F p).mp hepi
    obtain ⟨K, W, b, α, c, hα, hc, hb⟩ := hcompact A V a ha
    let t : Finset I := (hα.image ι).toFinset
    have ht (k : K) : ι (α k) ∈ t := by
      simpa only [t, Set.Finite.mem_toFinset] using
        (Set.mem_image_of_mem ι (Set.mem_range_self k))
    refine ⟨t, (site_epimorphic_family_iff_cover_lifts J _hJ U
      (fun i : t ↦ F i.1) (fun i : t ↦ p i.1)).mpr ?_⟩
    refine ⟨K, W, b, (fun k ↦ ⟨ι (α k), ht k⟩),
      (fun k ↦ (F (ι (α k))).obj.map (c k).op (s (α k))), hb, ?_⟩
    intro k
    have hp := ConcreteCategory.congr_hom ((p (ι (α k))).hom.naturality (c k).op) (s (α k))
    have hη := ConcreteCategory.congr_hom (CC := fun X ↦ X)
      ((toSheafify J.toGrothendieck (uliftYoneda.{max u v}.obj U)).naturality
        (c k).op) (ULift.up (a (α k)))
    dsimp at hp hη
    rw [hp, hs (α k)]
    rw [← hη]
    simp [uliftYoneda_obj_map, hc k]
  · intro hcompact I V a ha
    let F : I → Sheaf J.toGrothendieck (Type (max u v)) := fun i ↦
      (presheafToSheaf J.toGrothendieck (Type (max u v))).obj
        (uliftYoneda.{max u v}.obj (V i))
    let p : ∀ i, F i ⟶
        (presheafToSheaf J.toGrothendieck (Type (max u v))).obj
          (uliftYoneda.{max u v}.obj U) := fun i ↦
      (presheafToSheaf J.toGrothendieck (Type (max u v))).map
        (uliftYoneda.{max u v}.map (a i))
    have hepi : Epi (Sigma.desc p) := by
      apply (site_epimorphic_family_iff_cover_lifts J _hJ U F p).mpr
      refine ⟨I, V, a, id, (fun i ↦
        (toSheafify J.toGrothendieck (uliftYoneda.{max u v}.obj (V i))).app
          (Opposite.op (V i)) (ULift.up (𝟙 (V i)))), ha, ?_⟩
      intro i
      have hη := ConcreteCategory.congr_hom (CC := fun X ↦ X)
        (NatTrans.congr_app
          (toSheafify_naturality J.toGrothendieck (uliftYoneda.{max u v}.map (a i)))
          (Opposite.op (V i))) (ULift.up (𝟙 (V i)))
      dsimp at hη
      simpa only [p, id_eq, sheafifyMap, uliftYoneda_map_app,
        TypeCat.ofHom_apply, Category.id_comp] using hη.symm
    obtain ⟨t, ht⟩ := hcompact I F p hepi
    obtain ⟨K, W, b, α, c, hb, hc⟩ :=
      sheafified_arrows_cover_refinement J _hJ U
        (fun i : t ↦ V i.1) (fun i : t ↦ a i.1) ht
    refine ⟨K, W, b, (fun k ↦ (α k).1), c, ?_, hc, hb⟩
    exact t.finite_toSet.subset (by
      rintro i ⟨k, rfl⟩
      exact (α k).2)

end CategoryTheory
