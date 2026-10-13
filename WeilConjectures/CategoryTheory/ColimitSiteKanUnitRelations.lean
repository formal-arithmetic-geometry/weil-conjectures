/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import Mathlib.CategoryTheory.Filtered.Basic

/-! # Equality of Kan units at one stage

Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit),
independence of presentations in the section construction.
(blueprint: lem-weil-pbc-colimit-site-kan-unit-relations).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit),
section construction, independence of the presentation and restriction arrows.
(blueprint: lem-weil-pbc-colimit-site-kan-unit-relations).

Proof: Compute the value of the left Kan extension K by the set colimit
on structured arrows. The two unit generators have the same stage object and
identity arrow. Their equality is witnessed by a finite zigzag of generating
Kan relations. Lift all arrows in this zigzag to a common later category,
using surjectivity of the arrow colimit. The object-colimit equality criterion
aligns their endpoints with the transported stage objects. Refine once more
so the arrow-colimit equality criterion enforces all triangles and identifies
the two endpoint arrows with identities. Equalize the finitely many competing
maps from i and t.right, obtaining one morphism b in Under i.

Choose one b : t -> r at the common refinement. Map each generator (W, f, s)
to theta_b(s) restricted along its lifted arrow g : F(b.right)(U) -> F(b.right)(W).
A generating relation associated to h : W -> W' identifies the restriction
of s' along h with s' at W'. The lifted arrows satisfy
g' = g followed by F(b.right)(h). Naturality gives
theta_b(A_t(h.op)(s')) = A_r(F(b.right)(h).op)(theta_b(s')).
Restriction along g therefore has the same value as restriction along g'.
The reversed relation gives the reversed equality, and reflexive relations
are immediate.
Naturality of theta and the lifted triangles identify the images of each Kan
relation. Induction along the zigzag therefore equates the endpoint sections.
The identity endpoint arrows identify the two endpoint images with theta_b(x)
and theta_b(x'). No coherence between different theta maps is needed, since
all generators use the same b. No outer presheaf-colimit equality, sheaf
condition, or section diagram D is used in this argument.
-/
theorem raw_section_kan_unit_relations
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (i : J) (t : Under i)
    (A : ∀ r : Under i, (F.obj r.right)ᵒᵖ ⥤ Type u)
    (θ : ∀ (r : Under i) (b : t ⟶ r),
      A t ⟶ (F.map b.right).toFunctor.op ⋙ A r)
    (K : V.ptᵒᵖ ⥤ Type u)
    (β : A t ⟶ (V.ι.app t.right).toFunctor.op ⋙ K)
    (hβ : K.IsLeftKanExtension β)
    (U : F.obj t.right) :
    ∀ (x x' : (A t).obj (op U)), β.app (op U) x = β.app (op U) x' →
      ∃ (r : Under i) (b : t ⟶ r),
        (θ r b).app (op U) x = (θ r b).app (op U) x' := by sorry

end CategoryTheory
