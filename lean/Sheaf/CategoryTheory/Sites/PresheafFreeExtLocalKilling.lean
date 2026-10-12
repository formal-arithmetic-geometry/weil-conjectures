/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Local killing of Ext classes from free abelian sheaves

Source: Stacks Project, Derived Categories, Tag 06XU; Cohomology on Sites, Tag 03F9.
(blueprint: lem-sc-presheaf-free-ext-local-killing)
-/

@[expose] public section

universe u v w'

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Sheaf

/-- A positive Ext class from the sheafified free abelian presheaf is killed after a
locally surjective map of small-valued presheaves.
Source: Stacks Project, Derived Categories, Tag 06XU (Yoneda representatives), and
Cohomology on Sites, Tag 03F9 (local lifting in the vanishing argument).
(blueprint: lem-sc-presheaf-free-ext-local-killing)

Proof: represent the class by a degree-q Yoneda extension using Tag 06XU and let
G -> Z[P] be its last epimorphism. At each object V construct E(V) as the subtype
of P(V) times G(V) consisting of pairs (p,g) for which g maps to the image of the
free generator p in Z[P](V). Restrictions act on both coordinates; naturality of
the generator map proves that they preserve the defining equality. Projection to
the first coordinate defines f:E -> P. This is locally surjective because the last
map of the extension is an epimorphism of abelian sheaves. E(V) remains in Type v.
Projection to the second coordinate gives a natural map E -> G; the free abelian
and sheafification adjunctions extend it to Z[E] -> G, whose composite with the
last epimorphism is Z[f]. Pulling the last short exact sequence back along Z[f]
therefore gives a split short exact sequence. Its Ext class is zero, so the entire
pulled-back Yoneda product is zero. For q=1 this is the sole short exact sequence.
No representative of a mere existence theorem is used to define public data. -/
theorem exists_presheaf_ext_local_killing
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{v}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
    (F : Sheaf J AddCommGrpCat.{v}) (P : Cᵒᵖ ⥤ Type v)
    (q : ℕ) (hq : 0 < q)
    (x : Ext ((presheafToSheaf J AddCommGrpCat).obj (P ⋙ AddCommGrpCat.free)) F q) :
    ∃ (E : Cᵒᵖ ⥤ Type v) (f : E ⟶ P), Presheaf.IsLocallySurjective J f ∧
      (Ext.mk₀ ((presheafToSheaf J AddCommGrpCat).map
        (Functor.whiskerRight f AddCommGrpCat.free))).comp x (Nat.zero_add q) = 0 := by
  sorry

end CategoryTheory.Sheaf
