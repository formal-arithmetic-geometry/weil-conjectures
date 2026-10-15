/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Sheaf.CategoryTheory.SimplicialMatchingObject
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Sheaf.Paper.SiteSheafificationSectionsLocal
import Sheaf.CategoryTheory.SiteCoveringAxioms

/-!
# Disjoint unions of semirepresentable hypercovers

Source: Stacks Project, Hypercoverings, Tags 0DB1 and 0DB2, in the slice over `T`
(blueprint: lem-weil-pbc-site-hypercover-disjoint-union).

The helper characterizes matching arrows by their proper-face projections, independently of
choices of limits. In a slice category its degree-zero target is the identity of the base,
and its degree-one target is the fibre product over the base.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace CategoryTheory.SimplicialObject

/-- An arrow is the proper-face matching arrow if its target, with the indicated projections,
is the boundary limit. Degree zero uses a terminal object, degree one a binary product,
and degree `n + 2` the recorded finite boundary diagram. In a slice these are the augmented
matching objects. The isomorphism in the last branch merely permits any choice of limit;
the equations specify the canonical arrow, rather than an arbitrary map to that limit.
Source: Stacks Project, Tags 0186, 0DB1 and 0DB2
(blueprint: lem-weil-pbc-site-hypercover-disjoint-union). -/
def IsProperFaceMatchingArrow {D : Type u} [Category.{v} D]
    (K : SimplicialObject D) (n : ℕ) (M : D) (μ : K _⦋n⦌ ⟶ M) : Prop :=
  match n with
  | 0 => Nonempty (IsTerminal M)
  | 1 => ∃ p : Fin 2 → (M ⟶ K _⦋0⦌),
      Nonempty (IsLimit (Fan.mk M p)) ∧ ∀ i : Fin 2, μ ≫ p i = K.δ i
  | n + 2 => ∃ c : Cone (matchingBoundaryIndex K n).multicospan,
      Nonempty (IsLimit c) ∧ ∃ e : M ≅ c.pt,
        ∀ i : Fin (n + 3), μ ≫ e.hom ≫ c.π.app (WalkingMulticospan.left i) = K.δ i

/-- Taking the disjoint unions of the terms of a semirepresentable hypercover over `T`
gives a simplicial object over `T` whose representable-sheaf matching arrows are epimorphisms.
The cofans specify the given coproducts. Their Yoneda-image cofans being colimiting is
exactly the hypothesis that the canonical sheaf-coproduct maps are isomorphisms. The
isomorphisms `e` identify the constructed simplicial terms with those specified coproducts;
the component equations say that every operator is the one induced by disjoint union.
Source: Stacks Project, Hypercoverings, Tags 0DB1 and 0DB2, in the slice over `T`
(blueprint: lem-weil-pbc-site-hypercover-disjoint-union).

Proof: (1) Use each coproduct universal property to induce every simplicial operator from
its component maps. Equality on all summands gives identity, composition and augmentation.
(2) Formal coproducts over `T` have finite limits
[lem-weil-pbc-semi-representable-finite-limits]. The functor sending a family to the
coproduct of its representable presheaves preserves finite limits in the slice: the terminal
family maps to `h_T`, and the explicit formal pullback formula gives sectionwise pullbacks.
Sheafification preserves these finite limits [lem-weil-pbc-sheafification-sets-exact], hence
identifies sheafified formal matching families with sheaf matching objects
[lem-weil-pbc-simplicial-matching-object]. (3) A section of a sheafified matching family is
locally represented by an actual section [lem-weil-pbc-site-sheafification-sections-local].
Pull back the componentwise matching cover to lift that section, and compose the two covers.
Thus the sheafified matching arrow is locally surjective, hence epi
[lem-weil-pbc-site-sheaf-sets-epi-locally-surjective]. This includes degree zero.
(4) Sheafified formal families are coproducts of representable sheaves by the sheafification
adjunction [def-weil-pbc-sheafification]. The assumed canonical coproduct isomorphisms commute
with all operators because they agree on each representable summand. The induced
isomorphisms of matching limits commute with their projections; conjugating the epi matching
arrows by these isomorphisms proves the conclusion. At degree zero the target is `h_T`,
and at degree one it is `h_A₀ ×[h_T] h_A₀`. -/
theorem site_hypercover_disjoint_union
    {C : Type u} [SmallCategory C] [HasPullbacks C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks] [J.toGrothendieck.Subcanonical]
    (T : C) (K : SimplicialObject (FormalCoproduct.{u} (Over T)))
    (hcover : ∀ (n : ℕ) (M : FormalCoproduct.{u} (Over T)) (μ : K _⦋n⦌ ⟶ M),
      IsProperFaceMatchingArrow K n M μ →
        ∀ j : M.I,
          Presieve.ofArrows
            (fun i : {i : (K _⦋n⦌).I // μ.f i = j} => ((K _⦋n⦌).obj i.val).left)
            (fun i => (μ.φ i.val ≫ eqToHom (congrArg M.obj i.property)).left) ∈
              J (M.obj j).left)
    (a : ∀ n : ℕ, Cofan (K _⦋n⦌).obj)
    (ha : ∀ n : ℕ, IsColimit (a n))
    (hsheaf : ∀ n : ℕ,
      IsColimit (Cofan.mk (J.toGrothendieck.yoneda.obj (a n).pt.left)
        (fun i : (K _⦋n⦌).I => J.toGrothendieck.yoneda.map ((a n).inj i).left))) :
    ∃ A : SimplicialObject (Over T), ∃ e : ∀ n : ℕ, A _⦋n⦌ ≅ (a n).pt,
      (∀ (m n : ℕ) (φ : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
        (i : (K _⦋n⦌).I),
        (a n).inj i ≫ (e n).inv ≫ A.map φ.op ≫ (e m).hom =
          (K.map φ.op).φ i ≫ (a m).inj ((K.map φ.op).f i)) ∧
      (∀ (n : ℕ) (M : Over (J.toGrothendieck.yoneda.obj T))
        (μ : (A ⋙ Over.post J.toGrothendieck.yoneda) _⦋n⦌ ⟶ M),
        IsProperFaceMatchingArrow (A ⋙ Over.post J.toGrothendieck.yoneda) n M μ →
          Epi μ.left) := by
  sorry

end CategoryTheory.SimplicialObject
