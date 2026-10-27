/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.AffineEtaleHypercoverPresentation
public import Sheaf.AlgebraicGeometry.SpaceEtaleHypercover
public import Mathlib.AlgebraicGeometry.Cover.Open
import Sheaf.Paper.SiteHypercoverFiniteExtensionConstruction
import Sheaf.Paper.SiteHypercoverFiniteExtensionSplit
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers

/-! # Affine-component étale hypercovers and split refinements

Source: Stacks Project, Hypercoverings, Tags 0DAV, 0DAU, 0DB0, 0DB2 and 0DAY
(blueprint: lem-sfb-affine-etale-hypercover-refinement).

The base scheme is arbitrary. Prescribed affine-cover factorizations are required
only on nondegenerate components. Naturality forces the maps on degenerate copies.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Existence over every scheme, including compatibility with algebraic-space base change.
Source: Stacks, Tags 0DAV, 0DB2 and 0DAY
(blueprint: lem-sfb-affine-etale-hypercover-refinement).

Proof: Work in formal families of étale T-schemes, whose finite limits exist by
lem-weil-pbc-semi-representable-finite-limits. The proper-face matching diagram is
finite (lem-weil-pbc-matching-object-proper-faces). Start with an affine open cover
of T (lem-weil-pbc-affine-opens-basis). At each degree cover every matching component
by affine opens, using etale composition and covering composition and base change.
Apply lem-weil-pbc-site-split-attachment-operators and
lem-weil-pbc-site-split-attachment-split to adjoin the new components and all forced
old degeneracies. Strict restriction gives a compatible countable sequence of
truncations and hence a full simplicial formal family, without finite subcovers.
Realize each family by its scheme coproduct (lem-weil-pbc-scheme-coproduct-family);
component maps glue uniquely (lem-weil-pbc-scheme-morphism-gluing). Disjoint open
summands identify each finite matching limit with the realized formal matching
family. Étale cancellation and locality on the source show the matching arrows
are étale; the component coverings give surjectivity. For every algebraic space X/T,
finite limits commute with base change, and surjective étale maps remain so
(lem-trf-space-fibre-products-etale-covers). Inverse images of the disjoint open
summands give the displayed pulled-back coproduct cofans. The empty boundary gives
X in degree zero; no affineness of the pulled-back components is claimed. -/
theorem exists_affine_etale_hypercover (T : Scheme.{u}) :
    ∃ V : AffineEtaleHypercoverPresentation T,
      ∀ X : AlgebraicSpace T,
        AlgebraicSpace.IsSpaceEtaleHypercover X
          (V.simplicial ⋙ Scheme.Etale.forget T ⋙ AlgebraicSpace.schemeBaseChange X) ∧
        ∀ n : SimplexCategoryᵒᵖ,
          Nonempty (IsColimit (Cofan.mk
            ((AlgebraicSpace.schemeBaseChange X).obj
              ((Scheme.Etale.forget T).obj (V.simplicial.obj n)))
            (fun i ↦ (AlgebraicSpace.schemeBaseChange X).map (V.inclusion n i)))) := by
  sorry

/-- Split refinement with prescribed affine opens on precisely the nondegenerate summands.
The canonical normalization in `V.split` gives I_n as the disjoint union of epi labels
and nondegenerate indices; its component isomorphisms identify each summand with its
nondegenerate source. The last equality is the forced map to H on every such copy.
Source: Stacks, Tags 0DAV (relative matching construction), 0DAU, 0DB2 and 0DAY
(blueprint: lem-sfb-affine-etale-hypercover-refinement).

Proof: Perform the construction in the preceding theorem relative to H. In degree
zero refine the prescribed affine open cover of H_0. If the map is built below n,
for each formal matching component P form P ×_{M_n(H)} H_n. The projection onto P
is surjective étale by lem-weil-pbc-etale-covering-base-change. Cover the inverse
images of all prescribed degree-n affine opens by affine neighbourhoods, using
lem-weil-pbc-affine-opens-basis. Their composite maps cover P by
lem-weil-pbc-etale-covering-composition. Attach these as the new nondegenerate
summands with lem-weil-pbc-site-split-attachment-operators, retaining the old copies
indexed by proper surjections. The boundary equation gives faces and naturality
on new summands. On old summands use the lower-degree map followed by H's degeneracy.
The functor law, epi-mono factorization and the normalized attachment operators
check every naturality square. Lemma lem-weil-pbc-site-split-attachment-split proves
the epi-label bijections and component isomorphisms. Pass to all degrees by strict
restriction; realize by scheme coproducts and compare matching objects using the
disjoint open pieces, as above. Algebraic-space base change preserves both the
matching covering maps and the decompositions. Finally the displayed forced-map
equality follows by composing naturality of the component inclusion and of V → H.
No finite subcover, quasi-compactness or quasi-separatedness is used. -/
theorem exists_split_affine_etale_hypercover_refinement
    (T : Scheme.{u}) (H : SimplicialObject T.Etale) (hH : IsEtaleHypercover H)
    (cover : ∀ r : ℕ, (H.obj (op (SimplexCategory.mk r))).left.AffineOpenCover.{v}) :
    ∃ (V : AffineEtaleHypercoverPresentation T) (f : V.simplicial ⟶ H),
      (∀ X : AlgebraicSpace T,
        AlgebraicSpace.IsSpaceEtaleHypercover X
          (V.simplicial ⋙ Scheme.Etale.forget T ⋙ AlgebraicSpace.schemeBaseChange X) ∧
        ∀ n : SimplexCategoryᵒᵖ,
          Nonempty (IsColimit (Cofan.mk
            ((AlgebraicSpace.schemeBaseChange X).obj
              ((Scheme.Etale.forget T).obj (V.simplicial.obj n)))
            (fun i ↦ (AlgebraicSpace.schemeBaseChange X).map (V.inclusion n i))))) ∧
      (∀ (r : ℕ) (i : (V.components.obj (op (SimplexCategory.mk r))).I),
        CategoryTheory.FormalSplitAttachment.IsNondegenerate
          ((SimplicialObject.truncation (C := FormalCoproduct.{u} T.Etale) r).obj
            V.components) ⟨r, Nat.lt_succ_self r⟩ i →
        ∃ (j : (cover r).I₀)
          (g : ((V.components.obj (op (SimplexCategory.mk r))).obj i).left ⟶
            (cover r).openCover.X j),
          g ≫ (cover r).f j =
            (V.inclusion (op (SimplexCategory.mk r)) i).left ≫
              (f.app (op (SimplexCategory.mk r))).left) ∧
      ∀ (n r : ℕ) (σ : SimplexCategory.mk n ⟶ SimplexCategory.mk r) (_ : Epi σ)
        (i : (V.components.obj (op (SimplexCategory.mk r))).I),
        ∃ e : (V.components.obj (op (SimplexCategory.mk r))).obj i ≅
            (V.components.obj (op (SimplexCategory.mk n))).obj
              ((V.components.map σ.op).f i),
          e.hom = (V.components.map σ.op).φ i ∧
        V.inclusion (op (SimplexCategory.mk n)) ((V.components.map σ.op).f i) ≫
            (Scheme.Etale.forget T).map (f.app (op (SimplexCategory.mk n))) =
          (Scheme.Etale.forget T).map (e.inv) ≫
            V.inclusion (op (SimplexCategory.mk r)) i ≫
            (Scheme.Etale.forget T).map
              (f.app (op (SimplexCategory.mk r)) ≫ H.map σ.op) := by
  sorry

end AlgebraicGeometry
