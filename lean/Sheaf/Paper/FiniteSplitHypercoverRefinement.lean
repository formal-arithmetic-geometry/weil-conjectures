/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FiniteSplitEtaleHypercover
public import Sheaf.AlgebraicGeometry.SemiRepresentableObject
import Sheaf.Paper.EtaleHypercoverProduct
import Sheaf.Paper.FiniteSplitHypercoverExistence
import Sheaf.Paper.FiniteSplitHypercoverReplacement
import Sheaf.Paper.EtaleHypercoverHomotopyEqualizer

/-!
# Finite refinements and local lifting

Source: blueprint `lem-weil-pbc-hypercover-refinement`, order 947;
Stacks Project, Hypercoverings, Tags 0DAV, 094K, 01GJ, 01GK, 01GS.
(blueprint: lem-weil-pbc-hypercover-refinement)

Cofilteredness is stated by its three defining conditions. Covering sieves encode
restriction-stable local lifting requirements; lifts are on the finite constituent
pieces, as in the semi-representable interpretation of hypercovers.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FiniteSplitEtaleHypercover

/-- Existence and cofilteredness modulo simplicial homotopy.
Source: blueprint order 947; Stacks Tags 0DAV, 094K, 01GI, 01GN, 01GS.
Proof: finite limits of qcqs étale objects are qcqs, by
lem-weil-pbc-qcqs-morphism-permanence. Cover each matching component by finitely many
affine opens (lem-weil-pbc-qcqs-finite-affine-open-cover), refine its covering by
finite affine étale pieces (lem-weil-pbc-etale-covering-affine-refinement), and
inductively adjoin these as nondegenerate summands, retaining all degeneracies.
Matching equations give the face identities, and epi-mono factorization gives
all remaining simplicial identities. This constructs an object in every degree.
For two objects apply this construction to their product (lem-weil-pbc-hypercover-product).
For parallel maps pull back the endpoint map of the simplicial path object.
Its matching covers follow from lem-weil-pbc-hypercover-finite-simplex-lifting
applied to the finite triangulated prisms, with the comparison
lem-weil-pbc-sr-matching-object-one-member. A finite split replacement gives a
homotopy between the two composites, hence equality in RefinementClasses.
(blueprint: lem-weil-pbc-hypercover-refinement) -/
theorem exists_and_cofiltered (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
    Nonempty (FiniteSplitEtaleHypercover X) ∧
      (∀ U V : FiniteSplitEtaleHypercover X,
        ∃ W : FiniteSplitEtaleHypercover X, Nonempty (W.Refinement U) ∧
          Nonempty (W.Refinement V)) ∧
      (∀ (U V : FiniteSplitEtaleHypercover X) (a b : U.Refinement V),
        ∃ (W : FiniteSplitEtaleHypercover X) (c : W.Refinement U),
          isRefinementHomotopic (c ≫ a) (c ≫ b)) := by
  have hypercover (U : FiniteSplitEtaleHypercover X) : IsEtaleHypercover U.simplicial := by
    intro n
    exact ⟨U.matching n, U.projection n, U.matchingMap n,
      U.projection_naturality n, U.matching_universal n,
      U.matchingMap_projection n, U.matching_cover n⟩
  refine ⟨exists_finite_split_hypercover X, ?_, ?_⟩
  · intro U V
    obtain ⟨W, ⟨c⟩⟩ := exists_finite_split_replacement (U.simplicial ⨯ V.simplicial)
      (isEtaleHypercover_prod X U.simplicial V.simplicial (hypercover U) (hypercover V))
    exact ⟨W, ⟨c ≫ prod.fst⟩, ⟨c ≫ prod.snd⟩⟩
  · intro U V a b
    obtain ⟨K, hK, c, ⟨H⟩⟩ := exists_etale_hypercover_homotopy_equalizer U V a b
    obtain ⟨W, ⟨d⟩⟩ := exists_finite_split_replacement K hK
    refine ⟨W, d ≫ c, Relation.EqvGen.rel _ _ ?_⟩
    exact ⟨by simpa only [Category.assoc] using H.precomp d⟩

/-- A finite family of locally solvable requirements is solved on finite constituent
pieces after refinement. Each sieve consists of maps on which the corresponding lift
exists; its covering condition is precisely local solvability. No compatibility between
independent lifts is required. Source: blueprint order 947; Stacks Tags 01GJ, 01GK, 094K.
Proof: before fixing a nondegenerate degree, pull back every higher-degree requirement
along all degeneracies through r. There are only finitely many such requirements.
Intersect their covering families with the relative matching cover, then choose a
common finite affine refinement using lem-weil-pbc-etale-covering-base-change,
lem-weil-pbc-qcqs-finite-affine-open-cover and lem-weil-pbc-etale-covering-affine-refinement.
The new summands solve all requirements, and degenerate copies inherit the solutions
on their lower-degree sources. Continue unconstrained above r. The canonical split
cofans and the finite cofans of the nondegenerate summands supply the finite cofan
in each retained degree. For sheaf-valued lifting data these constituent solutions
glue over the disjoint union to a solution on the whole term.
(blueprint: lem-weil-pbc-hypercover-refinement) -/
theorem exists_refinement_solving_local_requirements
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U : FiniteSplitEtaleHypercover X) (r k : ℕ) (degree : Fin k → Fin (r + 1))
    (R : ∀ j : Fin k, Sieve (U.simplicial.obj (op (SimplexCategory.mk (degree j).val))))
    (hR : ∀ j, R j ∈ X.smallEtaleTopology
      (U.simplicial.obj (op (SimplexCategory.mk (degree j).val)))) :
    ∃ (V : FiniteSplitEtaleHypercover X) (f : V.Refinement U),
      ∀ n : Fin (r + 1), ∃ (l : ℕ) (T : Fin l → X.Etale)
        (ι : ∀ i, T i ⟶ V.simplicial.obj (op (SimplexCategory.mk n.val))),
        Nonempty (IsColimit (Cofan.mk (V.simplicial.obj (op (SimplexCategory.mk n.val))) ι)) ∧
          ∀ (j : Fin k) (h : degree j = n) (i : Fin l),
            R j (ι i ≫ f.app (op (SimplexCategory.mk n.val)) ≫
              eqToHom (congrArg (fun m : Fin (r + 1) ↦
                U.simplicial.obj (op (SimplexCategory.mk m.val))) h.symm)) := by
  sorry

/-- An arbitrary étale hypercover has a finite split refinement through any finite degree.
Source: blueprint order 947; Stacks Tags 01GJ, 0DAV, 094K.
Proof: construct the split skeleton inductively. In degree n the relative target is
M_n(V) ×_{M_n(K)} K_n. Its projection is a covering by
lem-weil-pbc-etale-covering-base-change. Each matching component of V is qcqs, so
lem-weil-pbc-qcqs-finite-affine-open-cover and
lem-weil-pbc-etale-covering-affine-refinement select finitely many affine pieces of
this cover, without a quasi-compactness assumption on K_n. They define the new faces
and the refinement map. Retain the inherited degeneracies and continue through r;
above r use the ordinary finite split extension. The comparison
lem-weil-pbc-sr-matching-object-one-member identifies the scheme and formal-family
matching conditions. (blueprint: lem-weil-pbc-hypercover-refinement) -/
theorem exists_truncated_refinement
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (K : SimplicialObject X.Etale)
    (hK : X.IsSemiRepresentableHypercover
      (K ⋙ FormalCoproduct.incl.{u} X.Etale)) (r : ℕ) :
    ∃ V : FiniteSplitEtaleHypercover X,
      Nonempty ((SimplicialObject.truncation r).obj V.simplicial ⟶
          (SimplicialObject.truncation r).obj K) := by
  sorry

end AlgebraicGeometry.FiniteSplitEtaleHypercover
