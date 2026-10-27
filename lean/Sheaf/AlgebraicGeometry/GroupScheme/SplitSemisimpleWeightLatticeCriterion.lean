module

public import Sheaf.AlgebraicGeometry.GroupScheme.Semisimple
public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Sheaf.AlgebraicGeometry.TorusCharacterTangentWeights
public import Mathlib.LinearAlgebra.RootSystem.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Sheaf.AlgebraicGeometry.RelativeSplitTorusMatrixSheaf
import Sheaf.RepresentationTheory.RelativeTorusBundleWeights
import Sheaf.AlgebraicGeometry.ReductiveTorusSelfCentralizer
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections
import Sheaf.LinearAlgebra.RootDatumLatticeEmbedding
import Sheaf.AlgebraicGeometry.SemisimpleCentralIsogenyMultiplicative
import Sheaf.AlgebraicGeometry.GroupScheme.CentralIsogenyBorelRootCompatibility
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # The weight-lattice criterion over a split characteristic-zero field

Source: Milne, Algebraic Groups (2017), Propositions 23.29 and 23.59, pp.493,502;
Theorem 23.55 and Corollary 23.56, p.501; Proposition 19.15, pp.400--401.
(blueprint: lem-sfb-split-semisimple-weight-lattice-criterion)

The lattices are the actual group-scheme Hom groups, written additively. The root datum
is specified by its roots, composition pairing and adjoint character weights. Its
coroots are the normalized coroots: the finite root system and its perfect pairing
uniquely determine them, equivalently by the opposite rank-one root subgroups.
Rationalization is written with the rational factor first, using tensor symmetry.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory
open scoped MonObj TensorProduct

namespace AlgebraicGeometry

/-- Every central semisimple cover is an isomorphism exactly when the character lattice
is the full weight lattice. Covers need not be split over the original field.

Source: Milne, Propositions 23.29 and 23.59, pp.493,502; Theorem 23.55 and
Corollary 23.56, p.501; Proposition 19.15, pp.400--401.
(blueprint: lem-sfb-split-semisimple-weight-lattice-criterion)

Proof plan:
1. Extend to F = AlgebraicClosure k. Smoothness and affineness survive base change
   by lem-pc-proper-base-change and lem-weil-pbc-affine-morphism-permanence. Tensor
   the finite list of coordinate generators to retain finite type. The identity
   point and lem-sbc-connected-rational-point-geometrically-connected give geometric
   connectedness. The geometric semisimplicity hypothesis gives reductivity by
   lem-sfb-reductive-borel-pair-structure. Use
   lem-sfb-geometric-neutral-reductivity-field-invariance and
   lem-weil-pbc-smooth-ring-map-iff-smooth-affine for the relative reductive interface
   of def-sfb-pinned-split-root-realization. The same applies to each cover H'.
2. In split coordinates, lem-sfb-relative-split-torus-matrix-sheaf identifies the
   character and cocharacter groups with integer vectors, unchanged by extension
   and in perfect composition pairing. The tangent comparison of
   lem-sfb-affine-group-lie-tangent-calculus respects conjugation. By
   lem-sfb-relative-torus-bundle-weights each geometric root space is the scalar
   extension of its original root space, nonzero exactly when the latter is.
   Lemma lem-sfb-reductive-torus-self-centralizer preserves maximality after further
   extensions, and lem-sfb-arbitrary-base-root-lines-coroots identifies coroots and
   their rank-one normalization under extension. Thus all weight integrality tests
   are unchanged. Since k is infinite, its split torus points are dense, so the
   recorded tangent character spaces are the usual rational character spaces.
3. Apply lem-sfb-reductive-rank-one-reflections for the finite reflection group.
   Choose a regular integer cocharacter (1,N,...,N^(r-1)) avoiding the finitely
   many zeros of the root-coordinate polynomials; in rank zero choose zero.
   Lemma lem-sfb-regular-cocharacter-borel-description provides a Borel containing
   this specified torus. Apply lem-sfb-reductive-borel-pair-structure and
   lem-sfb-semisimple-roots-span to its reduced based root datum. Transport back
   the integer data using step 2. Lemma lem-sfb-root-datum-lattice-embedding gives
   the finite-index inclusions Q(roots) <= X <= P(roots).
4. Suppose X = P. Base change a surjective finite-central-kernel cover q to F.
   A nonzero coordinate vector space remains nonzero after field extension, so
   surjectivity persists. Kernels are identity fibre products; their coordinate
   algebras remain finite-dimensional, and algebra-point centrality persists.
   Lemma lem-sfb-semisimple-central-isogeny-multiplicative gives faithful flatness.
   Use lem-sfb-central-isogeny-borel-root-compatibility to lift the Borel pair.
   By lem-sfb-isogeny-root-power-laws the character pullback h is injective with
   finite cokernel and identifies roots and coroot pairings.
5. Every inverse rational image of an upstairs character is integral on coroots,
   hence belongs to P = X. Thus h is onto. Centrality gives root exponents one,
   so lem-sfb-root-datum-isogeny-realization makes the actual q_F an isomorphism.
   Its coordinate map has zero kernel and cokernel after extension. Extending
   vector-space bases detects their vanishing over k, hence q is an isomorphism.
6. Conversely, if X differs from P, restrict the rational coroot functionals to P.
   They are integral by definition, and root reflections preserve P. Roots and
   coroots, reducedness and the simple-root base give a reduced based root datum
   on P in def-sfb-pinned-split-root-realization.
7. Lemma lem-sfb-pinned-split-root-classification realizes it over k. Its roots
   span, so lem-sfb-semisimple-roots-span gives geometric semisimplicity. Smooth
   affine finite type is realization data; connectedness descends from the
   geometric fibre. Apply lem-sfb-split-central-isogeny-lifting to X -> P for
   a finite faithfully flat central cover with kernel D_k(P/X).
8. Since P/X is nonzero and finite, k[P/X] has dimension |P/X| > 1, so this
   kernel is nontrivial and the cover is not an isomorphism. This contradicts
   the universal property and proves the converse. In rank zero V = X = P = 0;
   the forward argument still applies and the converse's strict case is absent. -/
theorem splitSemisimple_weightLattice_criterion
    {k : Type u} [Field k] [CharZero k]
    (H S : Grp (Over (Spec (.of k))))
    (hH : SolvableGroupStructure.IsAlgebraic H)
    (hHs : Smooth H.X.hom) (hHc : ConnectedSpace H.X.left)
    (hHss : IsSemisimpleGroupScheme
      ((MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj H).X)
    (i : S ⟶ H) (hi : IsClosedSubgroupScheme i.hom.hom)
    (hsplit : ∃ r : ℕ, Nonempty (S ≅ MultiplicativeType.splitTorus k r))
    (hmax : ReductiveTorusCentralizer.IsMaximalTorus
      ((MultiplicativeType.baseChange (K := AlgebraicClosure k)).map i))
    [IsCommMonObj S.X] [IsCommMonObj (StandardGroupSchemes.multiplicative k)]
    (a : ModObj S.X H.X)
    (ha : a.smul = (i.hom.hom ⊗ₘ 𝟙 H.X) ≫ GrpObj.conj H.X)
    (Φ : Finset (Additive (S ⟶ Grp.mk (StandardGroupSchemes.multiplicative k))))
    (P : RootDatum Φ
      (Additive (S ⟶ Grp.mk (StandardGroupSchemes.multiplicative k)))
      (Additive (Grp.mk (StandardGroupSchemes.multiplicative k) ⟶ S)))
    (hroot : ∀ α : Φ, P.root α = α.val)
    (hpair : ∀ (χ : Additive (S ⟶ Grp.mk (StandardGroupSchemes.multiplicative k)))
      (ν : Additive (Grp.mk (StandardGroupSchemes.multiplicative k) ⟶ S)),
      ν.toMul.hom.hom ≫ χ.toMul.hom.hom =
        (𝟙 (StandardGroupSchemes.multiplicative k)) ^ (P.toLinearMap χ ν))
    (hweights : ∀ χ : Additive (S ⟶ Grp.mk (StandardGroupSchemes.multiplicative k)),
      χ ∈ Φ ↔ χ ≠ 0 ∧ @TorusCharacterTangent.weightSpace k _ S H a χ.toMul ≠ ⊥) :
    (∀ (H' : Grp (Over (Spec (.of k)))),
      SolvableGroupStructure.IsAlgebraic H' → Smooth H'.X.hom →
      ConnectedSpace H'.X.left →
      IsSemisimpleGroupScheme
        ((MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj H').X →
      ∀ q : H' ⟶ H, Surjective q.hom.hom.left →
        IsFinite (GrpObj.ker q.hom.hom).hom →
        (∀ (A : Type u) [CommRing A] [Algebra k A]
          (x : StandardGroupSchemes.affine k A ⟶ GrpObj.ker q.hom.hom)
          (g : StandardGroupSchemes.affine k A ⟶ H'.X),
          (x ≫ GrpObj.kerι q.hom.hom) * g = g * (x ≫ GrpObj.kerι q.hom.hom)) →
        IsIso q) ↔
    ∀ v : ℚ ⊗[ℤ] Additive (S ⟶ Grp.mk (StandardGroupSchemes.multiplicative k)),
      (∃ χ : Additive (S ⟶ Grp.mk (StandardGroupSchemes.multiplicative k)),
        TensorProduct.mk ℤ ℚ _ 1 χ = v) ↔
      ∀ α : Φ, ∃ n : ℤ,
        (((Int.castAddHom ℚ).toIntLinearMap.comp (P.coroot' α)).liftBaseChange ℚ) v =
          (n : ℚ) := by
  sorry

end AlgebraicGeometry
