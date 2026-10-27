module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import Mathlib.CategoryTheory.Sites.Sheafification
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFpqcSheaf
import Sheaf.AlgebraicGeometry.ClosedPointField
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Representability
import Sheaf.AlgebraicGeometry.InvariantAffineDescentGluing
import WeilConjectures.AlgebraicGeometry.InvariantAffineNeighbourhoods
import Sheaf.AlgebraicGeometry.FreeFlatGroupSpaceQuotient
import Sheaf.AlgebraicGeometry.AlgebraicSpaceDenseSchemeOpen
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFourPropertyFppfDescent
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFppfCoveringCalculus
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Homogeneous quotients by closed subgroup schemes

Source: Milne, Algebraic Groups (2017), Definition 5.20 and Theorem 5.28,
printed pp.104–105; Proposition 5.25; Appendix B, B.36–B.37, pp.604–606.
Finite presentation: Stacks Project, Tag 01TX.
(blueprint: lem-sfb-algebraic-group-homogeneous-quotient).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

/-- A separated finite-type group scheme modulo an arbitrary closed subgroup has a
separated finite-type scheme quotient with flat surjective finitely presented projection,
coset fibres on all test schemes, and fpqc local lifts.

Source: Milne, Algebraic Groups (2017), Definition 5.20, Theorem 5.28 and Proposition 5.25,
printed pp.104–105; Appendix B, B.36–B.37, pp.604–606; Stacks Project, Tag 01TX.
(blueprint: lem-sfb-algebraic-group-homogeneous-quotient).

Proof plan (the twelve steps of the DAG):
1. The closed subgroup L is finite type over k, hence flat and locally finitely presented.
   Regard schemes as algebraic spaces (def-trf-scheme-algebraic-space) and use
   pqf-lem-lft-fp-locnoeth. The action l · g = g j(l)⁻¹ is free by cancellation.
2. Apply lem-sfb-free-flat-group-space-quotient to get F = G/L and a flat surjective
   locally finitely presented map q. Its kernel pair is G × L via (g,l) ↦ (g,g j(l)).
   Left translations descend through def-weil-pbc-sheafification and give a G-action.
3. The kernel-pair embedding is the inverse image of the closed subgroup under
   (a,b) ↦ a⁻¹b. Use lem-sfb-space-fppf-covering-calculus and
   lem-sfb-space-closed-immersion-fppf-descent to conclude that F is separated.
4. Apply lem-sfb-representable-lft-fppf-source-descent for local finite type.
   Lemmas lem-sfb-stack-point-topology-flat-lfp-open and lem-sfb-space-qcqs-permanence
   give quasi-compactness of F, and quasi-compactness and quasi-separatedness of q.
5. Over each finite subfield K of an algebraic closure, form the union V[K] of scheme
   opens in F_K. It is a scheme by lem-pc-schemes-criterion, using
   lem-a1-algebraic-space-fpqc-sheaf. Translations preserve it and field extension
   carries it into the corresponding union after extension.
6. Use lem-sfb-quasiseparated-space-dense-scheme-open to find a nonempty scheme open.
   A closed point of its inverse image has finite residue field by
   lem-kun-closed-point-field. Translate its image to show q(G(K)) ⊆ V[K].
7. Apply lem-sfb-finite-extension-open-exhaustion to q_K⁻¹(V[K]). For some finite K,
   this is all of G_K, hence F_K is a scheme Y. Base change preserves separatedness
   and finite type by lem-sfb-space-four-property-fppf-descent and covering calculus.
8. The orbit map of the G_K-action on Y is q_K. Apply
   lem-sfb-homogeneous-scheme-finite-set-affine: every finite subset has an affine open.
9. The identification Y = F_K supplies def-pd-descent-datum. Apply
   lem-pd-invariant-affine-neighbourhoods and lem-pd-invariant-affine-descent-gluing
   over the finite faithfully flat extension to descend Y to a k-scheme X.
10. The fpqc equalizers of X and F agree after extension to K, so
    lem-a1-algebraic-space-fpqc-sheaf identifies them. Transport q and its properties.
11. Evaluate the kernel-pair formula on every k-scheme T. Its fibres are exactly the
    right L(T)-cosets, equivalently a⁻¹b is in the image of j on T-points.
12. For x : T → X, take T' = T ×_X G. Its projection to T is flat, surjective and
    quasi-compact, hence an fpqc cover in def-weil-pbc-fpqc-covering, using
    lem-sfb-space-fppf-covering-calculus and lem-sfb-space-quasicompact-fppf-local.
    The other projection lifts x on this cover, even when T is not affine. -/
theorem exists_homogeneousQuotient (k : Type u) [Field k]
    (G L : Over (Spec (.of k))) [GrpObj G] [GrpObj L]
    [IsSeparated G.hom] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    (j : L ⟶ G) [IsClosedSubgroupScheme j] :
    ∃ (X : Over (Spec (.of k))) (p : G ⟶ X),
      IsSeparated X.hom ∧ LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom ∧
      Flat p.left ∧ Surjective p.left ∧ LocallyOfFinitePresentation p.left ∧
      QuasiCompact p.left ∧ QuasiSeparated p.left ∧
      (∀ (T : Over (Spec (.of k))) (a b : T ⟶ G),
        a ≫ p = b ≫ p ↔ a⁻¹ * b ∈ Set.range (fun l : T ⟶ L ↦ l ≫ j)) ∧
      (∀ (T : Over (Spec (.of k))) (x : T ⟶ X),
        ∃ (I : Type u) (T' : I → Over (Spec (.of k))) (f : ∀ i, T' i ⟶ T),
          Presieve.ofArrows (fun i ↦ (T' i).left) (fun i ↦ (f i).left) ∈
            Scheme.fpqcPrecoverage T.left ∧
          ∀ i, ∃ g : T' i ⟶ G, g ≫ p = f i ≫ x) := by
  sorry

end AlgebraicGeometry
