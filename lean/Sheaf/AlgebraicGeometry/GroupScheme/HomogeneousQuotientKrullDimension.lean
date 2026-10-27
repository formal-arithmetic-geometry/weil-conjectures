module

public import Mathlib.CategoryTheory.Monoidal.Grp
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousQuotient
public import Mathlib.Topology.KrullDimension
import WeilConjectures.Mathlib.Topology.KrullDimension
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.DimensionExtension
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.SurjectiveFlatGlobalDimension
import Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Topology.NoetherianSpace
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Krull dimension of an arbitrary algebraic homogeneous quotient

Source: Milne, Algebraic Groups (2017), Proposition 5.23, printed p.104;
Propositions 5.24–5.25; Stacks Project, Tags 02FY, 06FE and 0AFE.
(blueprint: lem-sfb-homogeneous-quotient-krull-dimension).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

/-- The topological Krull dimension of a separated finite-type group scheme is the
sum of the dimensions of a closed subgroup and its represented fpqc homogeneous quotient.
All three dimensions are finite nonnegative integers. The quotient hypotheses are exactly
those supplied by `exists_homogeneousQuotient`; no smoothness, reducedness, connectedness,
normality or affineness is required.

Source: Milne, Algebraic Groups (2017), Proposition 5.23, printed p.104, with
Propositions 5.24–5.25; Stacks Project, Tags 02FY, 06FE and 0AFE.
(blueprint: lem-sfb-homogeneous-quotient-krull-dimension).

Proof:
1. By lem-sfb-algebraic-group-homogeneous-quotient, q is flat, surjective and finitely
   presented, hence locally of finite type (def-sbc-locally-finite-presentation).
   The closed immersion j identifies inverse images of a finite affine cover of A with
   spectra of quotients of finitely generated k-algebras (def-weil-closed-immersion).
   Thus L is finite type (def-weil-finite-type-morphism). The affine rings of A, L and X
   are Noetherian (lem-wf-affine-noetherian-components), giving local Noetherianity
   (pqf-def-locnoeth). Their dimensions are finite (lem-kun-dimension-finite-type).
   Their identities and q(e_A) give points, so their dimensions are natural numbers.
2. For a in A, take K = kappa(a) and the canonical g : Spec K → A. Put v = qg and
   F = A ×_X Spec K, pointed by (g,1). The map L_K → F, h ↦ gh, is an isomorphism:
   for b : F → A and r : F → Spec K, qb = qgr, so the test-scheme coset criterion
   factors (gr)⁻¹b uniquely through j. This gives the inverse F → L_K. Cancellation
   and the injectivity of j verify both composites, including on nonreduced schemes
   (def-sc-group-scheme, def-sc-group-scheme-subgroup, def-pc-fibre-product,
   def-pc-scheme-fibre, lem-sfb-algebraic-group-homogeneous-quotient).
3. L_K is a finite-type K-group scheme by lem-sfb-finite-type-composition-base-change.
   By lem-sfb-field-groupoid-constant-local-dimension at its identity, its local
   topological dimension there is dim L_K. By lem-kun-dimension-extension this is
   dim L = d. The pointed isomorphism of step 2 preserves irreducible closed chains
   in open neighbourhoods, so the local dimension of F at (g,1) is d
   (def-kun-topological-dimension-at-point, def-kun-topological-krull-dimension).
4. Apply lem-sc-fibre-dimension-after-base-change to q and v. The fibre of
   F → Spec K is F itself, so the ordinary fibre of q at q(a) has local topological
   dimension d at a. Here K is kappa(a); no kappa(q(a))-rational lift is assumed.
5. Apply lem-per-surjective-flat-global-dimension to q, using local Noetherianity,
   flatness, local finite type, surjectivity, nonempty X, and step 4. It gives
   dim A = dim X + d. Commutativity gives dim A = dim L + dim X. The natural-number
   values from step 1 prove the finiteness and nonnegativity clause. -/
theorem topologicalKrullDim_homogeneousQuotient (k : Type u) [Field k]
    (A L : Over (Spec (.of k))) [GrpObj A] [GrpObj L]
    [IsSeparated A.hom] [LocallyOfFiniteType A.hom] [QuasiCompact A.hom]
    (j : L ⟶ A) [IsClosedSubgroupScheme j]
    (X : Over (Spec (.of k))) (q : A ⟶ X)
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]
    [QuasiCompact q.left] [QuasiSeparated q.left]
    (hcoset : ∀ (T : Over (Spec (.of k))) (a b : T ⟶ A),
      a ≫ q = b ≫ q ↔ a⁻¹ * b ∈ Set.range (fun l : T ⟶ L ↦ l ≫ j))
    (hlift : ∀ (T : Over (Spec (.of k))) (x : T ⟶ X),
      ∃ (I : Type u) (T' : I → Over (Spec (.of k))) (f : ∀ i, T' i ⟶ T),
        Presieve.ofArrows (fun i ↦ (T' i).left) (fun i ↦ (f i).left) ∈
          Scheme.fpqcPrecoverage T.left ∧
        ∀ i, ∃ g : T' i ⟶ A, g ≫ q = f i ≫ x) :
    topologicalKrullDim A.left = topologicalKrullDim L.left + topologicalKrullDim X.left ∧
      ∃ a l x : ℕ, topologicalKrullDim A.left = (a : WithBot ℕ∞) ∧
        topologicalKrullDim L.left = (l : WithBot ℕ∞) ∧
        topologicalKrullDim X.left = (x : WithBot ℕ∞) := by
  sorry

end AlgebraicGeometry
