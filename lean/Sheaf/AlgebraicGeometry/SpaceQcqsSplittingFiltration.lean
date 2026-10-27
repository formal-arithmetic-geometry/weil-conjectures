module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.ReducedAlgebraicSpace
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Sheaf.AlgebraicGeometry.SpaceSeparatedLqfPermanence
import Sheaf.AlgebraicGeometry.AdmissibleFreeFiniteQuotient
import Sheaf.AlgebraicGeometry.ReducedClosedSubspaceSupport
import Sheaf.AlgebraicGeometry.SpaceSeparatedEtaleDiagonalComplement
import Sheaf.AlgebraicGeometry.SpaceEtaleSourceAtlasDetection
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints

/-! # Finite splitting filtrations of qcqs algebraic spaces

Source: Stacks Project, Decent Algebraic Spaces, Tag 07ST
(lemma-filter-quasi-compact-quasi-separated), using Tag 0BBN; Limits of Algebraic
Spaces, Tag 07SU (proposition-approximate), first proof paragraph
(blueprint: lem-sfb-qcqs-space-splitting-filtration).

The source's positive length is `m + 1`. Open indices run from `0` (the whole space)
to `m + 1` (empty), and chart indices from `0` to `m`. Reduced closed strata are
specified by their closed immersions and point supports, without choosing an atlas
or a noncanonical representative of the unique reduced closed subspace.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A qcqs algebraic space over the integers has a finite decreasing filtration by
quasi-compact open subspaces with quasi-compact separated scheme charts, each a
representable surjective etale neighborhood of its reduced closed stratum. The last
chart is an isomorphism, so the last nonterminal open is itself such a scheme.
The empty space is included, and `m + 1` is always a positive length.

Source: Stacks Project, Tags 07ST, 0BBN and 07SU, first proof paragraph
(blueprint: lem-sfb-qcqs-space-splitting-filtration).

Proof:
1. Choose an affine surjective etale atlas A -> X by
lem-sfb-qc-space-affine-etale-atlas. The uniform geometric fibre bound of
lem-sfb-space-qc-etale-fibre-bound gives d; use positive length max(1,d).
For empty X take the empty atlas and empty opens and charts.
2. By lem-sfb-etale-atlas-distinct-tuple-geometry, the scheme W_p of ordered distinct
p-tuples in A over X is quasi-compact and separated. Its map to the affine absolute
power of A is separated and locally quasi-finite, also after restriction by
lem-a1-space-separated-lqf-permanence. Thus lem-sfb-separated-lqf-affine-finite-set
puts each finite symmetric-group orbit in an affine open. The coordinate action is
free: a nontrivial permutation fixing a tuple equates distinct coordinates on any
nonempty component. Apply lem-sfb-admissible-free-finite-quotient to obtain the
quasi-compact separated scheme V_p = W_p / S_p and its finite etale surjection.
3. Descend W_p -> X through the quotient. By clause (1) of
lem-trf-space-etale-source-atlas-detection this map V_p -> X is representable etale.
By lem-a1-space-etale-open-image its image U_p is open, the factor V_p -> U_p is
representable surjective etale, and U_p is quasi-compact.
4. At an algebraically closed point with atlas fibre E, quotient geometric points
identify the fibre of V_p with the p-element subsets of E. Thus membership in U_p
means |E| >= p. Point membership can be tested after extension by
lem-a1-space-point-open-calculus. A nonempty geometric fibre has a rational point:
lem-trf-space-representable-etale-scheme-tests makes it an etale scheme, and
lem-weil-pbc-etale-fibre-discrete-separable-points together with
lem-weil-pbc-alg-closed-finite-extension-trivial splits it into rational points.
The cardinality criterion gives the nested opens, U_1 = X and the terminal empty
open; the open-subfunctor order follows from lem-a1-space-point-open-calculus.
5. Give each closed complement its unique reduced structure by
lem-sfb-space-reduced-closed-support. Its chart pullback is surjective etale by
lem-trf-space-representable-etale-scheme-tests and separated: its relative diagonal
is a base change of the absolute closed diagonal of V_p, using
lem-weil-pbc-closed-immersion-base-change. Its geometric fibre has one point, the
unique p-element subset of a p-element set. Apply
lem-sfb-space-separated-etale-diagonal-complement to obtain the stratum isomorphism.
6. The last stratum has full support in the last nonterminal open. Reduction does
not change field-valued points, since field maps kill nilpotents on affine charts.
Hence the same singleton-fibre and separatedness argument applies to the last
surjective etale map itself. A second application of
lem-sfb-space-separated-etale-diagonal-complement makes it an isomorphism.
-/
theorem exists_qcqs_splitting_filtration
    (X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))
    (hqc : CompactSpace (Point X.obj.obj)) (hqs : IsAbsolutelyQuasiSeparated X) :
    ∃ (m : ℕ) (U : Fin (m + 2) → OpenSubspace X)
      (V : Fin (m + 1) → Over (Spec (.of (ULift.{u} ℤ))))
      (f : ∀ p : Fin (m + 1), yoneda.obj (V p) ⟶ (U p.castSucc).val.toFunctor)
      (T : Fin (m + 1) → AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))
      (t : ∀ p : Fin (m + 1), (T p).obj.obj ⟶ (U p.castSucc).val.toFunctor),
      (U 0).val = ⊤ ∧ (U (Fin.last (m + 1))).val = ⊥ ∧
      (∀ p : Fin (m + 1), U p.succ ≤ U p.castSucc) ∧
      (∀ p : Fin (m + 2), CompactSpace (Point (U p).val.toFunctor)) ∧
      (∀ p : Fin (m + 1), CompactSpace (V p).left ∧ (V p).left.IsSeparated ∧
        IsEtale (f p) ∧ IsSurjective (f p)) ∧
      (∀ p : Fin (m + 1),
        IsRepresentableWith (fun _ _ q ↦ IsClosedImmersion q.left) (t p) ∧
        IsReduced (T p) ∧
        pointImage (t p) =
          mapPoint (U p.castSucc).val.ι ⁻¹' (pointImage (U p.succ).val.ι)ᶜ ∧
        IsIso (Limits.pullback.snd (f p) (t p))) ∧
      IsIso (f (Fin.last m)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
