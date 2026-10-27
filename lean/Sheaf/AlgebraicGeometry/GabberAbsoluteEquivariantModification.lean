/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q70
-/
module

public import Sheaf.AlgebraicGeometry.GabberModificationData
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Product
import WeilConjectures.RingTheory.StrictHenselizationFaithfullyFlat
import WeilConjectures.RingTheory.StrictHenselizationNoetherian
import WeilConjectures.RingTheory.StrictHenselizationRegular
import Sheaf.AlgebraicGeometry.AmpleRestrictClosedImmersion
import Sheaf.AlgebraicGeometry.FreeCharacteristicRegularBoundary
import Sheaf.TraceFormula.LogRegularDivisorialStructure
import Sheaf.AlgebraicGeometry.CoordinateBlowupBranchDrop
import Sheaf.AlgebraicGeometry.PermissibleBoundaryPreservation
import Sheaf.TraceFormula.ProjQcOpenTwistAmple
import Sheaf.AlgebraicGeometry.ProjectiveBundleToHProjective
import WeilConjectures.RingTheory.CompletionRegularLocal
import WeilConjectures.RingTheory.FlatUnderRegular

/-! # The absolute equivariant Gabber modification

Source: ILO, Travaux de Gabber, VIII Theorem 1.1, 4.1.1--4.2.13, 5.3.8--5.5.5,
Theorem 5.6.1, pp. 85, 117--130; X 1.3--1.4, pp. 139--141
(blueprint: lem-per-gabber-absolute-equivariant-modification).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace AlgebraicGeometry.GabberModification

/-- There is one simultaneous choice of the four-stage normalized modification and of its
auxiliary-boundary-independent fourth-stage procedure, with all the asserted output clauses.
Source: ILO VIII 1.1, 4.1.1--4.2.13, 5.3.8--5.5.5, 5.6.1; X 1.3--1.4
(blueprint: lem-per-gabber-absolute-equivariant-modification).

Proof plan from the node:

1. Fix the saturated fan resolution rule once. Apply the general log-regular regularization tower
to (X,M). It is equivariant because it is compatible with automorphisms; it is a normalized blowup
tower with integral, regular, log regular source. The divisorial-structure theorem identifies the
log structure with the boundary complement and makes its triviality locus dense and regular. Thus
the tower is the identity off Z. The free-characteristic criterion identifies the resulting
boundary as a normal crossings divisor. This constructs stage one without an excellent affine base
assumption. Dependencies: lem-per-gabber-log-blowup-regularization, lem-trf-log-regular-
divisorial-structure, lem-trf-free-characteristic-regular-boundary.

2. For stage two, stratify the strict transform of the original boundary by the number of local
branches and blow its closed deepest stratum. Etale locally this is the ideal $(t_1,\ldots,t_d)$
when that stratum meets $d$ branches. The coordinate-branch-drop lemma gives the following
explicit calculation. On its $t_i$ chart the coordinates are $t_i$, $t_j/t_i$ for $j\ne i$ in that
set, and the remaining parameters. The strict transform has at most $d-1$ of these branch
equations; it has exactly that depth wherever it is nonempty at the old deepest stratum. The weak-
family blowup lemma applied to the local branch family and the permissible-boundary lemma preserve
regularity and normal crossings. Repeat on the strict transform: induction on its finite depth
removes it after finitely many steps. The final boundary consists only of accumulated exceptional
components and is strict normal crossings. Each center and its regular exceptional divisor are
invariant; distinct irreducible components of a regular divisor are disjoint, so translates of
each exceptional component are disjoint or equal. Subsequent equivariant blowups preserve this
property of strict transforms. Thus the final boundary is G-strict. These centers are boundary
monomial ideals; the displayed smooth charts identify the ordinary blowups with their saturated
log blowups. All centers lie over Z. Dependencies: lem-per-weak-boundary-family-blowup, lem-trf-
permissible-boundary-preservation, lem-trf-nc-coordinate-blowup-branch-drop.

3. On the regular pair now obtained, apply tame fixed-family transversality to the nontrivial
subgroup fixed subschemes $X^H$. It gives the regularity and boundary normal-crossings hypotheses
for every intersection, identifies intersections with fixed schemes of generated subgroups, and
identifies their union with the nonfree locus. The weak-family blowup lemma therefore produces a
finite permissible tower, blowing the union of minimal fixed intersections and then their strict
transforms. Conjugation permutes this family, and the lemma's permutation compatibility makes
every center and the tower G-equivariant. At its end every original fixed-scheme ideal is
invertible and every strict transform is empty. The new boundary is the inverse image of the old
boundary together with the nonfree locus. Off that boundary the tower is unchanged and the action
is free. Dependencies: lem-per-tame-fixed-family-transversality, lem-per-weak-boundary-family-
blowup.

4. For a geometric point with nonabelian inertia $H$, put $K=[H,H]\ne1$. The common G-equivariant
tower of the preceding step makes the ideal of $X^K$ invertible. The factorization clause of the
commutator blowup lemma factors that common tower through $\operatorname{Bl}_{X^K}X$ as an
H-equivariant map. Its inertia-drop clause makes every upstairs inertia over that point a proper
subgroup of H. Inertia over a point whose inertia was already abelian is a subgroup of it and
stays abelian. Repeat the whole finite minimal-family tower, not an isolated H-center blowup.
Along any geometric point lifted through successive rounds, every nonabelian inertia strictly
decreases in order. Orders are initially at most $|G|$, so at most $|G|$ rounds suffice uniformly.
The permissible and equivariant assertions from the preceding step persist; accumulated
exceptional divisors remain G-strict by the same component argument as in stage two. This
constructs stage three with abelian inertia and a free complement. Dependencies: lem-per-
commutator-blowup-inertia-drop, lem-per-weak-boundary-family-blowup.

5. Write $(W,B)$ for the stage-three pair. Choose the strict inert affine surjective etale cover
$U\to W$ of the rigidification-cover lemma, with enlarged very tame strict normal crossings
boundary $\overline B_U$. Its hypotheses hold: W is regular with G-strict strict normal crossings
boundary by stages two and three; W is Noetherian, separated and quasi-excellent because the
normalized-tower lemma, applied to the composite of the first three towers on the Noetherian
quasi-excellent normal separated X, makes every stage Noetherian and quasi-excellent and the
composite projective, hence separated; and inertia is abelian with free complement by stage three.
On the affine U the action is admissible. The very-tame log-quotient theorem gives a finite
quotient $q:U\to Q$, its invariant fs log regular structure with boundary $q(\overline B_U)$, and
the Kummer etale G-cover. This argument permits finitely many connected components of U.
Dependencies: lem-per-abelian-inert-rigidification-cover, lem-per-very-tame-log-quotient, lem-per-
normalized-blowup-tower-etale-descent.

6. Apply the same general regularization rule to the log regular quotient Q; no quasi-projective
or excellent-base hypothesis is needed. Obtain a saturated log blowup tower $Q'\to Q$ with Q'
regular and log regular; by the free-characteristic criterion its enlarged boundary is a normal
crossings divisor, possibly not strict, which is all the Kummer lemma requires. Pull it back in fs
log schemes along q. Kummer boundary restriction supplies stability under this pullback, the
normalized-cover identification, and log regularity. The invariant-boundary Q-Cartier lemma
applied to $B_U\subset\overline B_U$ shows that $D'=(h^{-1}q(B_U))_{\rm red}$ is a normal
crossings union of components in Q'. Off q(B_U), q has trivial inertia and is etale by the Kummer
lemma; regularity of this open quotient follows from the flat-under-regular lemma on local rings
of this surjective etale cover. The resolution is therefore its identity there. Consequently the
pulled-back cover is etale off D'. The boundary-restriction clause now removes the auxiliary
components: with boundary $q'^{-1}D'$ the source is fs log regular and very tame. That boundary is
exactly the inverse image of B_U. The normalized tower on U is the underlying tower of the pulled-
back saturated log blowups, retaining ordered centers as in the rigidified-comparison lemma.
Dependencies: lem-per-gabber-log-blowup-regularization, lem-per-kummer-boundary-restriction, lem-
per-very-tame-boundary-quotient-cartier, lem-per-rigidified-quotient-tower-comparison, lem-weil-
pbc-flat-under-regular, lem-trf-free-characteristic-regular-boundary.

7. First compare two enlarged rigidifying boundaries on a fixed admissible regular pair. For any
geometric point x take the completed strict local ring. Strict henselization and completion
preserve Noetherian regular local rings; strict henselization and completion are faithfully flat.
The rigidified-comparison lemma identifies the contracted pullback of either tower with its
complete-local construction. The complete-local rigidification-comparison lemma makes those
contracted towers equal. To recover their order before contraction, choose finitely many points S
meeting the image of every nonempty center in both original finite towers, and include their
finite G-orbits. On the disjoint union of the completed strict local schemes at S no stage
contracts. Compare also on its disjoint union with the completed strict local scheme at x. The
complete-local lemma applies to finite disjoint unions, so equality there respects the full
synchronized order. Restricting back to x gives equality before contraction. Faithfully flat
detection of ordered ideals in the descent lemma therefore proves equality of the two original
towers, including all centers. Dependencies: lem-per-rigidified-quotient-tower-comparison, lem-
per-complete-local-rigidification-comparison, lem-per-normalized-blowup-tower-etale-descent, lem-
sc-strict-henselization-regular, lem-weil-pbc-completion-regular-local, lem-sc-strict-
henselization-faithfully-flat, lem-weil-pbc-local-completion-faithfully-flat, lem-sc-strict-
henselization-noetherian.

8. For a strict inertia-preserving equivariant map of the original pairs, pull back a chosen
enlarged rigidification. The rigidified-comparison lemma gives the strict quotient map and
contracted scheme-pullback comparison. The preceding step removes the choice of auxiliary
boundary, so the comparison depends only on the original pairs; identities and composition hold
because they do so before forgetting the rigidification. Apply this to the two projections from
$U\times_WU$. The two boundary choices there give the same ordered tower, and their comparisons
agree on the triple fibre product. The normalized-tower descent lemma descends the centers and the
tower from U to W, with its G-action. Log regularity and very tameness can be checked on this
strict inert etale cover: characteristic monoids, strict local strata, and stabilizers are
identified by its strictness and inertia isomorphisms. The inverse-image boundary descends as
well. This is the global fourth stage. Dependencies: lem-per-rigidified-quotient-tower-comparison,
lem-per-normalized-blowup-tower-etale-descent.

9. Compose the four finite towers. Stages two and three have regular sources and hence are already
normal, so their ordinary blowups are normalized blowups with the same centers. The normalized-
tower lemma gives integrality, finite type, projectivity in the projective-bundle sense, and
preservation of the common dense open. In stages one and two the centers lie above Z; in stage
three they lie above the old boundary or nonfree locus; and stage four is the identity off the
stage-three boundary. Thus the composite is the identity over $X\setminus(Z\cup F)$ and its
boundary is exactly $b^{-1}(Z\cup F)$. The first-stage dense open is dense by the divisorial-
structure theorem; intersecting with the given free dense open remains dense since X is integral.
This also establishes birationality. Choosing the fixed resolution rule in the constructions gives
the simultaneous choice required in the statement. Dependencies: lem-per-normalized-blowup-tower-
etale-descent, lem-trf-log-regular-divisorial-structure.

10. Suppose finally that X has a locally closed immersion into $\mathbf P^n_B$ with B affine
Noetherian. Write it as a closed immersion into an open subscheme V of that projective space. V is
quasi-compact, since projective space over B is Noetherian. The Proj twisting lemma supplies an
ample invertible twist on V and closed-immersion restriction gives an ample invertible sheaf on X.
The projective-bundle-to-H-projective lemma now embeds $X^*$ as a closed subscheme of some
$\mathbf P^m_X$. The given locally closed immersion of X into $\mathbf P^n_B$ induces the same
type of immersion $\mathbf P^m_X\to\mathbf P^m_B\times_B\mathbf P^n_B$ (base change of its
open/closed factorization). Compose with the Segre closed immersion. This gives a locally closed
immersion of $X^*$ into a finite projective space over B, as asserted; finite type follows also
from finite type of the tower and the given X over B. No excellence hypothesis on B is used.
Dependencies: lem-trf-proj-qc-open-twist-ample, lem-trf-ample-restrict-closed-immersion, lem-trf-
projective-bundle-to-h-projective, lem-chow-segre.
-/
theorem exists_absolute_equivariant_modification :
    ∃ (P : FourthProcedure.{u, v})
      (choice : ∀ (G : Type v) [Group G] [Finite G] (X : FineSaturatedLogScheme.{u})
        (a : FSLogGroupAction G X), Input a → FourStage P G X a),
      ∀ (G : Type v) [Group G] [Finite G] (X : FineSaturatedLogScheme.{u})
        (a : FSLogGroupAction G X) (h : Input a), (choice G X a h).Output := by
  sorry

end AlgebraicGeometry.GabberModification
