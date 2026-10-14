## What changed

Closed `AlgebraicGeometry.exists_affineTildeDerivedTensorMate` by composing a universal
source transport equation with ordinary affine exchange and cancelling the supplied
invertible pullback counit. The pure-tensor formula for the coefficient complex map is
proved from the existing model fields. Two new modules state strictly separate steps:
the source comparison with its square transport, and the ordinary coefficient exchange.
The former gives one isomorphism for every square and never mentions the coefficient
complex map; the latter never mentions the derived tensor model or source isomorphism.

Refactored the existing concrete `affineTildeDerivedTensorToPushforward` definition into
its named concrete counit prefix and ordinary tail. Its signature and arrow are unchanged;
all factors of the original construction are retained, up to category associativity.
The private proved factorization API is used in the final equality. Its public dependency
is recorded in `coord/changes/affine-tilde-tensor-raw-factorization.md`.

## Proved and sorry left

Closed one original hole: `AlgebraicGeometry.exists_affineTildeDerivedTensorMate`
(node `lem-pc-affine-tilde-derived-tensor-mate`). No sorry remains in the item.
Two lower holes are added, so this is a decomposition, not a sorry-free proof:

- `AlgebraicGeometry.exists_affineTildeTensorSourceComparison`
  (`lem-pc-affine-tilde-tensor-source-comparison`): source identification via a K-flat
  resolution, actual affine derived pushforward-unit invertibility, and transport of
  the source counit equation through pinned derived-unit compatibility.
- `AlgebraicGeometry.affineTildeTensorOrdinaryExchange`
  (`lem-pc-affine-tilde-tensor-ordinary-exchange`): ordinary exchange identified on
  tensor generators and transported through localization and the right-derived unit.

Both statements include zero rings and zero complexes. Neither assumes the spectrum
square is cartesian. The source step works for unbounded complexes without requiring
the R-restriction of M to be K-flat. The ordinary step needs no K-flat or quasi-coherent
hypothesis. The original target's K-flat and quasi-coherent binders are unchanged.

## No longer needed

No original public import is removed: each supplies definitions or the existing signature.
The inherited attempt removed the redundant direct DerivedBaseChangeUnitCompatibility import
from ordinary exchange, and relocated the AffineBaseChangeTildeRepresentative import
from source comparison to ordinary exchange. These do not globally prune either module.
The parent's old direct proof dependencies are replaced by the two new steps and the
model/representative definitions. The following no longer occur directly in its proof:
`lem-pc-affine-derived-pullback-tensor-tilde`, `lem-sc-qcoh-acyclic-derived-pushforward-cohomology`,
`lem-pc-affine-morphism-hi`, `lem-pc-source-module-kflat-resolution`,
`lem-weil-pbc-tilde-pullback-base-change`,
`lem-pc-affine-tilde-pushforward-cohomology-normalization`, and
`lem-pc-derived-base-change-unit-compatibility`.

Resolution and tilde/pullback normalization remain below the source step; ordinary tilde
and pushforward comparisons remain below the exchange step. These are moved dependencies,
not globally pruned modules. The broad homology-only acyclic-pushforward comparison and
higher-direct-image vanishing are replaced in the source proof plan by the existing
`lem-pc-affine-pushforward-resolution-quasi-iso`.
The exploratory `AffinePushforwardResolutionQuasiIso` proof import, private affine-unit
helper and local scheme-module category instances are removed from the main module. No global pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The existing plan gives object comparisons and homology formulas, but lacks the exact
source counit transport and ordinary exchange equations needed in these coordinates.
These are stated separately, with complete proof descriptions. The source equation
quantifies over all commutative squares after choosing its source isomorphism, so the
isomorphism remains independent of the coefficient maps. The two steps are strictly
parts of the argument; the target proof actually composes them and cancels the counit.

The sandbox contained a compiling decomposition and several failed exploratory versions.
The failed explorations repeatedly unfolded the chosen derived functor and category bridges.
The final route names the
concrete prefix and tail and includes square transport in the source step. No new
module is introduced merely to evade the compilation limit. All three modules compile
within the existing 60-second limit. No target signature was changed. The unchanged direct caller
`AffineTildeDerivedTensorHomologyCoordinates` compiles against the delivered definition.

The resumed worker checked both intermediate statements and the proved generator formula,
repeated LeanFinder, Loogle and grep searches, and removed an unused local functor binding
from the new source statement. The main proof still composes two equalities and cancels
the direct image of the invertible counit. A narrower source-normalization statement was
explored in scratch files but is not delivered: the generic compatibility application
required expensive category/counit unfolding. The delivered source statement includes
that transport step, separate from ordinary coefficient exchange.

Verification: all three delivery files compiled (44.2, 25.8 and 42.4 seconds).
The direct caller compiled unchanged (8.3 seconds). Two dry runs passed their axiom probes
and preflight, with only the independent second reading still to be supplied.
The raw-map meaning was checked by comparing its concrete factors: the new prefix adds
only reflexive equality transport and groups the first two factors; the new tail retains
exactly the original last three factors. No formal old/new equality theorem is claimed.
The unit record has no realized nodes, and its semicontinuity route is not replaced.

The source descriptions were checked against
[Stacks 08DW](https://stacks.math.columbia.edu/tag/08DW), which identifies affine derived
pullback with derived scalar extension, and
[Stacks 08HY](https://stacks.math.columbia.edu/tag/08HY), which constructs the mate for
arbitrary commutative squares of ringed spaces.

## New nodes

`lem-pc-affine-tilde-tensor-source-comparison` is the universal affine source transport
step. It follows the K-flat resolution argument of Stacks 06Y6 and 08DW, affine
pushforward of a K-injective resolution, and pinned derived-unit compatibility 08HY.
It does not identify ordinary exchange with the coefficient complex map.

`lem-pc-affine-tilde-tensor-ordinary-exchange` is the termwise generator calculation,
localization and naturality of the derived pushforward unit. It uses the unit-normalized
tensor/tilde and affine pushforward comparisons (01I9, 06Y6 and 08HY); the target
representative normalization is only cancellation of its supplied counit.

Change record: `coord/changes/affine-tilde-tensor-raw-factorization.md`.


## Earlier second reading (a previous round; superseded)

1. **Interfaces and definitions — PASS.** Compared the delivered item against the
   repository with diff and checked all five existing declaration signatures byte for
   byte. All are identical. Only the raw-map definition changes, as declared in
   `affine-tilde-tensor-raw-factorization.md`. Its original five factors are retained:
   the new prefix inserts equality transport along a reflexive defining equality and
   groups the first two factors; the ordinary tail is exactly the last three factors.
   Proof irrelevance makes that transport the identity, and associativity identifies
   the composites. No new hypothesis or weaker conclusion is hidden in this change.
   The direct caller `AffineTildeDerivedTensorHomologyCoordinates` was compared with
   the repository and compiled unchanged against refreshed reviewed artifacts.
2. **Kernel and holes — PASS.** Independently compiled all three delivery modules
   through lcompile.py: source 47.8 s, ordinary exchange 31.3 s, item 49.6 s.
   Text inspection found exactly the two reported named theorem sorries, no definition
   sorry and none of the forbidden declaration forms. Scratch #print axioms checks
   show only propext, Classical.choice and Quot.sound for all three new concrete
   constructions, the raw arrow and coefficient map; the two lower statements and
   assembled mate additionally use sorryAx. The chosen tensor/tilde isomorphism is
   obtained from the already proved exists_tensorPullback_tilde_iso, not an arbitrary
   witness of an unproved existence theorem.
3. **Split statements — PASS as decomposition.** Read both complete signatures,
   docstring proofs and nodes. The source theorem stops at ordinary exchange and
   contains no coefficient map or target representative; the ordinary theorem has no
   derived tensor model or existential source comparison. They are separate strict
   parts of the parent argument, not renamed restatements. Checked zero complexes,
   zero rings, identity squares and non-cartesian coefficient squares. Resolving
   res_R M avoids assuming it is K-flat, while termwise tilde M is quasi-coherent,
   as required by affinePushforward_resolution_quasiIso. Checked the literature
   descriptions against [08DW](https://stacks.math.columbia.edu/tag/08DW),
   [08HY](https://stacks.math.columbia.edu/tag/08HY) and
   [0AVW](https://stacks.math.columbia.edu/tag/0AVW).
   Repeated LeanFinder, Loogle and Mathlib grep searches using localization/universal
   transformation and adjunction mate terminology. Hits included leftDerivedNatTrans_fac,
   leftDerived_fac_app, leftAdjointUniq and homEquiv naturality; none provides either
   full affine normalization equation. Also searched the upstream module library and
   Sheaf's ordinary tensor coordinates and affine comparisons. Those provide pieces,
   not duplicates. Neither remaining hole has a short complete proof from these APIs.
4. **Route and pruning — PASS.** Read the final assembly top down: the model fields
   prove the pure-tensor formula; source transport and ordinary exchange give two
   equalities which are composed; cancellation uses precisely the supplied invertible
   counit. Each public import supports a public signature or concrete definition body;
   the two added public imports are required by the refactored public raw definition,
   not solely by its theorem proof. The report lists all seven retired direct proof
   dependencies and distinguishes moved dependencies from global pruning. The unit
   sk-thm-picard-semicon has empty realized lists; its statement and route are untouched.
5. **Nodes — PASS.** The existing node changes only proof, proof_deps and proof_origin.
   The new nodes have the required source, searches, creation, blueprint, chapter/unit
   and Lean records. Both recorded Lean signatures match verbatim. For each of the
   three nodes, proof_deps is exactly the union of the uses of its proof steps. The
   parent steps follow the actual tensor-generator proof, equality composition and
   counit cancellation.

Changes in this reading: added this independent review and refreshed scratch validation.
No delivered Lean repair was needed in that reading; the later reviewer-requested
node repairs are recorded below. The attempted scratch formal old/new raw
map equality still encounters instance-transparency normalization; it is not delivered
or claimed as a proved theorem. The factor-by-factor semantic check above is the basis
for approving that refactor. One original hole is closed and two lower holes are added:
net minus one hole, with no global module pruning and no claim of a sorry-free proof.

Repair of reviewer X-7ade3's return (head 7ade39e6e):

- **B2 corrected.** The source-comparison node now states every algebra structure,
  the sheaf and module derived-category assumptions, and the arbitrary model m.
  It introduces f and g from the algebra structures and p and fprime from phi and
  psi, and states their commutative-square equation explicitly. Added
  `def-pc-derived-category` to stmt_deps. The Lean theorem is unchanged.
- **C4 corrected.** Source-comparison proof step 2 explicitly obtains tilde P's
  K-flatness from `lem-pc-affine-tilde-kflat` and invertibility of the fixed
  g-pullback counit from the K-flat counit clause of `def-pc-derived-pullback`.
  Both IDs are added to that step's uses and to proof_deps; the existing affine
  comparison dependency remains. Checked proof_deps against the union of uses.

These corrections repair the natural-language statement and dependency accounting;
all delivered Lean files and their signatures remain unchanged.


## Second reading by H2

1. **Interfaces — PASS.** Independently diffed the item against the repository and
   mechanically compared the five existing declaration signatures: all are byte for
   byte identical. The sole definition refactor is declared in the change record.
   Checked its factors against the original: the counit prefix inserts only
   eqToHom of a reflexive equality, followed by the original first two factors;
   the ordinary target map retains the original last three factors. Category
   associativity identifies their composite. The original direct caller
   AffineTildeDerivedTensorHomologyCoordinates compiled unchanged against the
   freshly compiled delivery overlay (4.0 s). No target meaning changes.
2. **Proof and axioms — PASS as decomposition.** Compiled the delivery in import
   order using lcompile.py: source comparison 48.1 s, ordinary exchange 28.8 s,
   item 44.9 s. Text inspection found precisely the two reported named theorem
   sorries and no forbidden declaration forms or definition holes. A fresh scratch
   axiom probe using this delivery's .lbuild showed only propext, Classical.choice
   and Quot.sound on the ordinary source iso, derived counit prefix, ordinary
   target map, raw arrow and coefficient map. The two lower statements and
   assembled mate additionally use sorryAx. The chosen ordinary tensor/tilde iso
   comes from the proved exists_tensorPullback_tilde_iso, not from an unproved
   arbitrary existence claim.
3. **Split statements — PASS after node repair.** Read both full signatures,
   docstring proofs and nodes. Read Stacks 08DW(2) (affine derived scalar extension),
   08HY (mate for an arbitrary commutative square) and 0AVW (unbounded affine
   pushforward), and the library's affinePushforward_resolution_quasiIso and
   unit-normalized exists_tensorPullback_tilde_iso. Resolving res_R M avoids
   assuming M is K-flat over R; termwise associated sheaves supply exactly the
   quasi-coherent hypothesis needed by the pushforward resolution theorem.
   Source comparison stops at ordinary exchange; ordinary exchange contains no
   derived tensor model or existential source comparison. The coefficient formula
   determines k on tensor generators, and t.hom followed by the p-counit cancels
   that counit's inverse. Checked identity squares, arbitrary non-cartesian
   commutative squares, zero complexes and zero rings: none requires flatness of
   phi or psi, and the zero cases reduce to zero-object equations. Repeated
   LeanFinder with universal-derived-counit terminology, Loogle with
   homEquiv_naturality_right, and Mathlib grep with tensorObj_map_tmul and adjunction
   naturality; also searched both local Lean roots and the source checkout.
   Hits give scalar counit and sheaf adjunction formulas, but neither complete
   affine normalization equation. No short closure of a lower hole was found.
   Added the omitted sheaf-derived-category assumption and its definition citation
   to the ordinary-exchange node's natural-language statement; Lean is unchanged.
4. **Route and pruning — PASS.** Read the parent proof top down: the model fields
   prove its tensor-generator formula, the two lower equations are composed, and
   cancellation uses exactly the supplied invertible counit. All public imports
   serve public statements or concrete definition bodies. The report lists every
   retired original direct proof dependency (seven), distinguishing relocation
   from pruning. sk-thm-picard-semicon has empty realized lists; its recorded
   statement and route are untouched. No global module pruning is claimed.
5. **Nodes — PASS after repair.** The parent changes only proof, proof_deps and
   proof_origin. Both new recorded Lean signatures match the source verbatim;
   each node's proof_deps is exactly the union of its steps' uses. Checked the
   prior B2/C4 repair: source comparison now records the arbitrary model and all
   category assumptions, cites affine-tilde K-flatness for tilde P and the
   K-flat counit clause of derived pullback. The ordinary node now records its
   category assumption too. Required creation, source, searches, blueprint,
   chapter/unit and Lean fields are present. Parent steps match the actual
   generator calculation, equality composition and counit cancellation.

Changes in this second reading: repaired only the ordinary-exchange node's omitted
category assumption/citation and appended this independent review; no Lean changes.
Closed one original named hole and added two strictly lower named holes, as listed
above: decomposition, net minus one hole; no globally pruned module.
