## What changed

Added a `STATEMENT-DISPUTED` comment immediately before
`AlgebraicGeometry.perfect_hom_open_restricted_data_pinned`. All existing signatures,
definitions, proofs, visibility and imports remain byte for byte unchanged. The pinned and parent nodes'
proof and proof_origin now record why its proposed proof does not establish its Lean statement.
This is a statement-dispute delivery, not a proof or a decomposition.

The second reading removed the first worker's two new component lemmas and their two new nodes.
Their equations inherit the same false universal quantification over arbitrary `hB`. The
unchanged `PerfectHomOpenRestrictedDataExists.lean` was removed from the delivery set.

## Proved and sorry left

Holes closed: none (0 of the item's 1 original hole). Holes added: none. Net: 0.

The existing `AlgebraicGeometry.perfect_hom_open_restricted_data_pinned` remains `sorry`, node
`lem-pc-perfect-hom-open-restricted-data-pinned`, now explicitly disputed.
`AlgebraicGeometry.perfect_hom_open_restricted_data` already had a proof in the baseline;
it still relies on that disputed lemma and on the existing
`AlgebraicGeometry.perfect_hom_open_restricted_data_exists` (node
`lem-pc-perfect-hom-open-restricted-data-exists`). It is not a newly proved result.

Removed the proposed holes
`AlgebraicGeometry.perfect_hom_open_restricted_data_pinned_stage` and
`AlgebraicGeometry.perfect_hom_open_restricted_data_pinned_limit`; neither is delivered.
There are no split-off statements or new nodes in the final delivery.

## No longer needed

No baseline imports or modules were pruned. The parent's former direct proof dependencies
`lem-pc-derived-open-restriction-qcoh-iff`, `lem-pc-perfect-hom-push-pull-cocone`,
`lem-pc-restrict-derived-direct-image-open` and `lem-pc-ringed-spaces-derived-adjoint`
are not invoked by its current Lean proof and were removed from its direct proof_deps.
PerfectHomPushPullCocone remains a public import needed for the statements; the others
were not direct imports. This reports dependency bookkeeping, not modules pruned from the
import closure. The actual reduction uses the existing existence and pinned nodes instead. The two proposed component
nodes `lem-pc-perfect-hom-open-restricted-data-pinned-stage` and
`lem-pc-perfect-hom-open-restricted-data-pinned-limit` were removed before delivery; they were
never baseline proof dependencies. Both original proof dependencies of the pinned node remain
recorded as the ingredients of its unsuccessful plan.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: `perfect_hom_open_restricted_data_pinned` asserts the pinned stage and apex
identities for every independently supplied restricted datum `hB`. The fields of
`PerfectHomPushPullData` impose testing-object naturality and compatibility with transitions
and cocone legs, but impose no normalization tying `hB` to `h`.

Counterexample in ordinary derived categories: take a singleton index preorder, the constant
ring diagram at the rational field and its identity cocone, `Y = Spec(Q)` with identity `s`,
`B` the full open, and `Q` the structure sheaf in degree zero. Choose representing stage and
apex objects (isomorphic to `Q`), with identity transition and cocone maps. Full restriction
and pullback along these identity base changes are equivalences. Given a restricted datum,
postcompose every stage and apex Hom equivalence with the automorphism minus the identity
of the pulled-back `Q`. Equivalently negate all their values. Negation is a bijection;
bilinearity of composition preserves stageNatural and limitNatural, and additivity of
pullback and conjugation preserves stageMap and limitMap. QCoh fields are unchanged.
Thus this gives another valid datum on the very same restricted cocone.

Keep `h` and `a` fixed. The claimed right sides do not depend on `hB`, while the left sides
change sign. Full restriction is essentially surjective and full, and each Hom equivalence
is surjective, so one can choose a restricted testing object and map whose image is a
nonzero identity (up to the identity-pullback isomorphisms). In characteristic zero it differs
from its negative. Hence at least one of the two data violates the stage equation; the same
argument applies to the apex equation. This is an informal mathematical counterexample,
not a Lean-certified refutation. Empty opens and zero objects give singleton Hom sets and
hide the defect; the full open with nonzero `Q` exposes it.

Yoneda constructs a representing isomorphism from each natural equivalence; it does not
force two independently chosen equivalences on the same object to agree. The literature's
mate calculation can justify a particular compatible restricted datum constructed from `h`,
which is what the existential parent asks for. Mere existence followed by a theorem about
arbitrary `hB` does not supply that construction. Splitting the false conjunction into two
false component lemmas repairs nothing. No weaker replacement or additional hypothesis was
introduced. The parent requires a future genuine compatible construction.

## Second reading by N2

1. Interface: PASS. Compared both proposed modules with their repository versions. The
   existence module was identical. The proposed component declarations were the only added
   declarations and the conjunction assembly the only changed existing proof. After repair,
   removing the new dispute comment reproduces the item's entire baseline source exactly.
   No target, existing statement, definition or visibility changed; no change record is needed.
2. Proof/kernel: the original proposed set compiled locally with lcompile.py. The final
   item and scratch axiom check compiled too. The sole local sorry is the baseline pinned
   theorem. There is no axiom, unsafe, opaque, implemented_by, extern or sorry in a definition.
   The three constructed definitions, pinned theorem and parent were checked with
   `#print axioms`; only propext, Classical.choice, Quot.sound and inherited/local sorryAx
   occur. The parent's compiled proof is not evidence of closure: it uses the false open lemma.
3. Split-off statements: FAIL in the proposal, repaired by removal. Both new statements
   are false components of the universal pinned assertion, and their docstrings also lack
   the required complete proof in words. Inspected PerfectHomPushPullData's fields and
   PerfectHomTransport's formulas; searched lean/ for representing data and pinned identities
   and searched Mathlib via msearch grep for representing-equivalence natural automorphisms
   and loogle for Equiv.neg. Mathlib has Equiv.neg, confirming the elementary sign-twist
   bijection; there is no need to introduce either proposed obligation.
4. Route/pruning: PASS after repair. No imports were removed: PerfectHomPushPullCocone and
   DerivedMayerVietorisCanonicalData are needed publicly by the signatures and definitions;
   PerfectHomOpenRestrictedDataExists is already a plain proof-only import. Read
   dag/units/sk-thm-picard-semicon.json: its realized statement and step arrays are empty;
   no realized unit node or chapter/unit route was bypassed. All old direct proof dependencies removed from the parent node are reported, and the report lists both removed proposed nodes separately.
5. DAG: PASS after repair. Removed both proposed new nodes. The existing pinned node keeps
   its statement, statement dependencies and Lean signature; its proof record now explicitly
   identifies the unsuccessful plan and counterexample. Its proof_deps still names the two
   existing plan ingredients, not the removed component nodes. The parent node now records its actual existing Lean reduction through existence and
   pinned equations, explicitly flags the disputed dependency, and distinguishes the three
   concrete definitions from the unimplemented construction in the old narrative plan.

Changed: removed the false split and conjunction wrapper, restored the baseline pinned sorry,
marked it disputed with the sign-twist counterexample, updated the pinned and parent proof records, removed the
unchanged extra module from the delivery set, and rewrote the report to count no progress.
