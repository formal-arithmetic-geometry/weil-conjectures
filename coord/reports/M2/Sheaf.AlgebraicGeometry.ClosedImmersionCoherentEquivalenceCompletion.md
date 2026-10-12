## What changed

Proved `AlgebraicGeometry.closedImmersion_coherentFormal_equivalence_completion` directly from `Scheme.closedImmersion_pushforward_idealPowers`. Its quotient isomorphisms and level naturality assemble an isomorphism of inverse systems; its module naturality assembles the natural isomorphism on coherent modules; its projection equation gives the required compatibility. The locally Noetherian coherence criterion supplies quasi-coherence, after obtaining Noetherianity of Z from the closed immersion. All existing signatures and public imports are unchanged. Removed six unused proof-only imports.

The second reading removed the proposed helper module `ClosedImmersionCoherentEquivalenceCompletionIso` and its two proposed nodes from the delivery. Neither helper declaration is in the repository, so this removes no existing interface and needs no change record.

## Proved and sorry left

Closed one original hole: `AlgebraicGeometry.closedImmersion_coherentFormal_equivalence_completion` (node `lem-weil-pbc-closed-immersion-coherent-formal-equivalence-completion`). Added zero holes; no `sorry` remains in the delivered module. This is a proof from existing dependencies, not a decomposition. The proposed holes `AlgebraicGeometry.closedImmersion_completion_comparison_iso` and `AlgebraicGeometry.closedImmersion_completion_comparison_projection` were removed entirely.

The axiom print for the target is `[propext, sorryAx, Classical.choice, Quot.sound]`: the inherited `sorryAx` is already present in `Scheme.closedImmersion_pushforward_idealPowers`. The coherence criterion and Noetherianity theorem print only the three permitted axioms. Thus this delivery closes the local hole, but does not certify the target's full import closure free of open proofs.

## No longer needed

Removed proof-only imports:
- `WeilConjectures.AlgebraicGeometry.Modules.TensorSection`
- `Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardAnnihilated`
- `Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardFullyFaithful`
- `Sheaf.AlgebraicGeometry.ClosedPushforwardStalks`
- `Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase`
- `Sheaf.AlgebraicGeometry.FinitePushforwardCoherent`

Old proof dependencies no longer used directly, all removed from this node's `proof_deps`:
- `lem-weil-pbc-closed-immersion-pushforward-annihilated`
- `def-weil-closed-immersion`
- `lem-weil-pbc-closed-immersion-finite`
- `lem-weil-pbc-finite-pushforward-coherent`
- `lem-weil-pbc-closed-immersion-pushforward-fully-faithful`
- `def-weil-pbc-closed-subset-proper-over-base`
- `lem-weil-pbc-closed-pushforward-stalks`
- `def-nagata-extended-ideal`

The existing ideal-power and coherence-criterion imports are retained. These are direct dependency removals; no assertion is made that the removed modules are unreachable from every target, since retained imports can still reach them.

## Where the brief, the DAG or earlier work was wrong

The first worker missed that the existing ideal-power theorem supplies all three compatibility clauses needed to construct the natural comparison. Its proposed projection helper was false: it asserted the equation for an arbitrary isomorphism θ rather than a specified canonical comparison. For the identity immersion, zero ideal, and a nonzero coherent module in characteristic unequal to two, negating a comparison yields another natural isomorphism but fails the prescribed quotient projection equation. The existence helper alone did not identify a canonical comparison. Both proposed helpers and their nodes were removed, and the earlier second-reading verdict is superseded.

## Second reading by M2

1. Compared the entire delivered module with the repository using `diff -u`: the existing declaration signature and docstring are byte-for-byte identical; only its proof and six proof-only imports change. No definition, public import, target statement, or existing declaration is altered. There are no applicable change records naming this module.
2. Compiled the repaired module with `lcompile.py`: no errors or warnings. Scanned for forbidden constructs and holes: none in the delivered module. Scratch `#print axioms` permits only the three standard axioms and the inherited `sorryAx` identified above. All data in the proof are assembled from quotient isomorphisms with specified projection compatibility; cokernel epimorphy determines these uniquely, so no arbitrary data witness is used to define an object.
3. Rejected the arbitrary-isomorphism projection claim by the identity-immersion/zero-ideal/sign counterexample. Removed both split-off statements; no new statement or new node remains. Searched the library for completion/pushforward comparisons and read the existing ideal-power theorem, and searched Mathlib through `msearch.py` for `NatIso.ofComponents`. The existing comparison family plus Mathlib's componentwise assembly suffices. The construction handles level n=0 as quotient exponent 1; no exponent-zero compatibility is assumed. Zero modules and empty schemes need no additional hypotheses.
4. The repaired proof follows the shortest existing quotient-comparison route. Retained exactly the proof-only imports supplying that comparison and coherence criterion. The No-longer-needed section lists all eight discarded old proof dependencies. Read `dag/units/sk-thm-p1.json`: this node is below its realized statement and steps; no realized node or unit route is bypassed, and the unit record is unchanged.
5. Replaced the target node's proof steps, `proof_deps`, and `proof_origin` to describe the actual two-level natural-isomorphism construction. Existing statement, statement dependencies, and Lean signature records remain unchanged. Removed the two proposed new node files along with their Lean helper module.

Second reading changed the invalid two-hole decomposition to a direct proof from the existing ideal-power theorem, corrected the report and DAG, and removed both new helpers and nodes.
