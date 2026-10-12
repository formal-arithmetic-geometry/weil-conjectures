## What changed

Replaced the previous pointwise-existence split by a direct construction on
R = Q times_T U. `finiteLocalModels_comparison` evaluates the representing
isomorphism on the universal Q-point, and `finiteLocalModels_transport` pulls
that morphism back along (x,b). There is no arbitrary witness choice and no new
sorry. Proved naturality by the pullback universal property and compatibility
by naturality of e and component injectivity. The final datum is assembled from
this constructed transport and its two proved laws.

Corrected the two helper statements to concern this canonical transport. The
structure and the final datum theorem have identical signatures and visibility.
No external module calls either corrected helper; no forced adaptations.

## Proved and sorry left

Closed `finiteLocalModels_transport_exists` with its original signature unchanged
(node `finite-local-models-transport-exists`).

Corrected and proved `finiteLocalModels_transport_naturality` and
`finiteLocalModels_transport_compatibility` (nodes with the corresponding
hyphenated names). Their old, false arbitrary-function statements are not claimed
as proved. This is one unchanged hole proved and two false helper interfaces
corrected and proved, not a decomposition.

`finiteLocalModels_descentDatum_compatibility_datum` was already a proof that
relied on all three sorries; it now uses an explicit function and the proved laws,
with its original type unchanged. The two new definitions and the private
section-naturality helper are fully proved. No sorry remains or is added anywhere
in the delivery. The delivery tool checks axioms of all declarations.

## No longer needed

Removed the previous attempt's import of
`Sheaf.AlgebraicGeometry.FiniteLocalModelsTransportPointwise`, its unlanded
module, and its unlanded node `finite-local-models-transport-pointwise`.
Pointwise existence plus arbitrary choice was only a restatement of the upper
hole and did not determine the required transport.

No original public imports are removable: both are used by the signatures and
construction. The planned `lem-galois-yoneda-fully-faithful` black box is not
needed in this node's proof: evaluation at the universal point and naturality
prove the comparison directly. This Mathlib leaf remains useful elsewhere.
Removed the old child-to-parent proof-dependency edges from the existence and
law nodes; the parent now depends only on the actual construction and laws.
No UNIT statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The old naturality and compatibility statements universally quantified over an
arbitrary function, without saying it came from the comparison construction.
They are false: with T=U=Spec k and Q a split two-point finite etale scheme,
composition with the swap fails section compatibility. Choosing identity on
Spec k sources and swap on Q sources fails naturality along a component map.
Both corrected statements now have complete proofs; their parent statement is
unchanged. Their change records and DAG statement_change fields document this.

The earlier sandbox attempt also selected arbitrary witnesses from mere
existence, contrary to the brief, and left these false law statements untouched.
Its new hole has been removed rather than delivered.

Edge cases: empty Q, U, T, or W use the same evaluation and pullback construction;
no inhabitedness, surjectivity of U over T, or chosen section of E is assumed.
E is evaluated only on R, which is etale over T, and on etale W in compatibility.
Naturality permits arbitrary scheme sources. The finite hypothesis is used only
to provide that Q is etale. Search tools found no preexisting transport theorem;
NatTrans.naturality, pullback.lift_fst/snd and pullback.hom_ext suffice.

## New nodes

`def-weil-pbc-finite-local-model-comparison-point` records the explicit universal
comparison point; it is a real definition, with no sorry or data choice from an
unproved theorem. `def-weil-pbc-finite-local-model-canonical-transport` records
the pullback construction from that comparison point. Both are in the item's
module and introduce no extra items requiring proof.

Change records:
`coord/changes/finiteLocalModels_transport_naturality.md` and
`coord/changes/finiteLocalModels_transport_compatibility.md`.

## Earlier second reading (a previous round; superseded)

1. **Declarations and signatures.** Compared the delivered module with the repository version. The
`FiniteLocalModelCompatibleTransport` structure and
`finiteLocalModels_descentDatum_compatibility_datum` signatures are byte-for-byte unchanged.
The two helper theorem signatures intentionally change from arbitrary transport functions to the
explicit canonical transport; both changes have dedicated records and DAG `statement_change` data.
The new comparison and transport definitions are documented nodes and have no `sorry` data.
Verdict: pass.

2. **Proof and axioms.** Compiled the module with `lcompile.py`; it is error- and warning-free and
contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. An axiom audit of
every declaration reports only `propext`, `Classical.choice`, and `Quot.sound`. The transport is
constructed by pullback and the comparison point, so no arbitrary witness is selected.
Verdict: pass.

3. **Split-off statements and searches.** The two changed helper statements restrict the laws to the canonical transport. This restriction corrects the false universal claims, as justified by the recorded counterexamples; the parent existence statement is unchanged. The existence theorem is proved directly from the construction. Local
`rg` and msearch checks found no duplicate declarations or shorter existing theorem supplying this
construction. No new sorry or split-off theorem was added.
Verdict: pass.

4. **Pruning and imports.** Both public imports are required by the public signatures and the
pullback/étale construction; no proof-only public import was introduced. The old arbitrary-choice
route and its pointwise module/node are absent from this delivery. The canonical transport and both
laws are the actual proof dependencies. Verdict: pass.

5. **DAG and unit route.** The delivered node records agree with the definitions and theorem bodies,
including updated `proof`, `proof_deps`, `proof_origin`, and statement-change metadata. The new
comparison and canonical-transport definitions have matching nodes. The unit `sk-thm-p1` remains
realized through its existing statement and steps; no unit-level route is bypassed. Verdict: pass.

Changed in this second reading: removed two unnecessary backward elaborator options after confirming
that the module still compiles; added this review section and retained the documented change records
and DAG metadata.

## Second reading by F1

1. Compared the delivered module against the read-only repository with diff.
The structure (including every field), transport-existence theorem, and final
datum theorem retain byte-for-byte signatures. Only the two explicitly reported
helper-law interfaces change; their old and new signatures match the two change
records. Whole-library rg confirms no external caller of either helper. Pass.

2. Independently compiled the delivered file using lcompile.py without errors
or warnings. Regenerated the axiom scratch from this exact delivered source:
the private helper, both constructions, and all four public theorems use only
propext, Classical.choice, and Quot.sound. No forbidden declaration or sorry
occurs. The comparison evaluates e.inv on a specified universal point; the
transport composes an explicit pullback lift, with no arbitrary witness choice.
Pass.

3. No statement was split off and no hole was added. Read the two corrected laws
and their proofs: naturality follows by pullback.hom_ext; compatibility follows
by component injectivity and naturality of e twice. Empty sources and empty
representatives need no separate choice or inhabitedness assumption. The old
universal laws fail for the split two-point representative as documented.
Independent msearch queries for universal-point extension and pullback.lift,
and rg for overTransport, found only supporting lemmas. The upstream
RepresentableBy.overTransport needs a big-site representation, unavailable in
this small-site signature. Pass.

4. Both public imports are needed by the signatures (FiniteEtale and the
localized etale-site functors). No new import or proof-only public import occurs.
Checked every old proof_deps edge: the parent drops
lem-galois-yoneda-fully-faithful, and each child drops its circular parent edge.
These removals and the discarded unlanded pointwise attempt are reported above.
No repository module is pruned by this delivery. Pass.

5. Read all six delivered nodes and compared existing-node changes to the
repository. Their proof plans, dependency unions, and origins follow the Lean
construction and laws. The two new definition nodes have source, search,
creation, blueprint, chapter/unit, and Lean records. Statement-change metadata
accompanies both corrected helpers. Checked sk-thm-p1.realized: none of its
statement or step realizations is bypassed. Pass.

Changed in this reading: regenerated the scratch axiom audit from the exact
delivered source and appended this independent review. No Lean proof or
interface repair was needed. One original hole is proved unchanged; the two
false holed helper statements are corrected and proved, not counted as proofs
of their old statements. No holes are added.
