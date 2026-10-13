## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.etaleTriple_strictHenselization_identification`
with a compiling reduction. The new comparison statement contains only the unique pointed
ring equivalence, corresponding to Steps 1–4 of the original DAG plan. The original module
proves the ideal equality by two inclusions: the pointed residue map kills q, while q
contracts to m and the structural map factors through the triple. It then applies the
existing proved `RingTheory.pair_henselization_completion_data` to the quotient maps of
the ring equivalence, proving the full completion evaluation clause and uniqueness.

Added proof imports for `StrictHenselizationComparison`, `EtaleResidueTriplesLocalization`,
and `PairHenselizationCompletionData`. The existing public imports and theorem signature
are unchanged. The proof has local transparency options for the scheme residue-field
encodings and a documented elaboration heartbeat budget; compilation remains below 60 s.
Updated the existing node's proof route and added the comparison node and module.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.etaleTriple_strictHenselization_identification`
(node `lem-sc-etale-triple-strict-henselization-identification`). Added one hole:
`AlgebraicGeometry.Scheme.strictHenselization_comparison`
(node `lem-sc-strict-henselization-comparison`). This is a decomposition, not a net
hole reduction: one closed, one added. There are no other sorries in the delivery.
The maximal-ideal and completion clauses are proved in the original module rather
than included in the new hole. No data definition or target statement was changed.

The remaining comparison has a full source-based proof in its docstring and node.
Its identity-triple case gives the identity on the strict henselization; a field base
has zero maximal ideal, and no assumption that the localization is finite over R is
introduced. The nonzero residue field excludes a zero colimit ring automatically.

## No longer needed

Removed the direct proof import `Sheaf.RingTheory.MapIntoHenselianColimit` from the
original module; it remains imported by the comparison module and is still needed
transitively. The original node's direct dependencies on
`lem-weil-pbc-strict-henselization-triples` and
`lem-weil-pbc-map-into-henselian-colimit` now occur in the comparison node. The direct
`def-weil-pbc-adic-completion` proof dependency is replaced by the existing stronger
`lem-weil-pbc-henselization-completion-data` tool, whose statement uses that definition.
No existing module or node is claimed pruned from the targets' transitive closure.

## Where the brief, the DAG or earlier work was wrong

The completion step already has an exact usable library theorem:
`RingTheory.pair_henselization_completion_data`. No new completion lemma is needed.
The ideal transport also needs no locality assertion about the comparison map: the
kernel equality and the triple's prime contraction prove it by an ideal sandwich.
The unit `sk-thm-br` has no realized node step that this reduction bypasses; the
comparison retains the original strict-henselization mapping route.

An initial scratch attempt accidentally wrote temporary modules in the read-only
repository; those files were removed and the item's original text restored. All
final delivery changes are in the sandbox. The local literature checkout lacks the
Stacks tex files; the cited Tags 04GW, 04GP and 08HR were read at their official pages.
Searches were run through msearch (LeanFinder, Loogle, grep) and rg on both library
roots before creating the comparison node. No exact existing comparison was found.

## New nodes

`lem-sc-strict-henselization-comparison`, in
`dag/nodes/sec-curve-estimates/lem-sc-strict-henselization-comparison.json`, states
only the pointed ring-colimit comparison before ideal or completion transport.
Its module is `Sheaf.RingTheory.StrictHenselizationComparison`. The source and proof
are Steps 1–4 of the original node, using Stacks Tags 04GW, 04GP and 08HR. The node
records the verbatim Lean signature and the actual three searches. No change record
is needed because no existing declaration signature or importer-visible interface
was changed.

## Second reading by B4

1. Compared both delivered modules with the repository. The only existing declaration,
   `AlgebraicGeometry.Scheme.etaleTriple_strictHenselization_identification`, has a
   byte-for-byte unchanged signature and docstring. Its local-ring, separable-closure,
   cocone, localization, and residue-compatibility hypotheses are all retained, as are
   uniqueness, both map compatibilities, ideal equality, and completion evaluation
   at every natural-number index. No definition or target changed. Verdict: pass.
2. Compiled both files through lcompile.py. Scratch copies with `#print axioms` show
   exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` for both declarations.
   The only delivered sorry is the named comparison theorem reported above; there are
   no forbidden declarations or hollow definitions. The original proof derives qC=mC
   from ker(psi)=mC and contraction of q, transports it by e, and uses quotientEquiv
   and pair_henselization_completion_data for all completion coordinates. Verdict: pass.
3. Read the comparison signature, docstring, node, and the mapping and triples lemmas.
   It states only the unique pointed ring equivalence, omitting the independently proved
   ideal and completion clauses, so it is a strictly smaller part of the argument.
   Identity triple and field-base cases are consistent; unital residue maps exclude zero
   colimits. Localization forces compatibility on A from compatibility on S. The
   separable closure over kappa(A) follows from the finite separable residue extension
   of the etale triple and hchiA. Fresh LeanFinder search for uniqueness of maps from
   pointed etale colimits into henselian local rings, Loogle for IsLocalization.AtPrime,
   grep for henselian/colimit combinations, and rg on both library roots found no exact
   replacement. No additional hole was closed. Verdict: valid decomposition, net zero.
4. Checked the shortest-route reduction: ideal transport is elementary and completion
   uses an already proved library theorem. The old direct proof dependencies all appear
   in No longer needed, with retained transitive uses distinguished from pruning.
   The unit sk-thm-br has empty realized lists; its Brauer/Tsen route is unchanged.
   Corrected the new module's public proof import: EtaleResidueTriples is public for its
   signature, StrictHenselizationTriples is a plain proof import. Existing public imports
   are unchanged. Verdict: pass; no module pruned from target closure.
5. Existing node changes are confined to proof, proof_deps, and proof_origin. The three
   new direct dependencies match the actual proof calls. The comparison node has source,
   proof, dependency union, creation/blueprint records, search records, and a verbatim
   Lean signature. Corrected its Step 3 and its declaration docstring: g has source C
   and target D over R, so D need only be henselian local; the unrelated finite-presentation
   descent argument for an ind-etale R-presentation of D was unnecessary. Verdict: pass.

Second-reading changes: corrected the comparison proof explanation and node Step 3,
made its proof-only StrictHenselizationTriples import private to the module, and added
this review. No existing signature or Lean proof body changed. The original one-hole
closure and one-hole addition remain a decomposition, with no claimed net progress.
