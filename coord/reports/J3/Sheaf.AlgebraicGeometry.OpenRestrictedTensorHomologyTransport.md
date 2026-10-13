## What changed

Preserved the original signature and docstring of
`AlgebraicGeometry.SingleComplexBaseChange.openRestricted_tensor_homology_transport`
byte for byte. Its proof now obtains the degreewise additive chain square from
`openRestricted_tensor_chain_transport` and applies
`openStalk_chain_homology_transport` to the specified tensor stalk maps and
`openTensorRestrictionComplexIso`. The representative in the latter theorem is
definitionally `openRestrictedTensorDerivedIso` in this instance.

Two new modules state these strictly separate steps. Both are proof-only imports
in the original module. Their public imports supply only objects in their
statements. No definition, old statement, or existing visibility changed.

## Proved and sorry left

Original hole closed: `AlgebraicGeometry.SingleComplexBaseChange.openRestricted_tensor_homology_transport`.
New named holes:

- `AlgebraicGeometry.SingleComplexBaseChange.openRestricted_tensor_chain_transport`,
  node `lem-pc-open-restricted-tensor-chain-transport`, is the ordinary degreewise
  tensor/stalk comparison, with no homology equation in its conclusion.
- `AlgebraicGeometry.SingleComplexBaseChange.openStalk_chain_homology_transport`,
  node `lem-pc-open-stalk-chain-homology-transport`, passes an assumed additive
  chain square to homology for arbitrary complexes and maps, with no tensors,
  pullback square, or input coordinates in its statement.

This is a decomposition, not a completed proof: 1 original hole closed, 2 new
holes added, net -1. No other holes were added or closed. Each remaining hole is
exactly `:= by sorry` in a named public theorem with a source and a full proof
in words. No data or definition is chosen from an unproved existence statement.

The rejected first-worker core and its hole have been removed entirely. The
unused `homologyMap_comp_transport` was not an existing library declaration;
it and its new module/node were removed because Mathlib already proves it.

## No longer needed

Removed the first worker's unused proof import
`Sheaf.AlgebraicGeometry.OpenRestrictedTensorHomologyTransportAux` and discarded
its duplicate helper/node. Removed the tautological new core/node. Neither was
in the baseline library, so these are not claimed as pruned library modules.

No baseline module is pruned. All three original proof dependencies remain
transitively necessary: `lem-weil-pbc-module-stalk-pullback` and
`def-pc-open-restricted-tensor-complex-iso` supply the chain calculation;
`def-pc-open-derived-stalk-iso` supplies the exact homology transport. They are
replaced in the parent's direct `proof_deps` by the two new step nodes.

## Where the brief, the DAG or earlier work was wrong

The first worker's core repeats the same pure-tensor hypothesis twice and has
exactly the original homology conclusion. Supplying a hypothesis a second time
is not a strictly simpler lemma or progress. Its wrapper also reformatted the
original signature and replaced its original docstring. The auxiliary composition
lemma repeats `HomologicalComplex.homologyMap_comp` and was unused.

The replacement follows the existing node's two proof steps without altering the
unit route. The unit `sk-thm-picard-semicon` has no realized entry naming this
node or either discarded helper. The analogous existing
`openOrdinaryTensor_germ_transport_equation` and
`openStalk_representative_coherence` concern a pinned restriction to an open
subscheme and different derived comparison maps; neither states this general
open-immersion comparison with `openDerivedStalkIso`. The new bridge avoids
copying those proofs and leaves their required analogue explicit.

## New nodes

`lem-pc-open-restricted-tensor-chain-transport` is precisely parent step 1,
restricted to ordinary degreewise additive morphisms. Its signature is recorded
verbatim in the new node. Its proof is the pure-germ calculation of Stacks
Lemma 6.26.4 (Tag 0098) with the units of the specified adjunction mates.

`lem-pc-open-stalk-chain-homology-transport` is parent step 2 for arbitrary
complexes and chain maps. Its signature is recorded verbatim in the new node.
Its proof is exact-functor homology naturality and cancellation of the specified
derived restriction comparison, using Stacks Section 20.32 (Tag 0D5U).

No change record is required: no existing statement or definition changed.

## Second reading by J3

1. Compared the first delivery and repaired delivery with the repository source.
   The rejected delivery preserved the elaborated target type but reformatted
   its signature and replaced its docstring. The repair preserves both byte for
   byte. No other existing module, statement, definition, or visibility changed.
2. Compiled the original attempted delivery and the repaired modules with
   lcompile.py. The only remaining sorries are the two named substeps above;
   no forbidden declaration or hollow definition is present. Axiom checks and
   the final delivery dry run are recorded below after verification.
3. Rejected the repeated-hypothesis core and unused Mathlib duplicate. Repeated
   searches with fresh LeanFinder, Loogle and Mathlib grep queries; inspected
   the existing project open-restriction homology proofs. Neither new statement
   duplicates an existing declaration. The chain lemma is before homology; the
   bridge assumes the chain square and has no tensor hypotheses. For zero maps
   the bridge reduces to homology of a zero composite; for identity restriction
   it is ordinary homology naturality; no cancellation of elements is needed.
   Empty opens have no point. Zero complexes and zero rings introduce no extra
   hypothesis. Each statement has its own proof docstring and node.
4. Retained the parent plan's ordinary chain-square step followed by exact
   homology transport. The unit's realized fields are unchanged. Removed both
   unused additions from the first attempt and retained the original public
   import needed by the unchanged signature. No baseline pruning is claimed.
5. Checked the parent and new nodes against the Lean: `proof_deps` are exactly
   the unions of their proof-step uses, provenance identifies this reduction,
   and each new node records its full signature, sources, searches, chapter,
   unit and creation metadata. Parent statement and statement dependencies stay
   unchanged.

Changes by this reader: removed the tautological core and unused auxiliary;
restored the original signature/docstring; introduced two genuine step lemmas
and the compiling reduction; rewrote the report and proof graph honestly as a
decomposition with net -1 holes.

Final local verification: all three delivered modules compile without errors or
warnings. A separate scratch module prints axioms of each of the three public
theorems: exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
The latter is expected for the two reported open substeps and their caller.
The original signature equality was checked byte for byte, and the final diff
changes only its proof and two plain proof imports. No lines exceed 100 columns.

The first preflight found missing LeanSearch-category records on the new nodes.
Ran both LeanSearch queries: the service returned Internal Server Error for
each. Recorded both as unavailable, without claiming a search verdict; the
independent LeanFinder, Loogle and source-grep searches succeeded.

Final dry run: deliver3.py --no-push printed OK at commit 1fc00cc3a9, with all
modules compiling and preflight passing. Review class CODEX because this
delivery adds the two genuine step statements/nodes.
