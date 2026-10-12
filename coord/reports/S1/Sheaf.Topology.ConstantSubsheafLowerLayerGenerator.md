## What changed

Reduced `TopCat.Sheaf.constantSubsheaf_lower_layer_generator` to three strictly separate
steps of Stacks Lemma 0A38: a positive labelled presentation, the stalk computation of
an explicitly constructed lower image, and gluing the top quotient section. Its signature
and existing docstring are unchanged. The main proof constructs `f` by `Sigma.desc`,
sets `L := image f` and `l := image.ι f`, supplies the finite generating epimorphism
`factorThruImage f`, proves compactness of both finite unions, and proves their inclusion.
It then combines the two different stalk assertions with the quotient-section result.
Each intermediate statement is in its own new module and has a matching node, source,
and complete proof in words. The item's node now follows this Lean proof.

## Proved and sorry left

Closed the original hole in `TopCat.Sheaf.constantSubsheaf_lower_layer_generator`.
There is no sorry left in the item's module. This is a decomposition, not a completed
axiom-free mathematical proof: one upper hole closed, three strictly lower holes added
(net minus two before pruning and the pinned import-closure baselines).

Every new hole is the complete proof of a named public theorem:

- `TopCat.Sheaf.constantSubsheaf_normalized_presentation`, node
  `lem-sc-constant-subsheaf-normalized-presentation`: finite positive labelled generation
  with an active label dividing all active labels; no lower subsheaf or quotient conclusion.
- `TopCat.Sheaf.constantSubsheaf_lower_image_stalks`, node
  `lem-sc-constant-subsheaf-lower-image-stalks`: bounds and vanishing for the actual
  categorical image of the low components; assumes a labelled presentation and does not
  assert compactness, finite generation, or existence of a quotient-section morphism.
- `TopCat.Sheaf.constantSubsheaf_quotient_section`, node
  `lem-sc-constant-subsheaf-quotient-section`: constructs the quotient morphism from the
  labelled sections and the two stalk vanishings; assumes neither compactness nor gcd closure.

Checked the mathematical edge cases: empty generating family gives U=V=empty and the
zero image; b=0 gives no low labels and L=0; all labels low gives U=V and a vacuous
isomorphism assertion; on a one-point space with active labels 2 and 3 the attained-divisor
hypothesis requires adding label 1, which fixes the lower-layer computation; with labels
2 and 4, the attained label 2 makes the lower image equal K as soon as a low label is
active. Arbitrary stalk coordinates are signs of canonical coordinates, so they preserve
the subgroup and its nonnegative generator. High summands in the finite presentation of
L have zero component: finite generation requires an epimorphism, not nonzero components.
The original statement does not require q to be epi, and none is asserted here.

All four modules compiled cleanly with the authorized local compiler. The delivery dry run
checks all declarations with its axiom probe and checks the node/signature records.

## No longer needed

Removed the item's direct proof imports of
`Sheaf.Topology.AbelianOpenExtensionByZeroStalks`,
`Sheaf.Topology.ConstantSheafLocallyConstantComparison`, and
`Sheaf.Topology.PresheafModuleStalkFunctor`.
The first two results remain needed for proving the new intermediate statements and
are retained in their proof plans; they are not claimed as globally pruned.
`Sheaf.Topology.PresheafModuleStalkFunctor` is not needed for these abelian-sheaf stalks:
Mathlib's `TopCat.Presheaf.stalkFunctor` supplies all stalk expressions in the signatures.
No module-dependent linearity theorem is used. No claim is made that another target does
not reach this module.

The original direct proof dependencies
`def-sc-abelian-open-extension-by-zero`, `def-weil-pbc-constant-sheaf`,
`def-weil-pbc-module-stalk`, `lem-sc-constant-sheaf-locally-constant-comparison`, and
`lem-sc-topological-extension-by-zero-stalks` are replaced by the three new statement nodes.
The definitions and the two supporting results remain recorded under the new nodes,
so no mathematical ingredient of the prescribed route is bypassed.
No public statement import was removed. There are no additional nodes or modules
that this argument renders unnecessary.

## Where the brief, the DAG or earlier work was wrong

The listed dependencies do not state normalization with the finite labelled presentation,
the low-image stalk calculation, or quotient-section gluing. Thus applying those existing
statements alone does not directly give the target conclusion. The new nodes make these
three missing interfaces explicit instead of applying a renamed version of the target.
No false statement or change to an existing definition or statement was found.
The source TeX file is absent on this machine; the source was read at
https://stacks.math.columbia.edu/tag/0A38. The construction follows its proof paragraphs.
The unit `sk-thm-curveestimate` realizes its statement by `thm-sc-proper-cohomology`,
not by this auxiliary node; its route is preserved. No chapter or unit record changed.

Searches were run using the prescribed search logger and by local ripgrep. LeanSearch
returned Internal Server Error and is recorded as unavailable. LeanFinder gave generic
finite-generation, quasicoherent-presentation, and gluing results, not these integer-layer
statements. Loogle on `TopCat.Sheaf` gave the generic sheaf API. Local searches checked
the original filtration modules and source topology library; the finite-filtration and
peel-layer theorems depend on this item and would be circular. Blueprint searches for
constant subsheaf and gcd found no duplicate interface. The new proof words name the
Mathlib tools read for finite range, Bezout, stalk exactness, and gluing.

## New nodes

`lem-sc-constant-subsheaf-normalized-presentation` in
`lean/Sheaf/Topology/ConstantSubsheafNormalizedPresentation.lean` realizes the normalization
paragraphs. It records the section produced by each generating component explicitly,
including the extension-by-zero unit section and its constant value under the fixed
ambient sheaf isomorphism. This is the data needed to make the later stalk and gluing
computations about the actual morphism g.

`lem-sc-constant-subsheaf-lower-image-stalks` in
`lean/Sheaf/Topology/ConstantSubsheafLowerImageStalks.lean` realizes the stalk calculation
for the image of low components. It also provides L_x=0 off V, the input needed by the
quotient gluing step. Compactness and the construction of the image are handled in the
main theorem, not hidden in this new hole.

`lem-sc-constant-subsheaf-quotient-section` in
`lean/Sheaf/Topology/ConstantSubsheafQuotientSection.lean` realizes the quotient section and
its stalk isomorphism. It constructs q from labelled sections and independently supplied
stalk vanishings; it is not the whole original existential conclusion. Its proof words
explain the presheaf summand map followed by sheafification that implements extension
by zero. No new definitions, statement corrections, or change records are needed.


## Second reading by S1

1. **Unchanged public contract — PASS.** Compared the delivered main module with the
   repository by diff and compared its theorem signature byte for byte. The existing
   signature and docstring are unchanged; only proof imports and the proof body differ.
   No existing definition changed. The three other delivered modules are new.
2. **Lean proof and axioms — PASS as a decomposition.** Independently compiled all four
   modules through `lcompile.py --all`: no errors or warnings. Read every proof and checked
   every occurrence of sorry: exactly the three named public theorems listed above remain.
   There are no definitions in the new modules, no forbidden declarations or attributes,
   and no hidden holes. A scratch copy with `#print axioms` for all four declarations
   compiled and reported only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   Removed the scratch copy before delivery. The main theorem constructs its categorical
   image inside its proof; no public data definition chooses an arbitrary unproved witness.
3. **Split statements — PASS.** Read each signature, its complete proof docstring, and its
   node. Checked empty X, empty families and empty opens, b=0, all-low and all-high labels,
   and one-point examples with labels 2/3 and 2/4. The attained-divisor hypothesis is
   essential on a mixed-label stalk; normalization adds the gcd section before truncation.
   Sign changes of arbitrary integer stalk coordinates do not change the positive generator.
   The quotient lemma needs only the supplied vanishings, rather than the gcd property.
   Each statement handles a strict part of the argument: presentation, a specified image's
   stalks, or quotient gluing. None restates the original existence of a compact finitely
   generated lower layer. Repeated LeanFinder searches with different wording for all
   three parts, Loogle for image inclusions, the logged grep search, and local rg searches
   of Mathlib, upstream topology, and lean/Sheaf found generic tools but no duplicate.
   The proved ConstantSubsheafStalkBound supplies a numerical bound, not these interfaces;
   finite filtration and peeling import this item and cannot replace it without a cycle.
   The three remaining proofs require substantial sheaf and integer bookkeeping; none
   could be closed in a few minutes from the current public interfaces.
4. **Top-down route and pruning — PASS.** Checked the source at
   https://stacks.math.columbia.edu/tag/0A38 and the actual extension-by-zero construction
   and canonical section. The main proof itself handles image factorization, finite
   generation, compact finite unions, and V≤U. Its three remaining imports are proof-only.
   Public imports provide symbols occurring in the signatures. Checked every old direct
   proof dependency against the report's No longer needed section: all five old node ids
   and all three removed imports are accounted for. Supporting comparison and extension
   stalk results remain in the new nodes' plans; no global pruning claim is made for them.
   The module-stalk dependency is not used as a linearity theorem. The unchanged unit
   sk-thm-curveestimate realizes its statement by thm-sc-proper-cohomology and has no
   realized step here; its prescribed route is retained.
5. **DAG agreement — PASS.** Verified all new Lean signature records against their source
   signatures (whitespace normalized), each node's dependency union against its proof
   steps, source, creation record, blueprint provenance, chapter, unit, and named Lean
   declaration. The existing node changes only proof, proof_deps, and proof_origin, and
   its three steps match the actual Lean calls and constructions. New nodes have complete
   source-based plans and the required search records.

Second reading changed only this report by adding the independent checks and verdicts.
No Lean or node repair was necessary. One original hole is closed by decomposition and
three lower holes remain; this is not an axiom-free proof or positive net hole reduction.
