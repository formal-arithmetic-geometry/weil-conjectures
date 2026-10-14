## What changed

Proved `AlgebraicGeometry.standardSingle_union_homotopy_chain_data` in
`Sheaf.AlgebraicGeometry.StandardSingleUnionHomotopyChainData`, preserving its
complete signature and its public imports. No other Lean module was changed.

Apply `relativeMV_cover_homotopy_data` on the scheme of the union, with the
single coefficient and its canonical single pullback map. The inverse images
of U and V cover that scheme, by `Scheme.Hom.preimage_sup` and
`Scheme.Opens.ι_preimage_self`. Apply `standardSingle_open_relative_arrow` to
U, V and their intersection. Compose the returned source and target vertex
isomorphisms with the relative cover comparisons, using `biprod.mapIso` at the
middle vertices. The global arrow already agrees definitionally with the
standard single arrow. Two private proved category lemmas transport the middle
and overlap equations using `Arrow.w`, biproduct projections and associativity.
The specified homotopy and its cone map are kept unchanged.

Added only the proof imports
`Sheaf.AlgebraicGeometry.RelativeMVCoverHomotopyData` and
`Sheaf.AlgebraicGeometry.StandardSingleOpenRelativeArrow`. Updated the item's
node `lem-pc-standard-single-union-homotopy-chain-data` in the sandbox to record
this route, its exact proof dependencies and its proof origin. No statement,
definition, instance, public import, or target was changed.

Single-file compilation through `lcompile.py` passed in 18.7 seconds with no
warnings. The theorem needs local elaboration options for the pinned derived
functors and 800000 heartbeats; the compile timeout was not changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.standardSingle_union_homotopy_chain_data`
(`lem-pc-standard-single-union-homotopy-chain-data`): 1 of 1 original holes.
The module contains no remaining `sorry`. Added zero holes and zero split
statements. Both private transport helpers are proved completely.

This is a proof from existing library declarations, whose existing downstream
obligations remain in their own modules; it does not claim that their transitive
proofs, or the project targets, are now free of `sorry`.

## No longer needed

Removed these four direct proof imports:

- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`
- `Sheaf.AlgebraicGeometry.KInjectiveMayerVietorisPresentation`
- `Sheaf.AlgebraicGeometry.DerivedMayerVietorisUnderivedOpenCounitSquare`
- `Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded`

Removed the item's direct proof-dependency edges to
`prop-pur-kinjective-resolutions-exist`,
`lem-pc-kinjective-mayer-vietoris-presentation`, `def-pc-derived-pullback`,
`lem-pc-mayer-vietoris-underived-open-counit-square`,
`lem-pc-derived-direct-image-composition`, and `def-pc-module-pullback`.
The existing statement dependencies remain unchanged. The resolution,
Mayer--Vietoris and counit-square modules are still reached transitively by the
relative cover proof; their removal here does not prune their obligations.
`Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded` is absent from
the revised import closure of this module. Other project routes may still need
it; no global unreachability is asserted.

The new direct proof route uses only the existing nodes
`lem-pc-relative-mv-cover-homotopy-data`,
`lem-pc-standard-single-open-relative-arrow`, `def-pc-relative-mv-maps`, and
`def-pc-standard-single-base-change-map`. No blueprint unit realization was
bypassed: `sk-thm-picard-coherence` has no realization attached to this node or
to these internal comparison steps.

## Where the brief, the DAG or earlier work was wrong

The original node's resolution-and-counit plan did not directly supply the
specified cone-map comparison. The library now has an unrestricted relative
cover theorem and a single-open arrow normalization theorem. Their combination
supplies that comparison without constructing another resolution diagram or
introducing another split. Searches with LeanFinder, Loogle, the provided grep
search and local `rg` led to these existing modules.

The earlier repair return records a universe failure in
`ProperFlatImageGlobalHomBaseChangeIso` after changes to comparison dependencies.
This delivery changes only this module's proof and its private helpers; it
preserves all existing signatures and public imports and does not modify either
comparison dependency. No forced adaptation is required.


## Second reading by X3

1. **Unchanged interface: pass.** Compared the delivered Lean file and node
   with the repository versions by `diff`. Extracted the entire existing
   theorem signature, including its local instance and all four arrow lets:
   it is byte-for-byte identical. The sole public import is identical. There
   are no new public declarations, definitions, instances, change records or
   adapted modules. The only new declarations are the two private transport
   proofs. Only `proof`, `proof_deps` and `proof_origin` differ in the node.

2. **Proof and axioms: pass.** Compiled the delivered module with `lcompile.py`
   without errors or warnings (21.6 seconds). Compiled a scratch copy with
   `#print axioms` for the theorem and both private helpers (18.8 seconds).
   The helpers use only `propext`, `Classical.choice` and `Quot.sound`. The
   theorem uses those and `sorryAx`, inherited from existing open statements
   below the imported comparison results. The delivered module contains no
   `sorry`, prohibited declaration or hollow definition. Its existential
   witnesses remain inside a theorem proof; no definition selects an arbitrary
   witness of an unproved existence statement.

3. **Split statements and edge cases: pass.** There are no new split statements
   or new nodes. Read the complete signatures of
   `relativeMV_cover_homotopy_data` and `standardSingle_open_relative_arrow`:
   the former accepts arbitrary derived coefficients on a covering pair, and
   the latter accepts arbitrary morphisms and every contained open with the
   literal tensor coefficient required here. Thus no flatness, affine,
   compactness or quasi-coherence assumption has been smuggled in. Empty,
   repeated and contained opens satisfy the same inverse-image cover identity
   and the same three containment proofs; zero N requires no new assumption.
   Both private helpers are direct consequences of arrow commutativity and
   biproduct projection extensionality, with no geometric side conditions.

4. **Route and pruning: pass.** Read the two proof dependencies and their
   current landed interface-restoration records. The global relative arrow
   unfolds to the specified standard single map. The U, V and intersection
   arrow isomorphisms transport all six object comparisons; associativity and
   `Arrow.w` give the middle and overlap equations. The same H and
   `mappingCone.mapOfHomotopy H` are retained. A fresh LeanFinder query for
   representation of a Mayer--Vietoris base-change morphism by a homotopy
   square returned sheaf Mayer--Vietoris short complexes and general cone
   constructions, not a replacement for this geometric comparison. Local
   `rg` searches of Sheaf, the adopted library and the source checkout found
   no shorter unrestricted result; the nearby
   `singleComplexOpenComparison_union_compatible_chain_data` requires extra
   affine, qcqs, quasi-coherence and compact-open hypotheses unavailable here.
   Each of the two plain imports supplies a theorem actually used, and the
   public import supplies the signature's standard map. All six removed old
   proof-dependency edges and all four removed imports are listed under
   `No longer needed`, with the distinction between direct removal and global
   pruning explicit. Read `dag/units/sk-thm-picard-coherence.json`, including
   its statement, proof step and empty `realized` lists: this internal
   coefficient-normalization reduction bypasses no realized unit step.

5. **DAG agreement: pass.** The node's verbatim Lean signature equals the
   unchanged declaration signature. Its four proof steps describe precisely
   the cover specialization, the three arrow normalizations and the two
   private category calculations. Its `proof_deps` are exactly the union of
   the steps' `uses`; `proof_origin` records the existing-library reduction.
   The retained statement dependencies, source, blueprint ancestry and unit
   are unchanged. No new-node fields or source proofs need checking because
   the delivery adds none.

**Changes by the second reader:** Added this independent review and recorded
its fresh compilation, axiom and search evidence. No Lean or DAG repair was
needed. Closed one original named hole, added zero holes, split off zero
statements; the transitive imported obligations remain open.
