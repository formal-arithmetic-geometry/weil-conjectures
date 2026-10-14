## What changed

Replaced the sole sorry in `AlgebraicGeometry.standardSingle_union_homotopy_chain_data`
by a compiled assembly of two separate steps of its original plan:

* `RelativeMVCoverHomotopyData` concerns arbitrary derived coefficients on an actual
  covering pair. It constructs the resolved homotopy square and its prescribed three
  relative comparison components, without identifying coefficients with single modules.
* `StandardSingleOpenRelativeArrow` identifies one relative open arrow with the standard
  single-module map on an ambient subopen. It contains no cover, complexes representing
  the comparison, or cone-map assertion.

The assembly restricts to the union scheme, proves its induced opens cover, specializes
with the constructed single-complex coefficient map, and applies the normalization three
separate times. Two proved private helpers combine the member arrow isomorphisms through
biproduct projections and transport comparison equations through arrow isomorphisms.
The chosen homotopy and its `mapOfHomotopy` are retained literally.
The statement and public imports of the original module are unchanged. No definition
selects data from either new existence theorem; all existential witnesses are eliminated
only inside this theorem's proof. There are no forced adaptations or interface changes.

Validation: the original module and both new modules compile using lcompile.py.
All new lines satisfy the 100-character bound. Searches used LeanFinder, Loogle and grep;
LeanSearch returned Internal Server Error, recorded as unavailable in the new nodes.
The Stacks sources were read at Tags 08BV, 08HZ and 08HY and in the fetched
`cohomology.tex` (the repository's literature checkout is absent on this machine).

## Proved and sorry left

Closed the local hole in `AlgebraicGeometry.standardSingle_union_homotopy_chain_data`
(node `lem-pc-standard-single-union-homotopy-chain-data`). No sorry remains in the item.

Added exactly two named holes, each the entire proof of a public theorem in its own module:

* `AlgebraicGeometry.relativeMV_cover_homotopy_data`
  (`lem-pc-relative-mv-cover-homotopy-data`). This is the unresolved enhanced cover
  construction before single-coefficient normalization, corresponding to plan steps 1–2.
* `AlgebraicGeometry.standardSingle_open_relative_arrow`
  (`lem-pc-standard-single-open-relative-arrow`). This is the unresolved one-open
  coefficient and coordinate normalization in plan step 3.

This is a decomposition, not a proof free of new assumptions: one upper hole closed,
two lower holes added, net minus one hole closed. The final theorem still depends on
these two sorries. Neither new statement is the original statement under another name:
one handles the resolved covering diagram before normalization; the other handles a
single open's arrow isomorphism, independently of any diagram or cover. The compiled
assembly supplies the cover specialization, overlap identification, biproduct comparison
and all three conjugacy transports.

Small cases checked mathematically: a zero coefficient or empty open gives zero terms;
a repeated member gives the diagonal/difference split sequence; an empty union has only
empty induced opens. The cover lemma imposes the necessary cover equality explicitly.
The normalization lemma applies to the empty subopen and the full subopen and does not
assert that the base-change maps themselves are invertible. No affine, flatness,
quasi-coherence, quasi-compactness or separatedness assumption has been added.

## No longer needed

Removed from the item's direct proof imports:

* `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`
  (`prop-pur-kinjective-resolutions-exist`).
* `Sheaf.AlgebraicGeometry.KInjectiveMayerVietorisPresentation`
  (`lem-pc-kinjective-mayer-vietoris-presentation`).
* `Sheaf.AlgebraicGeometry.DerivedMayerVietorisUnderivedOpenCounitSquare`
  (`lem-pc-mayer-vietoris-underived-open-counit-square`).
* `Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded`
  (`lem-pc-derived-direct-image-composition`).

These four modules remain dependencies of the new resolved-cover statement, so none is
claimed as globally pruned. The original node's direct proof dependency on
`def-pc-derived-pullback` and `def-pc-module-pullback` is also mediated by the two new
statements; the notions remain necessary in their statements. No entire module or node
has been shown unreachable from the targets. Global pruning: none.
The new normalization module also omits a redundant direct import of
`PicardTermwiseSingleMapComposition`, already public through `StandardSingleBaseChangeMap`;
its composition identity remains a proof dependency.
The stronger compact/quasi-coherent relative cone and SES presentation modules were
examined but are not imported: their hypotheses are absent here, and their statements
also leave the prescribed middle component unspecified.

## Where the brief, the DAG or earlier work was wrong

The original proof plan does not have a stated unrestricted enhanced cover comparison
or the single-coefficient relative-arrow normalization needed to assemble its steps.
The available `relativeMV_cone_presentation` has affine-base, qcqs, compact-open and
quasi-coherent hypotheses and cannot be applied to this item. Its endpoint control
also does not imply the required biproduct component equation. An arbitrary completion
of a square of distinguished triangles does not establish the prescribed cone component.
The existing `RelativeMVOpenCoefficientTransport` cannot be imported: its transitive
dependencies reach this item through proper-flat and standard-single base change. The
normalization node instead uses the acyclic `DerivedBaseChangeSourceIso` API and records
the remaining coefficient-mate calculation explicitly.
No claim is made that the original theorem is false; its full statement was preserved.

The unit record `sk-thm-picard-coherence` has empty `realized` lists. This decomposition
retains the original unit route and the resolved Mayer–Vietoris/counit argument; it does
not replace any unit step or alter a chapter or unit record.

## New nodes

`lem-pc-relative-mv-cover-homotopy-data`, in
`Sheaf.AlgebraicGeometry.RelativeMVCoverHomotopyData`, isolates the resolved comparison
on an actual cover for arbitrary derived coefficients. Its dependencies retain the
resolution, exact-row, underived-counit and direct-image-composition parts of the plan.
Source: cohomology.tex, `lemma-exact-sequence-j-star` (08BV),
`lemma-unbounded-relative-mayer-vietoris` (08HZ), `remark-base-change` (08HY), and
`lemma-restrict-direct-image-open` (08FE).

`lem-pc-standard-single-open-relative-arrow`, in
`Sheaf.AlgebraicGeometry.StandardSingleOpenRelativeArrow`, isolates one subopen's
normalization to literal tensor-pullback coefficients. Its proof uses source-coordinate
identification, exact open restriction and the already stated single-map composition
lemmas, source-isomorphism conjugacy and an explicit adjunction-mate calculation. Source: Tags 08HY, 0D5S, 01JR and 0A1D.

Both nodes inherit the item's chapter and unit, have complete statements, proof plans,
search records and verbatim Lean signatures. Blueprint searches for `relative comparison
cover`, `single coefficient`, and `08HZ` found no imported duplicate. Local searches found
no unrestricted theorem giving either interface. No change record is needed because no
existing signature or definition changed.

## Second reading by E3

1. **Declarations and interfaces.** Compared the delivered item module with the repository version. The target theorem statement is unchanged. The two added theorem signatures match their node `lean.statement` fields verbatim. The item keeps the same public `StandardSingleBaseChangeMap` import; removed imports are proof-only dependencies. Verdict: pass.

2. **Proof and trust basis.** Compiled all three modules with `lcompile.py --all`; compilation completed without errors or warnings. The item has no `sorry`; the only remaining holes are the two named public split-off theorems, each exactly `by sorry` in its own module and documented with source and blueprint node. No axiom, unsafe, opaque, extern, implemented_by, or hollow definition was found. Axiom probes report only the expected `sorryAx` in the two open split statements and transitively in the assembled theorem. Verdict: pass.

3. **New statements.** Read both nodes, their Lean statements, the source passages in `cohomology.tex`, and existing APIs. `relativeMV_cover_homotopy_data` is the unrestricted resolved cover comparison for arbitrary derived coefficients and explicitly requires the cover equality. `standardSingle_open_relative_arrow` is the single-open coordinate/coefficient normalization and asserts only an arrow isomorphism, not invertibility of the comparison arrow. Existing cone-presentation results impose absent affine, compactness, or quasi-coherence hypotheses and do not supply the prescribed components. Edge cases remain included. Verdict: pass; no statement correction needed.

4. **Shortest route and pruning.** Searched local declarations plus LeanFinder, Loogle, and grep. No existing unrestricted theorem duplicates either split interface. The assembly uses the cover theorem, three open normalizations, the biproduct arrow isomorphism, and the supplied homotopy cone map. Removed imports are still needed transitively by the cover theorem; no target-reachable module was incorrectly claimed pruned. Verdict: pass.

5. **DAG and unit agreement.** Checked that each node's `proof_deps` is the union of declarations used by its proof steps, and that each Lean record is verbatim. The original node's proof route records the two split interfaces and normalization steps. The unit has empty `realized` lists, so no realized unit statement or step was bypassed. Verdict: pass.

Changed after this reading: appended this review only. No Lean proof, statement, node, import, or definition required repair.
