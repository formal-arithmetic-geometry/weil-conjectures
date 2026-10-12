## What changed

Proved `AlgebraicGeometry.Scheme.dim_eq_iSup_ringKrullDim_of_affineOpenCover`
in `Sheaf.AlgebraicGeometry.DimensionAffineOpenCover`, with its signature unchanged.
Added the proof-only import `Mathlib.RingTheory.Ideal.Height`.
The proof uses the given chart isomorphisms directly, transports stalk dimensions
through open-immersion stalk maps, identifies spectrum stalks as localizations,
and combines the supremum-of-heights formula with the two cover inequalities.
Updated the item's DAG proof, proof dependencies, and proof origin to match.

## Proved and sorry left

Proved the module's only original sorry:
`AlgebraicGeometry.Scheme.dim_eq_iSup_ringKrullDim_of_affineOpenCover`
(node `lem-pc-dimension-affine-open-cover`). No sorry remains in the delivery,
and no intermediate statements were split off. The proof does not use
`Scheme.dim_eq_topologicalKrullDim`, the still-unproved comparison in Dimension.
Local compilation is clean. The proof treats empty charts through the empty
supremum in `WithBot ℕ∞`; it uses no nonemptiness of individual charts and imposes
no finiteness on the index type. The arbitrary index universe is preserved.

## No longer needed

Pruned dependency `lem-weil-pbc-affine-open-spec-points`: the supplied isomorphism
already provides the chart points, so constructing a canonical spectrum of the
ring of sections is unnecessary. Its Mathlib declarations `IsAffineOpen.fromSpec`,
`range_fromSpec`, `primeIdealOf`, and `fromSpec_primeIdealOf` are not used.
No original import was removed: Dimension supplies Scheme.dim, and Restrict
supplies the open subscheme in the statement and its inclusion in the proof.
No additional Sheaf or WeilConjectures modules are required.
The topological comparison node `lem-pc-scheme-dimension-local-rings` is also
unneeded, as already noted in the original DAG; this delivery uses the defining
supremum of stalk dimensions directly.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The planned passage from a chart to its ring of
sections can be omitted because the statement already supplies its isomorphism
to Spec(A i). The DAG now explicitly cites the existing Mathlib leaf
`lem-weil-pbc-spec-domain-stalks-function-field` clause (1) for localization of
spectrum stalks, alongside the open-immersion stalk-map declaration recorded in
`lem-weil-pbc-affine-open-stalk-localization` clause (b).
Search of the existing library and Mathlib found the necessary ingredients;
LeanFinder returned affine-cover definitions and covering lemmas, not the
complete theorem. No new nodes, definition changes, or statement changes.

## Second reading by V1

1. Compared every delivered Lean module with the repository version: the existing
   theorem signature, definitions, docstring, universes, and public imports are byte
   for byte unchanged. Only the proof and a plain proof-only Height import were added.
   Verdict: pass; no change record is needed.
2. Compiled the module locally without errors or warnings. A scratch copy with
   `#print axioms AlgebraicGeometry.Scheme.dim_eq_iSup_ringKrullDim_of_affineOpenCover`
   reports exactly `propext`, `Classical.choice`, and `Quot.sound`, without `sorryAx`.
   There is no sorry or forbidden declaration in the delivered Lean. Verdict: pass.
3. No statements were split off and no new nodes were added. Checked the supplied
   chart inverse and open-immersion stalk maps, the spectrum localization instance,
   and the height formula against the existing Mathlib leaf records. Empty charts
   have empty spectra and contribute bottom; infinite covers require only complete
   lattice suprema; an empty index type cannot cover the assumed nonempty scheme.
   Verdict: pass.
4. Searched the library again by `dim_eq_iSup`, `ringKrullDim.*affine`, and
   `affine.*ringKrullDim`: no existing replacement for the complete theorem appeared.
   The direct chart route already uses the necessary Mathlib ingredients and avoids
   the unproved topological comparison. Both original public imports support the
   statement; Height is proof-only. The one removed old proof dependency is fully
   listed under No longer needed. The unit record sk-thm-picard-rr has empty realized
   entries and names no mandated step this proof bypasses; its route is unchanged.
   Verdict: pass.
5. Compared the node JSON with its repository version: only proof, proof_deps, and
   proof_origin changed. Checked each dependency against the actual Lean ingredients;
   the union of step uses equals proof_deps. The statement and statement dependencies
   remain unchanged. Verdict: pass.

Second reading changed only this report by adding the independent review record;
no repair to the correct Lean proof or DAG metadata was needed.
