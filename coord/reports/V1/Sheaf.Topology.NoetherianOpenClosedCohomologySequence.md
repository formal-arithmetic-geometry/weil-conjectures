## What changed

Proved `TopCat.noetherian_open_closed_cohomology_sequence` without changing its statement.
Added proof-only imports of `Sheaf.Topology.SliceOpenClosedShortExact` and
`Sheaf.Topology.SliceOpenExtensionClosureUnit`. The proof constructs the presheaf counit
by summing identity maps, checks naturality on injections, lifts it through sheafification,
and proves the stipulated injection formula. It then applies the exactness step, chooses
the inverse image on the closure as F', and composes the closed-immersion cohomology
comparison with the evaluated cohomology functor applied to the inverse support isomorphism.

`TopCat.slice_open_extension_closure_unit_isIso` is also proved: outside U the direct sum
has no indices, hence the presheaf stalk is zero; sheafification preserves stalks. On the
closure, the unit stalk map followed by the closed-pushforward comparison is the
inverse-image stalk isomorphism, by their germ formulas. Off the closure both stalks are
zero. The generic abelian-sheaf stalkwise isomorphism criterion finishes the proof.

Both new modules have matching new nodes. The original node now records the actual
reduction. All original public imports and existing signatures are preserved. The second reader made
`Mathlib.Topology.Sheaves.Abelian` a proof-only import in the new closure-unit module.

## Proved and sorry left

Proved `TopCat.noetherian_open_closed_cohomology_sequence` (the original single sorry)
and `TopCat.slice_open_extension_closure_unit_isIso`
(`lem-sc-slice-open-extension-closure-unit`). These are proofs from existing library
statements, so they still transitively use the sorries of inverse-image stalks,
closed-pushforward stalks, and closed-immersion cohomology comparison.

The only new sorry is `TopCat.slice_open_closed_short_exact`
(`lem-sc-slice-open-closed-short-exact`, module `Sheaf.Topology.SliceOpenClosedShortExact`).
It is strictly the exactness part of the argument: it neither constructs a nor gives
its section formula, the closure-support isomorphism, or any cohomology comparison.
Its hypotheses pin the input a as the canonical sheafified counit. Its docstring and
node give the complete two-case stalk argument and the required model identification.

## No longer needed

No original import was removed and no original dependency is globally pruned.
The following original `proof_deps` are no longer direct dependencies of the item:
`lem-sc-topological-extension-by-zero-stalks`,
`lem-sc-closed-pushforward-abelian-stalks`,
`lem-sc-abelian-sheaf-short-exact-stalkwise`,
`lem-weil-pbc-sets-sheaf-iso-on-stalks`, and
`lem-weil-pbc-topological-inverse-image-stalk`.
They remain reachable through the new exactness or closure-unit nodes; none is globally
unnecessary. The other two original dependencies, the inverse-image definition and
closed-immersion cohomology comparison, remain direct dependencies.
The new closure-unit module retains `Mathlib.Topology.Sheaves.Abelian` privately for
proof tools and instances; it is not required as a public import by its statement.
The extension-by-zero stalk lemma and stalkwise short-exactness criterion are delegated
to the new exactness node; closed-pushforward and inverse-image stalk lemmas are used by
the proved closure-unit node. The closure-unit proof needs no comparison between the
slice extension and topological extension: empty direct sums prove outside stalk
vanishing directly, and Mathlib's generic AddCommGrpCat stalkwise isomorphism criterion
avoids the underlying-sets/additive-inverse detour of the old step 4.

## Where the brief, the DAG or earlier work was wrong

No statement was found false. The existing extension-by-zero stalk theorem uses an
open-subspace model, whereas the item uses `F.over U` on the slice. Identifying those
models and their counits is genuine glue, now explicitly included in the exactness
node rather than silently treating their objects as definitionally equal.
The closure-support branch is fully formalized without that glue. Noetherianity is
unused by these local results, as in the original mathematical plan.
The unit `sk-thm-curveestimate` realizes only `thm-sc-proper-cohomology` and has no
realized proof steps affected by this node-level reduction.
The cited Stacks TeX files are absent on this machine; their official pages were read:
https://stacks.math.columbia.edu/tag/02UT,
https://stacks.math.columbia.edu/tag/02UZ, and https://stacks.math.columbia.edu/tag/02UV.

## New nodes

`lem-sc-slice-open-closed-short-exact`: canonical exactness for a slice-site open extension,
with the two stalk cases and the model/counit identification left as one named theorem.
It holds for arbitrary topological spaces. For U empty, a has zero source and the
complement unit is an isomorphism; for U=X, a is an isomorphism and the last sheaf is zero.
These cases also justify that the section-formula hypothesis pins exactly the intended map.

`lem-sc-slice-open-extension-closure-unit`: the specific closure adjunction unit is an
isomorphism, proved from existing stalk comparisons and generic Mathlib tools. Empty U,
dense U, empty X, and the zero sheaf cause no exception: the proof uses empty-sum stalk
vanishing off U and the inverse-image unit formula at every point of the closure.

No change record is needed: existing definitions, statements, and public imports are unchanged.

## Second reading by V1

1. Compared every delivered module with the read-only repository. Only the item's
   module already exists; its theorem signature and docstring are byte-for-byte
   unchanged. Its diff adds two ordinary imports and replaces its proof. Both other
   modules are new. No definition or target statement is changed; no change record
   is required. Verdict: pass.
2. Compiled all three files in import order with `lcompile.py --all`; no errors or
   warnings. Searched all delivery Lean files: the sole `sorry` is the named exactness
   theorem listed above, and no forbidden construct occurs. Scratch-copy
   `#print axioms` for all three declarations reports exactly `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. The item and closure-unit proofs
   therefore close their local holes, not the entire upstream axiom closure.
   Verdict: pass with explicitly recorded remaining upstream sorries.
3. Read the exactness statement, docstring, node, and the available open-extension,
   closed-pushforward, inverse-image, and stalkwise exactness statements. Its injection
   hypothesis determines the presheaf map on every direct-sum generator and hence
   the sheaf map by sheafification uniqueness. Tested empty U, U=X, empty X, the
   zero sheaf, and a proper open in a two-point space: the stalk sequences are
   respectively identity followed by zero or zero followed by identity. This is
   strictly the exactness component, without construction of a, closure support,
   or cohomology comparison. The closure-unit proof checks equality on germs before
   cancellation of isomorphisms and handles both zero stalks off the closure.
   Repeated searches with different words using leanfinder, loogle, msearch grep,
   and rg in lean/; no existing theorem matches the slice-model exactness statement.
   The generic stalkwise isomorphism criterion is already used directly. Consulted
   the official [02UT](https://stacks.math.columbia.edu/tag/02UT) and
   [02UZ](https://stacks.math.columbia.edu/tag/02UZ) source pages. Verdict: pass.
4. Followed the proof from the top: the counit and its formula are proved directly,
   only exactness is postponed, closure support is proved from existing stalk tools,
   and the cohomology comparison is transported by functoriality in the correct
   direction. All original imports are needed by the existing signature; the two
   new imports of the item are proof-only. The Abelian import of the new closure
   module was unnecessarily public and is now ordinary. The report now explicitly
   lists all five old dependency edges delegated to the new nodes; no globally
   unused node is claimed. Checked `dag/units/sk-thm-curveestimate.json`: its realized
   statement remains `thm-sc-proper-cohomology`, with no realized steps bypassed.
   Verdict: pass after import and reporting repair.
5. Compared the three node records with their Lean declarations and proof routes.
   The original node's steps construct the sheafification lift, invoke the two new
   statements, and transport the closed-immersion comparison. New nodes have source,
   complete proof plan, dependency union, three search kinds, creation provenance,
   blueprint origin, chapter/unit, and matching Lean records. The sheafification
   and stalkwise-isomorphism node references name Mathlib tools actually used.
   Verdict: pass.

Changed only the new closure module's Abelian import visibility and completed the
report's direct-dependency and axiom accounting. The exactness split requires the
slice/open-subspace model comparison and a stalkwise exactness proof; it is not a
few-minute missing tactic, so its sourced named statement remains open.
