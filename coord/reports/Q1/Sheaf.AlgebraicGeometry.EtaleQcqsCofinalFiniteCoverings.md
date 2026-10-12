## What changed

Proved `AlgebraicGeometry.etale_qcqs_cofinal_finite_affine_coverings` with its statement unchanged. Replaced the private proof import of `Sheaf.AlgebraicGeometry.QcqsSchemeCofinalFiniteCoverings` by private imports of `Mathlib.AlgebraicGeometry.Cover.QuasiCompact` and `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`. Kept all existing public imports and the original docstring. Updated the node's proof, proof_deps and proof_origin to the direct Mathlib route already identified in its original split_report.

The input sieve gives a jointly surjective scheme cover. `QuasiCompactCover.exists_hom` refines it by finitely many spectra; a cover morphism gives the factorization, and the cover gives surjectivity. Reindexing through an equivalence with an ULift of a Fin type handles the completely arbitrary output universe. Compactness of the pairwise pullbacks follows by instance inference from affineness and quasi-separatedness of U. No intermediate statements were added. The empty scheme and empty input index are permitted, and no nonempty index or positive finite cardinal was assumed. The item is not a unit realization in `dag/units/sk-thm-p1.json`, so this shortcut is below the preserved unit route.

Searches actually run: LeanFinder for finite affine refinement of an etale covering of a quasi compact scheme; Loogle for `AlgebraicGeometry.QuasiCompactCover.exists_hom`; and grep for `QuasiCompactCover.exists_hom|quasiCompact_of_compactSpace`. Their log is in the sandbox's searches.jsonl. Read the actual Mathlib theorem, cover constructors, over-category constructors, and compactness instances. Local compilation passed cleanly. Both new proof imports are needed: removing UniversallyOpen makes `Scheme.Hom.isOpenMap` unavailable; Cover.QuasiCompact supplies the refinement theorem.

## Proved and sorry left

Proved `AlgebraicGeometry.etale_qcqs_cofinal_finite_affine_coverings` (node `lem-weil-pbc-etale-qcqs-cofinal-finite-coverings`), the sole original sorry. No sorry remains in the item and no sorry was added elsewhere. The proof uses only Mathlib, so it does not inherit any Sheaf sorry.

## No longer needed

Removed import and proof dependency: `Sheaf.AlgebraicGeometry.QcqsSchemeCofinalFiniteCoverings`, node `lem-weil-pbc-qcqs-scheme-cofinal-finite-coverings`.

Removed proof dependencies: `lem-weil-pbc-etale-covering-base-change`, `lem-weil-pbc-etale-composition-cancellation`, and `def-pc-fibre-product`. The fibre-product definition remains a statement dependency and its public Mathlib support remains imported. The base-change and composition dependencies were Mathlib leaves rather than additional Sheaf modules. No affine open cover of U, restriction to affine base pieces, or assembly of local refinements is needed. This is pruning from this item's proof; other callers may still need these nodes.

Retained `lem-weil-pbc-etale-covering-affine-refinement` as the record for the actual Mathlib declaration `QuasiCompactCover.exists_hom`, and retained the spectrum compactness, qcqs permanence, and site-definition nodes used by the new route. No unit statement or step is pruned.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original DAG already recorded the shorter Mathlib route. Its natural-language affine-refinement node is specialized to an affine base, whereas its recorded Lean declaration `QuasiCompactCover.exists_hom` needs only a compact base. The proof uses that checked, stronger Mathlib signature directly; it does not apply the specialized informal statement to a non-affine base. In the compiled Mathlib version, the finite refinement index initially has the input cover's universe; explicit finite reindexing is required for the theorem's independent universe w. The original docstring describes the old route and is preserved as existing API; the updated node and this report describe the implemented proof.

## Second reading by Q1

1. Visibility and statements: PASS. Compared the sole delivered Lean module with the
repository version using diff, and separately compared the theorem signature byte for
byte. Its hypotheses, conclusion, public imports, existing docstrings, and all definitions
are unchanged. Only its proof, a declaration-local elaboration option, and private proof
imports differ. No statement change or change record is required.

2. Proof and trust: PASS. Independently compiled the module through lcompile.py without
errors or warnings. Compiled a scratch copy with `#print axioms
AlgebraicGeometry.etale_qcqs_cofinal_finite_affine_coverings`: exactly `propext`,
`Classical.choice`, and `Quot.sound`. Scanned the delivered Lean file: no sorry, axiom,
unsafe, opaque, implemented_by, extern, or kernel-check bypass. Read the covering-sieve
criterion, QuasiCompactCover.of_isOpenMap and exists_hom, and the quasi-compact morphism
and compact pullback instances in the pinned Mathlib sources. The refinement really
factors through the given family and really covers U.

3. Split-off statements: PASS, vacuous. There are no new declarations, no new nodes,
and no split-off sorry. Checked the empty-scheme/empty-family cases: the argument never
requires a nonempty index or a positive cardinal. The equivalence with ULift of Fin
preserves all members and works in the independent output universe w.

4. Top-down route and pruning: PASS. The direct Mathlib refinement followed by compact
pullback instances is the shorter route already recorded in the original node. Searched
lean/Sheaf/AlgebraicGeometry and the upstream cover module with finite/affine/refinement
and exists_hom terminology; found no ready-made stronger theorem that shortens this
argument. Both private imports provide declarations used by the proof; public imports
support the existing signature and remain unchanged. Compared the old and new proof_deps:
all four removed entries are listed under No longer needed, including the fibre-product
node that remains a statement dependency. Read sk-thm-p1.json realized: neither this item
nor the removed dependencies realize a unit statement or step, and no unit route is
bypassed.

5. Nodes versus Lean: PASS. The only changed node fields are proof, proof_deps, and
proof_origin. Checked their four steps against the code and verified proof_deps equals
the union of step uses. Read the retained dependencies' Mathlib matches. In particular,
the affine-refinement node records the actual general Mathlib declaration used on the
compact, possibly non-affine base; the node and report explicitly distinguish that from
its narrower informal specialization. No new-node requirements apply.

Second-reading changes: appended this independent review only. No Lean or DAG repair
was necessary; retained the existing proof and existing docstrings.
