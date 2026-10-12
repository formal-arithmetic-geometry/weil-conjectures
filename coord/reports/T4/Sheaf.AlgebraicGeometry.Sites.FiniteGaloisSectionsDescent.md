## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.finiteGaloisSectionsDescent` with a direct proof of its unchanged statement. The singleton spectrum map is a covering because field spectra have one point. Mathlib's `Presieve.isSeparatedFor_singleton` proves injectivity; functoriality and `etaleSpecMap_comp` prove invariance. The existing `AlgebraicGeometry.finiteGaloisTensorDecomposition` gives equality of the two restrictions of an invariant section. Factoring arbitrary pairs of site maps through the scheme pullback supplies compatibility, and `Presieve.isSheafFor_singleton` gives descent.

Removed the first worker's three proposed auxiliary theorems and their new node files, rather than delivering their unproved split. No existing statement, definition, visibility, or import changed. No change record is needed.

## Proved and sorry left

Closed the original module hole: `AlgebraicGeometry.Scheme.finiteGaloisSectionsDescent` (node `lem-exc-finite-galois-sections-descent`). Holes added: none. Sorry left in delivered modules: none. This is a proof from the existing dependency declarations, not a decomposition into new holes; the module-local net is one hole closed and zero added.

The pre-existing dependency `AlgebraicGeometry.finiteGaloisTensorDecomposition` is still open and is not delivered here. An explicit scratch `#print axioms` of both it and `finiteGaloisSectionsDescent` returned exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. Thus this closes the local proof hole, while the target's import closure remains dependent on existing open work.

The proposed holes `finiteGaloisSectionsDescent_mapsTo`, `finiteGaloisSectionsDescent_injective`, and `finiteGaloisSectionsDescent_surjective` were removed before delivery. They never enter the library.

## No longer needed

No existing imports, proof-dependency nodes, or modules were pruned. Every node in the repository version's old `proof_deps` remains used: `lem-weil-pbc-finite-separable-extension-etale` supplies the etale field instance; `def-weil-pbc-etale-sheaf-of-sets` supplies the singleton-cover sheaf condition; `def-weil-affine-spectrum` supplies the spectrum maps; `lem-exc-finite-galois-tensor-decomposition` supplies the projection formulas and section equivalence. The tensor-decomposition import remains a plain proof-only import.

The three auxiliary node files proposed by the first worker were discarded. They were not part of the old library or its old proof dependencies.

## Where the brief, the DAG or earlier work was wrong

The first worker's three sorry docstrings lacked complete natural-language proofs, and their common DAG step vaguely cited tensor decomposition even for invariance and injectivity. Those two components follow immediately from functoriality and singleton-cover separatedness. The entire descent argument can be formalized directly against the already-stated tensor-decomposition theorem, so no auxiliary holes or new nodes are needed.

The original target statement and literature route are correct. Checked the direct proof in Stacks Project Tag 04JM at https://stacks.math.columbia.edu/tag/04JM: equality of the two restrictions along the Galois self-intersection is followed by unique sheaf descent. The local Stacks source file was unavailable on this machine, so the published tag was read directly.

## Second reading by T4

1. Compared the delivered module with the repository version using `diff`, and asserted equality of the complete text preceding the original proof body. Verdict: the existing signature, docstrings, imports, and visibility are byte-for-byte unchanged; no definition was changed and no change record is required.

2. Compiled the initial worker version and the repaired delivered module through `lcompile.py`; the final file compiles without errors or warnings. Read the whole proof and scanned for forbidden declarations and hidden sorry. Verdict: no sorry, axiom, unsafe, opaque, implemented_by, or extern in the delivered module. Scratch `#print axioms` confirms only the three permitted axioms and the existing dependency's `sorryAx`; no arbitrary data is chosen from an unproved existence theorem.

3. Reviewed all three proposed component statements: they are true strict components, but unnecessary as new holes. Searched upstream and `lean/Sheaf` with `rg`, and used independent LeanFinder and Loogle searches for covering-map injectivity and compatible-section descent. Mathlib's singleton-cover lemmas and the existing tensor theorem suffice. Verdict: removed all three auxiliary statements and nodes; no split-off statements remain to deliver. Small cases checked mathematically: E=L makes the pullback and descent identities; empty sections make injectivity and surjectivity vacuous; a terminal singleton sheaf descends its sole section; nontrivial Galois extensions use all automorphisms through beta without requiring a section of the field extension.

4. Read the target from the top down and used the shortest available route while retaining the Galois tensor decomposition of the original plan. Read `dag/units/sk-prop-h2.json`: this auxiliary descent node is not one of its `realized` statement or step nodes; its fixed Kummer/Brauer route is untouched. Verdict: no unit route is bypassed, no old proof dependency is omitted from the pruning report, and no new hole is introduced.

5. Read the existing node and each proposed auxiliary node against the Lean. Replaced the proposed auxiliary-based plan by three explicit steps matching the singleton-cover, functoriality, and tensor/pullback descent proof; retained exactly the original four proof dependencies and the document source. Verdict: the delivered node's `proof`, `proof_deps`, and `proof_origin` agree with the final Lean, with all other node fields unchanged.

Changes by the second reader: wrote the complete direct reduction to existing declarations; removed the three proposed auxiliary theorems and their nodes; repaired the existing node's proof plan; rewrote this report with exact hole accounting and the inherited axiom limitation. No new modules, declarations, or nodes are delivered.
