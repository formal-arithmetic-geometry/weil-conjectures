## What changed

Proved `AlgebraicGeometry.fpqc_affine_model_transition_cartesian` with its existing
signature and declaration docstring unchanged. The canonical restriction square is proved
by pullback cancellation and pasted with `hp B`. The fpqc singleton over U is obtained by
base change of `hf`. Mathlib's
`CategoryTheory.Precoverage.ZeroHypercover.isPullback_of_forall_isPullback` checks the
flipped desired square on that cover. The local square is the flipped pasted square,
transported along `(hp U).isoPullback`. Flip back and use the supplied commutativity `ht`.

Removed the proof-only import `Sheaf.AlgebraicGeometry.FpqcMorphismsDescend` and added the
proof-only import `Mathlib.CategoryTheory.Sites.Hypercover.Subcanonical`. Both existing
public Mathlib imports remain because the signature uses their fpqc and directed-cover
interfaces. Added a copyright header and module documentation. Updated only `proof`,
`proof_deps`, and `proof_origin` in the existing DAG node. No public signature, definition,
other module, or unit record changed.

Sources read: [Stacks Tag 02W3](https://stacks.math.columbia.edu/tag/02W3), the nested-affine
comparison paragraph, and [Tag 023Q](https://stacks.math.columbia.edu/tag/023Q), fpqc
subcanonicity. Read Mathlib `Sites/Hypercover/Subcanonical.lean`, including the proof of
the pullback criterion, and `AlgebraicGeometry/Sites/Fpqc.lean`. The criterion implements
the comparison-isomorphism argument through locality of isomorphisms on a subcanonical
site, so no private reconstruction of effective-epimorphism descent is needed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.fpqc_affine_model_transition_cartesian`
(node `lem-galois-fpqc-affine-model-transition-cartesian`).

Added zero holes, zero split-off statements, and zero new nodes. No `sorry` remains in
the delivered module. The three proved private helpers of the first worker's candidate
are no longer needed and have been removed. This is a proof, not a decomposition.

The final file compiles without warnings through `lcompile.py`. An independent scratch
copy with `#print axioms AlgebraicGeometry.fpqc_affine_model_transition_cartesian`
reports exactly `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

Removed import/module `Sheaf.AlgebraicGeometry.FpqcMorphismsDescend` and old direct
`proof_deps` entry `lem-galois-fpqc-morphisms-descend`. This is the complete difference
between the old and new direct dependencies. No claim is made that the module is
unreachable from other callers. The canonical descent isomorphisms and inverse
compatibility machinery of that route are not used. The other old dependencies,
`def-pc-fibre-product` and `lem-galois-fpqc-covering-base-change`, remain used; the Mathlib
leaf `lem-weil-pbc-fpqc-representable-descent` supplies fpqc subcanonicity.

## Where the brief, the DAG or earlier work was wrong

The first worker repaired an earlier duplicate scheme-specific effective-epimorphism
helper by generalizing it to arbitrary subcanonical precoverages. That candidate was
sound and compiled, but the second reader found the existing Mathlib pullback criterion
by searching for covers and subcanonical topologies rather than fpqc cancellation.
It replaces all three private helpers and their local compatibility argument.

The original DAG route through full faithfulness of morphism descent was valid but
longer than necessary. The final route keeps the comparison-isomorphism reasoning
inside Mathlib. No statement correction or forced adaptation is needed.

## Second reading by S1

1. Compared the only delivered Lean module with the repository using `diff -u`.
   The existing theorem signature, universe, namespace, public visibility, and entire
   declaration docstring are byte for byte unchanged. The changes are its proof,
   module documentation, and proof-only imports. There are no changed definitions,
   extra hypotheses, weakened conclusions, or other delivered modules. Verdict: pass.
2. Read the original candidate's universal-property argument, including compatibility
   for arbitrary pairs of maps over the cover and uniqueness by epi cancellation.
   It was sound. Replaced it with the Mathlib criterion and compiled the final file
   without errors or warnings. The scratch axiom probe gives only the three standard
   axioms. There is no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`,
   or data chosen from an unproved existence assertion. Verdict: pass.
3. No statements are split off and no new public declarations are introduced.
   Searched both library roots for fpqc singleton helpers and searched Mathlib for
   pullbacks local on covers and subcanonical hypercovers. Read the discovered
   `isPullback_of_forall_isPullback` statement and proof, rather than duplicating it.
   No affine or nonempty-model assumption is needed. Empty U, empty models, and the
   identity inclusion satisfy the same categorical argument; the singleton index is
   inhabited even when its scheme is empty. Verdict: pass.
4. Checked top-down reduction: projection equations identify the canonical restriction
   square; `IsPullback.of_right` proves it; pasting with `hp B` and rewriting `hr`
   gives the outer square. Base change of `hf` supplies the cover required by the
   Mathlib criterion, and `hp U` supplies precisely its pullback object. Both retained
   public imports occur in the signature; the new import is proof-only. The old direct
   dependency removed is fully listed above. Unit `sk-prop-h2` has empty `realized`
   entries, and no unit statement or route changes. Verdict: pass.
5. Compared the node JSON with its repository version. Only `proof`, `proof_deps`,
   and `proof_origin` change. Read each dependency's statement/Mathlib match: fibre
   products give the canonical squares and transport isomorphism, covering base change
   gives hq, and representable descent gives the fpqc subcanonical instance used by
   the criterion. The proof steps describe the actual Lean and their `uses` union is
   exactly `proof_deps`. No new node fields or change records are required. Verdict: pass.

Second reading changed: replaced three private proved helpers with the existing Mathlib
local pullback criterion, added its proof-only import, and updated module documentation,
the node's proof route, and this report. Existing signatures and declaration documentation
remain unchanged.
