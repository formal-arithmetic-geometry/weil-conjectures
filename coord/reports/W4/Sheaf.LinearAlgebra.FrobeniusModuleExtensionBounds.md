## What changed

Proved `FrobeniusModule.IsMixedOfWeightsAtMost.of_shortExact` by the original
filtration-splicing argument. Its public statement, universes, assumptions,
visibility, and public imports are unchanged. There are no additional imports.
Removed the inherited `set_option warn.sorry false`; all hole warnings are now
enabled, and the delivery axiom probe checks every declaration independently.

The filtration of A is mapped into B and followed by the inverse images of the
filtration of C. Exactness identifies the joining subspaces. Four private proved
helpers transport purity through the quotient isomorphism and establish the
stability of mapped and pulled-back subspaces. A private proposition abbreviation
`boundedPurePiece` packages the existing graded-piece condition so that dependent
rewrites retain the quotient's finite-dimensional instance. It contains no holes
and occurs only inside the proof.

Repaired the return at head `f2ecfdafc` reporting an unattributed hole at line 23,
offset 715. The hole scanner matches the `sorry` component of `warn.sorry` as a
hole token. Removing this unnecessary warning-suppression option fixes the
reported rejection without changing any declaration or patching a tool.
The final proof does not use the previous eigenvalue-to-mixedness route or its
holed dependency. Also repaired retained compiler errors in index arithmetic and
dependent quotient rewrites, and replaced the stale report and node proof route.
The node now records the implemented filtration argument. No consumers or
interfaces require adaptation; no definition of the library was changed.

Added `coord/changes/frobenius-extension-bounds-warning-option.md` because
preflight requires a change record for removing the top-level warning option.
The downstream-use check confirms that consumers need no adaptation.

## Proved and sorry left

Closed 1 original hole:
`FrobeniusModule.IsMixedOfWeightsAtMost.of_shortExact`
(node `lem-a1-extension-bounds`). Added 0 holes; split off 0 statements.
There are no remaining holes in the item or any private helper.

The final module compiles through `lcompile.py`. An explicit `#print axioms`
check reports exactly `propext`, `Classical.choice`, and `Quot.sound` for the main
theorem, with no `sorryAx`. The diagnostic command was removed from the final file.

## No longer needed

No original imports, modules or DAG dependencies are pruned: the sole original
dependency `def-weil-frobenius-module-weights` is used directly.

Relative to the earlier returned packet, the proof no longer uses
`Sheaf.LinearAlgebra.FrobeniusPunctualBoundMixed`, node
`lem-a1-punctual-bound-module-mixed`, or
`WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Exact`.
Their proof imports are absent and the punctual-bound node is removed from this
node's proof dependencies. No new statements are needed for quotient transport;
its elementary linear algebra is proved locally.

## Where the brief, the DAG or earlier work was wrong

The retained report and node described an eigenvalue proof that the retained Lean
file no longer implemented. They now agree with the direct filtration proof and
its verified axiom closure. The original mathematical statement and filtration
plan are valid, and the unit route is preserved.

Edge cases include either filtration having length zero, both outer modules zero,
repeated filtration steps, and nonsemisimple Frobenius. The proof uses no strictness,
semisimplicity, or splitting assumption. The joining index is covered on both sides
by exactness, and surjectivity and injectivity are used for their respective quotient
identifications. All three independent carrier universes are retained.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
