## What changed

Added a named intermediate theorem for the finitely generated subextension step and
used it to prove `Algebra.separableExtension_bot_residueField` by unfolding
`IsSeparableExtension`. The existing smoothness theorem remains proved from the
separability transfer and regular-local criterion.

## Proved and sorry left

Proved `Algebra.separableExtension_bot_residueField` by reduction to the named
intermediate theorem. Proved `Algebra.smoothAtPrime_bot_of_isSeparable_fractionRing`.
One sorry remains in `Algebra.separableExtension_bot_residueField_finitelyGenerated`.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The residue-field separability transfer requires an explicit finitely generated
subextension transport step; this was split into a new node.

## New nodes

`lem-weil-pbc-smooth-at-generic-point-over-field-residue-separable-fg`.

## Second reading by A3

1. Compared the delivered module with the repository version. Existing declaration
signatures are unchanged; the only added declaration is the reported split node.
Verdict: pass.
2. Compiled the module with `lcompile.py`; it is error-free. The only remaining
`sorry` is the named split theorem, and no forbidden declarations or hollow
definitions were introduced. Verdict: pass.
3. Checked the split statement and searched the library for an existing equivalent.
It is a strict finitely generated reduction of the parent statement and is needed
by its proof. Verdict: pass.
4. The proof follows the finitely generated transport route and leaves no imports
that can be removed. Verdict: pass.
5. Updated the parent node's proof and `proof_deps` to name the split node, and
added the split node with matching Lean declaration metadata. The unit route is
preserved. Verdict: pass.

Changed the split theorem docstring to include its blueprint and proof description,
and corrected the DAG files so the original parent node and the new split node are
both delivered.
