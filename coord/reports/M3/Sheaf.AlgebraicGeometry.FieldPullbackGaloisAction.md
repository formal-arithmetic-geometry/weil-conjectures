## What changed

Completed `AlgebraicGeometry.Scheme.fieldPullback_galoisAction` without changing
its statement or either existing definition. Only the assigned Lean module and
its own DAG node are changed. The proof constructs the restriction functor's open
stabilizers, computes the actual canonical stalk comparison on unit germs,
checks equivariance using an extending automorphism of Omega, assembles the
natural isomorphism, and identifies global pullback with the identity on the
underlying invariant elements. Three proved private helpers handle the canonical
germ calculation, terminal sections and transport of invariants.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Scheme.fieldPullback_galoisAction`
(node `lem-per-field-pullback-galois-action`). No holes added or split off.
No `sorry` remains in any delivered declaration. Server single-file validation
compiled the complete proof in 17.7 seconds, below the 60-second limit. A scoped
heartbeat allowance covers elaboration through the nested bundled functors;
it does not change the wall-clock limit. The proof uses the existing
`IntermediateField.separableClosure_restriction_image` for continuity; this
pre-existing dependency remains a separate item.

## No longer needed

The proof does not invoke
`AlgebraicGeometry.inverseImage_stalk_germ`: its existential conclusion does
not specify that the comparison is `Etale.upperStarCompSheafFiberIso`, as the
item's conclusion requires. The private canonical germ lemma proves that
normalization directly from the general-site formulas, following the proof in
`WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm`. Its private import and
proof edge `lem-weil-pbc-inverse-image-stalk-germ` are removed.

The proof uses the supplied `hK` and `hL`, so it does not invoke
`abelianSheaves_equiv_discreteGModules_action` or construct a fresh abelian
stalk equivalence. The redundant private import
`Sheaf.AlgebraicGeometry.AbelianSheavesGModulesAction` and the corresponding
proof edges are removed. The public `AbelianSheavesGModules` import and the
statement dependency `lem-exc-abelian-sheaves-gmodules` remain. No claim is made
that these modules can be withdrawn globally. No unit statement or step is
bypassed. No source-library declarations are changed or removed.

## Where the brief, the DAG or earlier work was wrong

The planned use of the existential `inverseImage_stalk_germ` lemma alone was
insufficient to identify the specifically named canonical stalk isomorphism in
the conclusion. The proof now computes that isomorphism's normalization
explicitly, using the same source argument. The displayed scalar towers also
need to be composed explicitly when Lean uses the two global-section lemmas.
The mathematical statement is unchanged; no definition repair was needed.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
