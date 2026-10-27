## What changed

Proved `AlgebraicGeometry.AlgebraicSpace.representable_etale_kernel_relation` with its
original signature and public imports unchanged. Evaluating the given presheaf pullback
and applying Mathlib's `PullbackCone.IsLimit.equivPullbackObj` constructs the specified
sectionwise bijections. Their injectivity proves the scheme monomorphism through
`Over.mono_left_of_mono`; their image characterization gives the equivalence relation,
diagonal, and factor-switching involution.

A fully proved private helper transfers a scheme-test morphism property to any supplied
representing pullback. It uses the unique pullback isomorphism and fully faithful Yoneda,
then invariance under precomposition by an isomorphism. Applying it to surjectivity and
etaleness, with both orientations of the kernel square, proves all four projection
properties. No other library module or public interface changes. The item's node now
records the implemented argument and its actual dependencies.

The proof uses the Lean 4 skill at `/home/ubuntu/.codex/skills/lean4/SKILL.md`.
The complete proof compiled in 4.0 seconds through the required remote `lcompile.py`
compiler. The first delivery axiom probe passed; its warning gate required an explicit
reference to the redundant `hrep` hypothesis, which is now included without changing
the signature or disabling a linter. The final delivery recompiles and audits the proof.
No private helper contains a hole.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.AlgebraicSpace.representable_etale_kernel_relation`
(node `lem-a1-representable-etale-kernel-relation`).

Holes closed: 1 of 1. Holes added: 0. Holes remaining in the item: 0.
There are no split-off statements or new modules in the delivery. The proof uses
Mathlib and the existing scheme-test definitions, without a further sorried theorem.

## No longer needed

Removed the proof-only imports `Mathlib.CategoryTheory.Sites.Limits` and
`WeilConjectures.Mathlib.CategoryTheory.Yoneda`. The former's extra sheaf-limit
construction is unnecessary because `hR` already asserts a presheaf pullback;
Mathlib's evaluation functor and explicit pullback equivalence suffice. The latter's
special representing-object theorem is unnecessary: the pullback isomorphism and
Mathlib's `yoneda.preimageIso` provide the required compatible scheme isomorphism.
The only added private import is `Mathlib.CategoryTheory.Limits.Types.Pullbacks`.
All original public imports are preserved.

Removed `lem-weil-pbc-site-sheaf-sets-limits-sectionwise` and `def-pc-fppf-site` from
this node's direct proof dependencies. The site remains a statement dependency;
the proof works with the already supplied presheaf square. The representing-object
uniqueness node `lem-pc-representable-unique` remains used through its Mathlib leaf,
and `def-pc-fibre-product` and `def-trf-algebraic-space` remain used.
No node or module is withdrawn, and no claim of global unreachability is made.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was found. The DAG's first step can be
shortened because the Lean hypothesis is already an `IsPullback` of presheaves,
so no passage from a sheaf limit is necessary. The rest of the five-step plan is
implemented directly. Empty schemes, an identity atlas, and a represented target
need no additional hypotheses or case splits. Both the unit route and the item's
mathematical statement are preserved.

## Second reading by D8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
