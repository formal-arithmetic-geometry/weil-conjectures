## What changed

Proved `AlgebraicGeometry.exists_nonempty_normal_open` in
`Sheaf.AlgebraicGeometry.FiniteDenseNormalOpen`, with its signature unchanged. Reused the
principal-open construction from the proved source-library theorem
`Scheme.exists_isIso_fromNormalization_restrict`: Noether finiteness, a common denominator,
normality of the localization, and normality of its stalks. Updated the docstring and DAG proof
to match. All existential choices occur within a theorem proof; no definitions were added.

The module compiles through `lcompile.py` without warnings. The argument works in arbitrary
characteristic, including imperfect fields, using the general finite integral-closure theorem.
The chosen denominator is nonzero, and the generic point witnesses nonemptiness. No global
quasi-compactness is needed by the proof, but the original hypothesis stays unchanged.

## Proved and sorry left

Closed: `AlgebraicGeometry.exists_nonempty_normal_open`
(`lem-fin-dense-normal-open`), the sole original hole: 1 of 1 proved.
Added holes: none. Remaining holes in delivered Lean modules: zero. No decomposition.

## No longer needed

Removed proof imports `Sheaf.AlgebraicGeometry.NormalScheme` and
`WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`. The proof instead imports
`WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField` and
`WeilConjectures.Mathlib.RingTheory.DedekindDomain.IntegralClosure`.

Removed direct proof dependencies `def-fin-normalization-extension`,
`lem-fin-normalization-extension-finite`, `def-sbc-normal-dominant-galois`, and
`lem-weil-pbc-integral-closure-finite-extension-normal`; removed the last node from
`tool_uses`. The argument constructs the principal open directly and never constructs the
normalization scheme or invokes the normal-scheme predicate. The elementary denominator
criterion proves normality directly, so integral-closure normality is unnecessary.
The finiteness input is the existing proved node
`lem-weil-pbc-finite-type-field-integral-closure-finite`, specialized to the identity extension.
These are removals from this proof, not assertions that other users no longer need the nodes.

## Where the brief, the DAG or earlier work was wrong

No statement defect. The original DAG routed finiteness through the normalization scheme,
although the existing ring-level Noether finiteness result supplies exactly the needed input.
The source-library proof of the dense-open normalization isomorphism already contains the
entire requested normal-open construction. Its reuse preserves the blueprint's affine,
common-denominator and localization argument; the unit route is unchanged.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
