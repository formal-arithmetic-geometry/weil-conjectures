## What changed

Proved `AlgebraicGeometry.Etale.closed_unbounded_compactSupport_normalization` in
`Sheaf.AlgebraicGeometry.ClosedUnboundedCompactSupportNormalization` with its signature
unchanged. A closed immersion is finite, so the existing source finite-pushforward
exactness instance applies to the actual ordinary module-sheaf functor. The witnesses
are the existing termwise factorization, the displayed identity-open comparison, and
`rightDerivedFunctorIsoMapDerivedCategory`. Its `hom_fac` lemma proves the specified
normalization of the actual unit. The source cohomology isomorphism and both bound
preservation lemmas finish the proof on arbitrary unbounded objects.

Updated the item's proof plan and dependencies to this shorter route. Public imports
are unchanged; only unused private proof imports are removed. No definitions or other
modules are changed. The first-localization-triangle step of `sk-prop-a1` is preserved.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.Etale.closed_unbounded_compactSupport_normalization`
(node `lem-pur-closed-unbounded-compact-support-normalization`). Added 0 holes;
0 split off; 0 textual sorry left in the delivered module.

Validation: the final module compiled cleanly through `lcompile.py` in 10.3 seconds
(exit code 0), with no warnings. `deliver3.py` runs the axiom probe and preflight.

## No longer needed

Removed private imports:

- `Sheaf.CategoryTheory.Sites.OrientedClosedBaseLocalization`.
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`.
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`.
- `Mathlib.CategoryTheory.Localization.Predicate`.
- `Mathlib.CategoryTheory.Sites.Sheafification`.
- `Mathlib.AlgebraicGeometry.Noetherian`.

The proof no longer directly needs these former dependency nodes:
`lem-trf-oriented-closed-base-localization`,
`lem-weil-pbc-exact-functor-derived-functor`,
`lem-weil-pbc-kinjective-total-derived`,
`lem-weil-pbc-localization-universal-property`,
`def-weil-pbc-sheafification`, `lem-weil-pbc-finite-type-over-noetherian`,
`lem-weil-pbc-exact-functor-complex-cohomology`,
`def-weil-abstract-derived-category`, and `def-weil-pbc-derived-categories`.
The last two remain statement dependencies where originally specified. Localization,
cohomology descent, K-injective derivation and identity-open normalization are reused
through their already proved source APIs. This does not assert that all these nodes
are globally unreachable. Removed the two obsolete tool approvals from this item's
`tool_uses`; no new approvals were added.

## Where the brief, the DAG or earlier work was wrong

The proposed proof was substantially longer than necessary. The existing public
`WeilConjectures.SixFunctors.Finite.Exact` import already supplies exactness for closed
immersions, the normalized unbounded comparison, natural cohomology, and both bounds.
The existing compact-support definition does not require a separate Noetherian
construction for the identity-open compactification. No mathematical statement changed.
The old docstring retains its original proof plan; the updated DAG and this report
record the implemented shorter proof.

Searches actually run: LeanFinder on exact unbounded derived comparisons and bounds,
Loogle on `mapDerivedCategory`, and msearch grep on the cohomology/bound lemma names.
Local source search found the exact finite-pushforward instance and normalized
comparison in the existing imports; no new statement was necessary.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
