## What changed

Proved `AlgebraicGeometry.Scheme.constantDerivedLimitResolutionUnit` with its complete
original signature. Constructed z from the ordinary constant/limit adjunction on
complexes and the given natural transformation. Its projection equations and uniqueness
follow from the limit universal property. The existing derived-adjunction unit formula
and naturality of completedRlimUnit give the required resolution comparison. The final
clause is naturality of the specified derived adjunction unit.

Updated the existing node's proof, proof_deps and proof_origin to match this argument.
Removed redundant public imports and added a private proof import of the derived
adjunction API. Change record: coord/changes/Z7-constant-derived-limit-resolution-imports.md.
No other Lean module, declaration signature or definition was changed.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Scheme.constantDerivedLimitResolutionUnit`
(node lem-cbc-constant-derived-limit-resolution-unit). No holes added or split off.
The delivered module contains zero sorry occurrences; no new theorem or definition was
introduced. This is a proof, not a decomposition.

## No longer needed

Removed direct public imports:
- Sheaf.Paper.PbcQbarCompletedPullback
- Sheaf.CategoryTheory.RingedSiteModules
- Mathlib.Algebra.Homology.HomotopyCategory.KInjective
- Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
- Mathlib.Algebra.Homology.DerivedCategory.Basic
- Mathlib.CategoryTheory.Functor.OfSequence
- Mathlib.CategoryTheory.Abelian.FunctorCategory

Removed redundant private imports:
- Mathlib.CategoryTheory.Localization.Predicate
- Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

The retained CompletedPullback import supplies the statement's definitions and the
existing limit, abelian and derived-category APIs transitively. The explicit private
RightDerivedFunctor.Adjunction import supplies the proof's adjunction formula.

Removed proof dependencies def-weil-inverse-system (no sequence constructor is used)
and lem-weil-pbc-localization-universal-property (the existing derived adjunction has
already performed descent, so no second lift is needed). Both remain unchanged wherever
else needed; def-weil-inverse-system also remains a statement dependency. No module is
withdrawn, no DAG node is deleted, and the unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The original Steps 4-5 construct a fresh localization descent and use invertibility
on K-injective values. The already defined constantRlimAdjunction gives eta directly;
its standard derived unit formula followed by naturality gives exactly the comparison
required here. Consequently the supplied hι and hJ are unnecessary for this equation,
but both original hypotheses are retained verbatim. No false statement or tool defect
was found in the mathematics. Remote compilation initially returned busy/no-answer
responses; these are not Lean failures.

The complete proof compiled remotely in 20.8 seconds and again in 20.4 seconds.
The latter run had only unused-binder warnings for the two retained hypotheses;
the final source references these hypotheses explicitly to preserve their exact names.
The final source then compiled cleanly in 21.0 seconds, with no errors or warnings.
The proof is valid for every natural transformation iota, so in particular for the
specified resolution. The zero complex, acyclic inputs, and identity morphisms impose
no extra assumptions: the equations are universal adjunction and naturality equations.
The first delivery attempt returned capacity exit 75 (24 occupied delivery slots);
the retry uses the same required delivery tool.

## Second reading by Z7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
