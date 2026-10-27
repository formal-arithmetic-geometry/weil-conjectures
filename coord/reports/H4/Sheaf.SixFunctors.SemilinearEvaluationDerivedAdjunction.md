## What changed

Filled `AlgebraicGeometry.ProEtale.SemilinearProperOpen.semilinearEvaluationDerivedAdjunction`
without changing its statement, public imports, or seven comparison definitions. The new
helpers are private and proved. Updated only `proof`, `proof_deps`, and `proof_origin` of
`lem-sf-semilinear-evaluation-derived-adjunction` to follow the actual argument.
Change record: `coord/changes/H4-semilinear-evaluation-proof-context.md` documents the
local proof-context attributes conservatively flagged by preflight; no downstream
Lean module or public interface is changed.

Naturality of a transformation between constant towers identifies each component with
component zero. This factors the specified ordinary pullback square through the diagonal;
exact square composition localizes that equality. Mathlib mate pasting then gives both
requested factorization equations. Existing `evalR_isIso` and `evalJInv_isIso` supply the
invertibility clauses, and the existing `ConstantNormalization.chi_mate` calculation fixes
the specified direct-image comparison. For the final open equation, the proof compares
the units of the specified derived open adjunctions with exact localized ordinary units,
then uses exact localization of inverse mates and the ordinary constant-diagram triangle
identity. These comparisons are established before evaluating derived morphisms.

The blueprint unit route is preserved. The source is the evaluation/adjunction sentence
of `literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-compatibility/`
`fix-prop-coherence.proof.md`, with Stacks 07A7 and 03DI as recorded by the item.

Edge cases: the proof uses the unique index map to zero, which also exists for n = 0;
it does not invert a coefficient map or use a nonempty scheme/open. The argument therefore
retains zero coefficient rings, empty opens, arbitrary transition maps, and unbounded
complexes. The full module compiles cleanly through `lcompile.py` (42.8 seconds). Final delivery
checks are run by `deliver3.py`.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.SemilinearProperOpen.semilinearEvaluationDerivedAdjunction`
(node `lem-sf-semilinear-evaluation-derived-adjunction`). No holes added, no split-off
statements, and no `sorry` remains in the delivery. Imported declarations retain their
existing dependency status; no claim is made that all their transitive holes are closed.

## No longer needed

Removed these unused proof-only imports:

- `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`.
- `Sheaf.Paper.SemilinearDerivedSections`.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`.
- `Sheaf.CategoryTheory.RingedConstantTowerPushforwardNormalization`.
- `Mathlib.CategoryTheory.Abelian.FunctorCategory` (instances already available).

The following original proof dependencies are not needed directly by this proof:

- `def-coef-semilinear-system-models`: the existing operation interfaces suffice;
  its public import remains for the existing statement and definitions.
- `def-weil-extension-by-zero-presheaf` and
  `lem-pur-site-restriction-module-adjunction-exact`: reuse the already specified
  ordinary open adjunction and constant-diagram triangle identity.
- `lem-coef-semilinear-derived-sections` and
  `lem-weil-pbc-constant-tower-pushforward-normalization`: reuse `evalR_isIso`,
  `evalJInv_isIso`, and the already proved calculation of the canonical chi.
- `lem-sf-semilinear-evaluation-ordinary-adjunction`: constancy follows directly
  from naturality of the already specified ordinary comparison.
- `lem-weil-tower-category-levelwise-abelian`: the existing operation interfaces
  and available functor-category instances supply the necessary structures.

Retained exact square composition, exact localization of inverse mates, Mathlib mate
pasting, and canonical constant-tower normalization. No module is withdrawn; dependencies
of other existing declarations, including adopted source declarations, are preserved.

## Where the brief, the DAG or earlier work was wrong

Several planned arguments are already proved in the canonical operation modules.
Proof-only `import all` permits reuse of their complete private calculation lemmas;
no declaration in those modules is changed. The specified open adjunction is obtained
by a right-derived adjunction followed by exact-right-adjoint transport. Its equality
with the directly localized ordinary adjunction requires comparing the units: uniqueness
of adjoints alone would not give the normalized equality requested here.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
