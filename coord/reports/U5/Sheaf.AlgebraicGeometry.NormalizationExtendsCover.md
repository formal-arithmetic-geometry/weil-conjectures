## What changed

Proved `AlgebraicGeometry.Scheme.normalizationIn_functionField_extends_cover` with its
signature and public imports unchanged. Four fully proved private helpers establish
invariance of relative normalization under source isomorphisms, comparison with an
integral factorization through a normal scheme, triviality of normalization for a
normal integral scheme, and the induced generic stalk map.

The main proof makes P Noetherian, uses the existing clopen normal-components theorem
and connectedness to obtain integrality and normality, constructs the algebra map from
the cover's generic stalk map, and identifies the normalization over V with P using the
relative-normalization universal property and smooth base change along V's open immersion.
The node's proof and proof dependencies now record this route. No definitions, public
signatures, visibility, or consumer interfaces changed. No new nodes or change records.
The unit's realized field does not attach this node to a prescribed step; its route stays.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.normalizationIn_functionField_extends_cover`
(node `lem-fin-normalization-extends-cover`). Added 0 holes; split off 0 statements.
No sorry remains in the delivered module or its private helpers.

The proof uses `AlgebraicGeometry.Etale.exists_clopen_normal_integral_components`
(node `lem-fin-etale-normal-components`, module
`Sheaf.AlgebraicGeometry.EtaleNormalComponents`), whose proof remains sorry in the
library. Closing the assigned hole does not close that dependency.

## No longer needed

Removed the following unused direct proof imports:

- `Mathlib.AlgebraicGeometry.Noetherian` (replaced by the proved source-library
  Noetherian API, `WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian`)
- `Mathlib.AlgebraicGeometry.FunctionField`
- `Mathlib.AlgebraicGeometry.Restrict`
- `WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField`
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`
- `Mathlib.AlgebraicGeometry.Scheme`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Mathlib.RingTheory.Unramified.LocalRing`
- `Mathlib.AlgebraicGeometry.Gluing`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated`

The retained public imports already expose the function-field, stalk, restriction and
normalization API. `EtaleNormalComponents` and `UniversallyOpen` remain as direct proof
imports. No public import changed.

The following old direct proof dependencies are unnecessary:

- `lem-weil-pbc-finite-proper`
- `def-weil-proper-morphism`
- `lem-sc-integral-function-field-affine-fraction`
- `lem-weil-pbc-open-preimage-fibre-product`
- `lem-weil-pbc-etale-scheme-base-change`
- `lem-weil-pbc-etale-algebra-residue-field-separable`
- `lem-weil-pbc-finite-algebra-is-integral`
- `lem-sc-integral-scheme-stalks-in-function-field`
- `lem-sc-function-field-sections-glue`
- `def-weil-affine-spectrum`
- `lem-weil-pbc-affine-source-morphism-separated`
- `lemma-nagata-ext-scheme-theoretically-dominant-separated`
- `lem-weil-pbc-scheme-morphism-gluing`

The finite morphism's finite-type instance replaces the properness detour. The
statement needs no separate finite-dimensional or separability instance. The already
proved normalization API handles integral-closure comparison and gluing; explicit
section-gluing and separated-target rigidity are unnecessary. The obsolete direct
`tool_uses` entry for `lem-sc-function-field-sections-glue` is removed. These facts can
remain transitively used by upstream normalization implementations; no global module
unreachability is claimed. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found and the statement is unchanged. The original DAG
spells out affine and gluing work already provided by Mathlib's relative-normalization
universal property and smooth base change. Its finite separable field extension step
proves more than the Lean statement requires. The current source proof was read at
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/lem-fin-normalization-extends-cover.proof.md`.

On resumption, the required dry run reached Lean and exposed a final cancellation
mismatch between `asIso`'s inverse and `inv`. The proof now changes explicitly to
`inv` before applying `IsIso.hom_inv_id_assoc` and `normalizationPullback_snd`.
The corrected module compiled successfully in 4.6 seconds with no diagnostics
(`compile-resumed-retry.log`). `deliver3.py --no-push` then reported OK: the delivery compiles and passes
server preflight. The review class is CODEX because the proof-route node changes.

## Second reading by U5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
