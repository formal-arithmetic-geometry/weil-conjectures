## What changed

Proved `AlgebraicGeometry.Scheme.Modules.finite_singleton_fibre_neighbourhoods_and_module_stalk`
in `Sheaf.AlgebraicGeometry.FiniteSingletonFibreLocalization`, with its original signature and
all original public imports unchanged. The proof constructs the target neighbourhood as the
complement of the closed image of the source complement. It then proves bijectivity of the
actual `TopCat.Presheaf.stalkPushforward` on germ representatives. Finally it proves scalar
compatibility on a common neighbourhood using the module and structure-sheaf germ identities.

This is the alternative direct proof explicitly given in the last sentence of the proof of
Stacks Tag 05B8, `lemma-finite-morphism-single-point-in-fibre`, in
`literature/stacks-project/more-morphisms.tex`. No affine localization argument is needed.
Updated the theorem's proof explanation and its existing DAG node to record this route.
The node's statement, statement dependencies, Lean attachment and unit are unchanged.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.Modules.finite_singleton_fibre_neighbourhoods_and_module_stalk`
(node `lem-trf-finite-singleton-fibre-localization`). Added 0 holes, split off 0 statements,
and left 0 holes in the delivered module. The proof uses no other project theorem with
an unfinished proof. The axiom check and final delivery compilation validate the result.

Edge cases: the given point rules out an empty source; no surjectivity away from its image
is required; the zero module is included. The direct argument works for arbitrary modules,
so the original quasi-coherence hypothesis can be unused while remaining in the signature.
In the injectivity argument the additional intersection with both original target opens
ensures all restricted sections have exactly the same domain.

## No longer needed

Removed these private proof imports:

- `Mathlib.Algebra.Module.LocalizedModule.Basic`
- `Mathlib.LinearAlgebra.TensorProduct.Defs`
- `WeilConjectures.AlgebraicGeometry.Morphisms.AffineModuleGermLocalization`
- `Mathlib.AlgebraicGeometry.AffineScheme`
- `WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChange`
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`
- `Mathlib.AlgebraicGeometry.Morphisms.Integral`
- `Sheaf.RingTheory.UniquePrimeLocalization`

The original file had eight private proof imports. The necessary finite-to-integral and
closedness instances remain available from the public finite-morphism import.

Removed these unused proof dependencies from the node:

- `def-weil-finite-integral-morphism`: already a statement dependency; no separate affine
  coordinate reduction in the proof.
- `def-weil-pbc-module-localization`
- `def-weil-pbc-module-tensor-product`
- `lem-sbc-affine-module-germ-localization`
- `lem-trf-unique-prime-localization`
- `lem-weil-pbc-affine-open-spec-points`
- `lem-weil-pbc-affine-open-stalk-localization`
- `lem-weil-pbc-affine-pushforward-base-change`
- `pqf-def-affine-morphism`

The localization and affine-coordinate dependencies are replaced by the definition of
stalks and the neighbourhood assertion proved in the same theorem. Removed the three
obsolete top-level tool approvals for affine pushforward, affine points, and affine stalk
localization. Their historical split report is preserved. These nodes and modules are no
longer needed by this proof; no claim is made that they are globally unused, and no module
or source-library declaration is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The old DAG and docstring planned an unnecessary algebraic detour through quasi-coherent
affine stalk localizations and unique primes. Stacks itself states the shorter topological
alternative. The unit's realized statement and steps are not bypassed or changed.

The only direct Lean importer is `Sheaf.TraceFormula.ElementaryDevissageFlatness`; its
future proof still needs this theorem and this delivery preserves its interface. The
read-only downstream check lists ten transitive importers and no external textual uses
of the theorem yet. There is no definition, statement, public import, or forced consumer
adaptation in this delivery, so no change record is required.

## Second reading by T7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
