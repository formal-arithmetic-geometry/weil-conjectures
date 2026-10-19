## What changed

Proved `AlgebraicGeometry.Etale.isIso_projectionMap_finiteConstant_of_preservesCountableCoproducts`
in `Sheaf.AlgebraicGeometry.ExceptionalConstantTensor`, with its original signature and
visibility unchanged. No existing definition or statement was changed and no other module
was adapted.

The proof constructs the free resolution explicitly, with finite syzygies, and proves its
augmentation is a quasi-isomorphism. It reuses the source library's bounded-complex induction
and gives the countable-only version of its module telescope argument. Precomposing the
canonical projection transformation with the exact derived constant-sheaf functor permits
this argument in modules. The existing projection unit and shift theorems supply the
structural properties. Derived adjunctions give the required countable coproduct preservation.

Updated the node's proof, proof dependencies and proof origin to this route, and removed its
five obsolete top-level tool-use approvals. The unit statement and steps are preserved;
`dag/units/sk-prop-a1-kummer.json` has no realized statement or step assigned to the item.
All original public imports remain unchanged. Added imports are proof-only imports.

Validation: the module compiled with zero errors or warnings through `lcompile.py`, including
after removing the unused plan imports. Rechecked the retained proof on 2026-10-19:
`lcompile.py` compiled it in 10.4 seconds, with zero holes, and its public theorem signature
and public import list match the current shared source exactly. The resolution construction
also covers the zero
ring and zero module: the basis cover remains surjective and its kernel is finite; nothing
uses a positive rank, a nonzero coefficient, or finite projective dimension.

The resumed compile on 2026-10-19 again passed in 13.0 seconds with zero warnings.
The resumed dry run requested a change record for the added local `open`, `variable`,
`universe` and scoped `omit` commands. Added
`coord/changes/B7-exceptional-constant-tensor-private-proof-commands.md`, recording the
unchanged signature, command scope, and all 400 transitive importers. No Lean edits
were required.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.Etale.isIso_projectionMap_finiteConstant_of_preservesCountableCoproducts`
(node `lem-exc-constant-tensor`).

Holes added: zero. Holes remaining in the delivered Lean module: zero. No split-offs, new
axioms, or holed definitions. Every private helper, including the resolution's exactness
and quasi-isomorphism proofs, is complete.

## No longer needed

Removed these direct proof imports:

- `Sheaf.AlgebraicGeometry.PullbackConstantModule`;
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`;
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact` (added to the
  shared source since the retained attempt, and also unnecessary for this proof);
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`;
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`;
- `Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`;
- `Mathlib.CategoryTheory.Sites.Sheafification`;
- `Sheaf.Paper.ProjectionMateExact`;
- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact` (available through the used source
  library generation module; its distinguished-triangle theorem is still used);
- `Sheaf.Algebra.Homology.ComplexColimitHomotopyColimit`;
- `Sheaf.AlgebraicGeometry.EtaleDerivedTensorDirectSums`.

The separate generic ringed-topos mate theorem
`lem-weil-pbc-ringed-projection-mate-exact` is unnecessary: the existing ordinary-etale
projection map has proved unit and shift APIs. The sheaf telescope
`lem-kun-complex-colimit-hocolim` is unnecessary: the proved module telescope theorem applies
before the derived constant-sheaf functor. The generic tensor-coproduct theorem
`lem-kun-derived-tensor-direct-sums` is unnecessary: the existing tensor-Hom adjunction
proves the preservation directly.

The nodes `lem-kun-pullback-constant`,
`prop-weil-pbc-inverse-image-modules-exact`, `def-weil-pbc-sheafification`, and
`lem-weil-pbc-site-r-module-presheaf-sheafification-exact` are not separate proof dependencies
of this argument. The stated conclusion is already the canonical projection component at
N_T[0]; it requires no extra comparison to N_U or sheafification calculation. The exact
constant-sheaf functor and its degree-zero comparison are existing source-library APIs.
This removes the corresponding five top-level `tool_uses` entries (the mate, tensor sums,
sheaf telescope, constant pullback, and inverse-image exactness). It does not assert that
these nodes are unused by other parents or globally pruned.

Also removed a duplicate private import of
`WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`; its original public
import remains.

## Where the brief, the DAG or earlier work was wrong

The mathematical plan was sound. Its separately stated sheaf-level structural dependencies
are more general than this item needs. The existing ModuleCatGeneration theorem for all
modules assumes arbitrary coproduct preservation, so it cannot be applied directly under
the item's countable-only hypothesis. The proof instead constructs the finite-free
resolution and specializes just its bounded-complex and telescope arguments, preserving
exactly the original hypothesis. No mathematical statement repair is needed. Preflight nevertheless requires a change record
for the additional proof-scope commands; see
`coord/changes/B7-exceptional-constant-tensor-private-proof-commands.md`.

## Second reading by B7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
