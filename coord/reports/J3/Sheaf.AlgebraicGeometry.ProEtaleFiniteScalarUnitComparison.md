## What changed

Proved `AlgebraicGeometry.ProEtale.finiteScalarUnitComparison` without changing its
statement or any of its concrete definitions. The coefficient direct-image square is
proved by the sheafification adjunction and naturality. Its sectionwise identity gives
the direct-image scalar comparison. The existing finite-module adjunction supplies the
actual small-model unit normalization. The pullback comparison is the inverse of the
mate of the direct-image comparison; the unit equation and the underlying abelian
comparisons prove the mate invertible and give all required clauses.

Added `Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleUnderlying`, with the proved theorem
`AlgebraicGeometry.ProEtale.finiteCoefficientModuleUnderlying_exists`. Its private
helpers adapt the existing model-ring presentation construction from CommRingCat to
RingCat and transport its unit-preserving module/abelian comparison back through
AsSmall. No arbitrary module data or new definitions with postponed properties are
chosen. The existential comparison is unique once its unit equation is fixed.

Updated the existing node's proof route and added the supporting theorem's node.
Change record: `coord/changes/J3-finite-scalar-proof-imports.md`.

On resumption, replaced the final composition rewrite with an explicit calculation:
postcompose the mate unit equation, use functoriality, then cancel the inverse mate.
The item compiled without errors or warnings in 23.4 seconds. The supporting module
also compiled without errors or warnings in 21.4 seconds against the current library.
Both files contain zero holes; the delivery dry run checks them together.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.finiteScalarUnitComparison`
(node `lem-exc-proetale-finite-scalar-unit-comparison`).

Added 0 holes. The new
`AlgebraicGeometry.ProEtale.finiteCoefficientModuleUnderlying_exists`
(node `lem-exc-proetale-finite-module-underlying`) is proved. No `sorry` remains in either
file of this delivery. Existing imported obligations remain their owners' items,
including the finite-module adjunction and the generic module inverse-image comparison.

## No longer needed

Removed `public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport` from the
item: its commutative fixed-coefficient realization and derived comparisons are unused.
The proof uses the existing normalized arbitrary finite-ring adjunction directly.
Also removed the direct proof imports
`Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`,
`Sheaf.AlgebraicGeometry.ProEtaleInverseImage`, and
`Sheaf.CategoryTheory.RingedSiteModules`: their required definitions remain available
through `ProEtaleConstantExact`. These nodes are not pruned from the argument.
No whole existing module is withdrawn. The pullback's coefficient isomorphism and the
module inverse-image construction remain needed through ProEtaleConstantExact.

The direct-image coefficient square follows on the entire continuous-function
presheaf by pointwise composition and sheafification naturality. No new open-fibre
gluing lemma or separate coefficient inverse-image square is required. The pullback
comparison is obtained as a mate instead of separately transporting the two restricted
actions. All statement dependencies remain meaningful; the updated proof dependencies
record the declarations actually used. The unit route is retained.

## Where the brief, the DAG or earlier work was wrong

The existing dependencies do not directly state the unit-normalized underlying abelian
comparison for the specified noncommutative finite-ring pullback. The existing
ProEtaleModuleInverseImageUnderlying specialization takes CommRingCat. The general
ModuleInverseImageUnitComparison theorem already handles RingCat, so its specialization
is proved here by adapting the existing AsSmall ring presentation argument. No false
statement, changed target, or definition repair was needed.

The earlier consumer check is stale: the current tree has one direct importer,
`ProEtaleSupportedKernelComplex`, and 123 transitive downstream modules. The direct
importer already publicly imports `ProEtaleFiniteModuleAdjunction`, which publicly
imports the removed realization module. Thus it loses no available declaration;
no adaptation is needed. The change record now records this check.

Edge cases use no nonzero-ring or nonempty-site assumption: the constructions and
unit equations apply to the zero ring and empty scheme, and no commutativity or
flatness of the scalar homomorphism is used.

Delivery infrastructure failed repeatedly while preparing the temporary worktree:
`git checkout -q --detach origin/sheaf-dag` exceeded its 600-second timeout.
A later dry run compiled both files but rejected linter warnings, now repaired.
The resumed item compile passed without warnings. A subsequent dry run reached
compilation but the compile server returned no answer within 242 seconds. The current
required dry run is waiting for temporary-worktree capacity. No launcher scripts were
changed and no delivery push has yet succeeded.

## New nodes

`lem-exc-proetale-finite-module-underlying` records the proved comparison of the
specified finite-ring transported module pullback with abelian inverse image, including
its actual small-model unit equation. It is strictly the abelian-normalization part of
the original argument; it contains no scalar homomorphism, alpha, beta, or scalar-unit
compatibility conclusion. Its proof is complete, with zero split-off holes.

The private `scalarPullbackMate` is irreducible, with its unit equation proved
separately, to prevent sectionwise checks from expanding the entire mate construction.
The wall-clock compile limit is unchanged. The final theorem has a scoped
400000-heartbeat elaboration budget for its category-theoretic instance synthesis.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
