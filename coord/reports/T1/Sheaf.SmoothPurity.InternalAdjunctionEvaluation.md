## What changed

Proved `AlgebraicGeometry.Etale.internalAdjunctionEvaluation` with its original signature,
public imports, and docstring. The existing canonical isomorphism is definitionally the
conjugate of the projection map. Three proved private helpers express its transpose by
naturality and the counit, then expand the three composed adjunctions. The final proof
precomposes this identity with the existing canonical symmetry.

A local priority for `GrothendieckTopology.W.monoidal` replaces the priority previously
provided by the removed exceptional-adjoint import, preserving that preference locally
without changing the public interface. The static preflight requires a change record
for this local command: `coord/changes/T1-internal-adjunction-local-monoidal-priority.md`.
Its Users table covers all four downstream modules; none needs adaptation.

Updated `lem-asd-internal-adjunction-evaluation` to record this direct proof from the
existing adjunctions instead of rebuilding them using resolutions. The unit route is
unchanged: its record has no realized statement or step assigned to this node.

Validation: the final file compiled with `lcompile.py` in 43.8 seconds, within the
unchanged 60-second limit. Text checks confirm the exact original theorem signature
and public imports, zero `sorry` tokens, and all Lean lines at most 100 characters.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Etale.internalAdjunctionEvaluation`
(node `lem-asd-internal-adjunction-evaluation`).

The private helpers `transpose_conjugate`, `transpose_composite`, and
`tensor_conjugate_evaluation` are proved.
Zero holes remain in the delivered module. Zero holes added; zero statements split off.
Existing imported declarations retain their original proofs and axioms.

## No longer needed

Removed these proof-only imports:

- `Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`
- `Sheaf.AlgebraicGeometry.CompactifiableOverField`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`
- `Sheaf.AlgebraicGeometry.ProperProjectionFormula`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection`

Removed these direct proof dependencies from this node:

- `prop-weil-pbc-inverse-image-modules-exact`
- `prop-pur-kinjective-resolutions-exist`
- `lem-weil-pbc-kinjective-hom-derived`
- `lem-weil-pbc-kinjective-total-derived`
- `lem-weil-pbc-ringed-internal-hom-exact-restriction`
- `lem-pur-rhom-global-sections`
- `def-asd-compactifiable`
- `def-weil-proper-morphism`
- `def-weil-finite-type-morphism`
- `pqf-lem-locnoeth-lft`
- `lem-amb-proper-coproducts-projection`
- `def-amb-etale-compact-support`
- `lem-pur-etale-open-derived-tensor`
- `thm-amb-etale-exceptional-adjoint`

The ordinary adjunctions and canonical projection map already exist, and the
internal-adjunction definition fixes their conjugate. Thus this proof needs no new
K-injective resolutions, global-sections comparison, compactification construction,
Noetherianity argument, or separate proper/open projection comparison. The underlying
functors and their properties remain available through the canonical construction;
no source-library declaration or proof was removed. Statement dependencies remain
unchanged. No assertion is made that these nodes are globally unused by other parents.

Removed all five obsolete `tool_uses` entries, namely
`prop-pur-kinjective-resolutions-exist`, `lem-weil-pbc-kinjective-total-derived`,
`lem-weil-pbc-ringed-internal-hom-exact-restriction`, `lem-pur-rhom-global-sections`,
and `pqf-lem-locnoeth-lft`.

## Where the brief, the DAG or earlier work was wrong

The planned reconstruction of the adjunctions is unnecessary for the present Lean
interface: `derivedHomRightDerivedLowerShriekIsoOfFinite` already uses precisely
`ParametrizedAdjunction.conjugateIso` of the specified projection map. The proof follows
the displayed Hom-bijection chain and its evaluation/counit sentence in
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-cbc/prop-asd-internal-adjunction.proof.md`.

Rewriting and simplifying the specialized composed adjunction forced expensive reduction
of the derived functor definitions. Proving the elementary calculation for arbitrary
parametrized adjunctions and applying it as a term avoids this reduction without changing
any definition or time limit. All public imports remain verbatim.

Change record: `coord/changes/T1-internal-adjunction-local-monoidal-priority.md`.

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
