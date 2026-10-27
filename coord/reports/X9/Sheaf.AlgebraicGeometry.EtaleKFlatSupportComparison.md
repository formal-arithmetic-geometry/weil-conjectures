## What changed

Reduced `AlgebraicGeometry.Etale.KFlatSupportComparison.etale_kflat_support_comparison`
to the strict natural support diagram and the coefficient normalization of its quotient.
The parent proof assembles these inputs, proves the normalized middle identity by
cancellation, constructs the two distinguished SES triangles and their connecting square,
and proves the first-map isomorphism consequence by the triangle two-isomorphism lemma.
The strict and scalar-normalization arguments are separated mathematically: the strict
result has no coefficient map, augmentation, derived tensor model or boundedness input;
the normalization result has no support-row exactness, kernel map or triangle assertion.

The equivalent compact interface uses the original actual support rows and maps,
packaged in `RowFamily`, `DiagramNatural` and `IsComparison`. The proved
`support_rightMap_iff` identifies the original summand characterization with equality
to the canonical quotient map. Component HEq is between definitionally equal endpoints.
Existing data definitions and all adopted-source modules are unchanged. The change
record is `coord/changes/etale-kflat-support-interface.md`; downstream scans found no
Lean consumers to adapt. The DAG parent remains mathematically valid.

## Proved and sorry left

The original module had one hole:
`AlgebraicGeometry.Etale.KFlatSupportComparison.etale_kflat_support_comparison`.
Its new assembly proof has no sorry. The characterization theorem
`AlgebraicGeometry.Etale.KFlatSupportComparison.support_rightMap_iff` is also proved,
using total-summand extensionality and the existing flat support diagram.

Two holes are added, each the complete body of a named public theorem in its own module:

- `AlgebraicGeometry.Etale.KFlatSupportComparison.support_comparison_strict`:
  actual-row/kernel-row transport, the strict natural comparison and localization of
  its middle map. Its docstring gives the complete kernel/exactness argument.
- `AlgebraicGeometry.Etale.KFlatSupportComparison.support_comparison_projection`:
  transport of the existing open projection model to the exact-pullback tensor and
  scalar coordinates. Its docstring specifies the normalization and cancellation.

Thus this is a decomposition: one upper hole closed, two lower holes added; net -1,
not a claim of a complete proof. There are no sorries in definitions or private helpers.
The existing open projection model remains an unproved DAG dependency, unchanged by
this packet; it is not imported merely to state the new normalization lemma.
Server compilation accepted the combined assembly and the characterization. Final
import-order packet compilation and delivery validation are recorded by the tools.

## No longer needed

Removed the former direct proof imports of
`Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated`,
`Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`,
`WeilConjectures.Algebra.Homology.FilteredColimitsTensor`,
`Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`,
`WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`,
`Sheaf.AlgebraicGeometry.EtaleDerivedChainTranspose`, and
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.
Their mathematical inputs remain needed inside the existing chain/projection lemmas;
none of those modules or upstream declarations is withdrawn. No global module pruning
is claimed. The original K-injective existence proof dependency is unnecessary here,
because the replacement and all its properties are supplied in the theorem hypotheses.
The SES triangle and two-isomorphism nodes remain used directly in the parent proof.

## Where the brief, the DAG or earlier work was wrong

The live DAG's chain diagram uses kernel rows, while the item uses the actual closed
support counit row. Passing between them requires a canonical kernel-row isomorphism;
their short exactness cannot simply be reused at the original type. The projection
model uses left-derived pullback, whereas the item uses exact derived pullback; their
canonical comparison isomorphisms must be transported, retaining map normalization.
Neither mathematical statement was found false. In particular no B-action on the
A-linear complexes or restriction-of-scalars preservation of injectives is asserted.

Many proof attempts passed tactic elaboration but their kernel checks unfolded the
competing pointwise and abelian-induced zero structures and the chosen derived
localization. The compact interface avoids that repeated expansion in the assembly.
The remaining attempts and successful generic helper proofs are preserved outside
`lean/` in the sandbox scratchpad, and are not part of the delivery.

## New nodes

`def-pur-etale-kflat-support-rows` records the explicit, sorry-free row-family interface.
Its row objects, row maps and characterization predicate are constructed directly.

`lem-pur-etale-kflat-support-characterization` records the proved equivalence between
the original total-summand quotient characterization and the canonical quotient map.
The proof compares every total-degree summand, including unbounded total coproducts.

`lem-pur-etale-kflat-support-strict` isolates the strict natural diagram, actual-row
exactness and K-injectivity after pullback, without scalar or boundedness data.
Edge cases empty open/closed strata and arbitrary unbounded flat Q are covered by the
same exactness and kernel argument.

`lem-pur-etale-kflat-support-projection` isolates coefficient normalization of the
canonical open map, without a support row, kernel comparison or distinguished triangle.
It retains all five bounds and the exact original tensor and replacement coordinates.

The equivalent statement repair is recorded in
`coord/changes/etale-kflat-support-interface.md`; no forced adaptations were needed.

## Second reading by X9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
