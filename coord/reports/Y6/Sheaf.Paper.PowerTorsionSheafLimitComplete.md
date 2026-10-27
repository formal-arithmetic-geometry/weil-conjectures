## What changed

Decomposed the one remaining hole in
`WeilConjectures.PowerTorsionLimit.power_torsion_sheaf_limit_complete` into three
proper steps and wrote the complete Lean assembly between them. The assigned
statement, including every existential witness and projection equation, is
byte-identical to the library statement.

The assembly chooses the canonical natural unit, uses the separately supplied
exponent at each Q_n, applies the existing proved
`integralOperationsRoosQuasiIsoInvariant`, and uses the strict signed-exchange
identity to prove that the actual unit on Roos Q is a quasi-isomorphism. Both
isomorphisms in that composite are genuine strict isomorphisms. It then applies
the quotient comparison to that arbitrary complex. No uniform nilpotence bound,
boundedness, constructibility, qcqs, or invertibility-on-T assumption is added.

Moved the existing constructions, unchanged in their data, into
`Sheaf.Paper.PowerTorsionSheafLimitModels`, publicly re-exported by the assigned
module. This allows the independent step modules to refer to the same functors,
unit and coordinates without an import cycle. The tensorTower functor-law proofs
are simplified to avoid expensive extensionality into sheaf-module maps. The
original public imports and all existing declaration names and signatures remain
available. The move is recorded in
`coord/changes/power-torsion-limit-model-extraction.md`.

The generic stated dependencies were read first. Their right-tensor presentation,
rearranged Roos functor, and homotopy-localization quotient bridge do not directly
match this item's left-tensor, integralOperationsRoos and none-slice conventions.
The new steps isolate exactly those model identifications and their normalizations;
they retain the original mathematical route. No source-library module is changed.

## Proved and sorry left

Original holes: one. Closed in the assigned module:
`WeilConjectures.PowerTorsionLimit.power_torsion_sheaf_limit_complete`, by a complete
assembly from the following three proper steps. This is a decomposition, not an
unconditional proof of the original mathematical theorem. Holes added: three;
net holes closed minus added: -2.

Every remaining delivery hole is a public named theorem with a source and a full
proof in words, in its own new module:

- `WeilConjectures.PowerTorsionLimit.left_koszul_nilpotent_unit`
  (`lem-sp-left-koszul-nilpotent-unit`): the single-complex nilpotent calculation
  and naturality; no outer tower, exchange or completeness conclusion.
- `WeilConjectures.PowerTorsionLimit.left_koszul_roos_exchange`
  (`lem-sp-left-koszul-roos-exchange`): signed interchange and finite Koszul tensor
  exchange; no torsion hypothesis or completeness conclusion.
- `WeilConjectures.PowerTorsionLimit.left_koszul_quotient_completeness`
  (`lem-sp-left-koszul-quotient-completeness`): quotient comparisons, triangle and
  completeness conditional on the actual Koszul unit being quasi-isomorphic;
  no outer tower or termwise nilpotence hypothesis.

There are no holes in definitions, no private holes, and no hole in the assigned
module or extracted models. The previously proved `unit_condition` is preserved.

Edge cases checked mathematically: zero complexes give the zero augmentations;
exponent one is allowed; the exponents may grow arbitrarily with n; every complex
may be unbounded; the exchange lemma uses only the two finite Koszul degrees and
does not claim arbitrary tensors commute with products; the quotient lemma uses
one K-flat flat-term resolution for all levels. The zero and empty scheme cases
do not require a nonzero coefficient section on an empty site.

## No longer needed

The assigned module no longer directly imports
`Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`,
`Sheaf.CategoryTheory.StrictRoosComparison`,
`Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`,
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`,
`Sheaf.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients`,
`WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone`,
`WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`, or
`Mathlib.Algebra.Homology.DerivedCategory.ShortExact`. Their mathematical content,
where needed, remains below the three steps or the proved Roos-invariance helper.
None of these modules or nodes is withdrawn or claimed globally unused.

The parent's direct proof dependencies are now the three new steps and
`lem-pur-integral-operations-well-defined`; its previous generic dependencies
remain transitively needed in the substeps. Its old direct tool_uses approvals
are removed because that assembly does not apply them directly:
`lem-weil-proetale-countable-products-exact`, `lem-weil-strict-roos-comparison`,
`lem-weil-tower-category-levelwise-abelian`, `lem-weil-pbc-complex-ses-triangle`,
`lem-weil-pbc-ringed-strict-tower-homotopy-limit`, `lem-pc-kflat-resolution`,
`lem-pur-kflat-tensor-quasiiso-independent`, `lem-pur-quasi-iso-cone-acyclic`,
`lem-pc-tensor-mapping-cone-iso`, `lem-pur-derived-change-of-rings`.

No mathematical dependency is pruned from the entire target route, and no file
is deleted. All unit-level statement and proof realizations remain.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The existing declared dependencies use distinct,
mathematically equivalent strict models. Applying them to this item's actual
unit requires the indicated signed symmetry, Roos-map identification and
localization/none-slice normalization; these are the unfinished parts, explicitly
exposed in the new steps rather than hidden inside the main proof.

The original tensorTower law proofs used deep extensionality, contributing to
slow elaboration. Only these proof fields are changed; object and map data stay
identical. The model extraction is required by the dependency graph of the
new independent modules, not an attempt to bypass the per-file compile limit.

## New nodes

`def-sp-power-torsion-limit-models` attaches the extracted, already constructed
strict functors, unit and coordinates. It introduces no new mathematics.

`lem-sp-left-koszul-nilpotent-unit` specializes the generic nilpotent-action
calculation after identifying the right and left tensor models and the specified
zero-homotopy unit.

`lem-sp-left-koszul-roos-exchange` isolates steps 4--6 in precisely the original
coordinate conventions, with no nilpotence requirement.

`lem-sp-left-koszul-quotient-completeness` isolates steps 7--9 for an arbitrary
complex whose Koszul unit is quasi-isomorphic, including the actual finite
quotients and the unrestricted integral convention.

Compilation of all five modules passed (exit 0); model 38.7 s, quotient step 7.2 s,
exchange step 14.9 s, nilpotent step 5.7 s, main assembly 21.1 s. Unused
proof-only generic imports in the new statement modules were then removed;
their DAG proof plans continue to cite those generic lemmas. No proof-only
import is needed to elaborate a `sorry` statement.

All nodes are in sec-smooth-purity/sk-lem-sp-tower, have exact Lean attachments,
sources, proof steps and actual logged Mathlib searches. The whole imported
blueprint was searched for Koszul and power-torsion comparisons; no existing
blueprint node states these model-specific interfaces. The named generic nodes
are retained as dependencies. Change record:
`coord/changes/power-torsion-limit-model-extraction.md`.

## Second reading by Y6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
