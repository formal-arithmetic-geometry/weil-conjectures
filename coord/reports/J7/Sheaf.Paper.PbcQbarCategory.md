## What changed

Filled the seven existing proof holes of `Sheaf.Paper.PbcQbarCategory`.
The generic scalar action is proved by enlarging to common finite fields and
using the existing transport cocycle, quotient equality criterion, normalized
preadditive structure, and finite-stage linearity. Three proved private helpers
express semilinearity of transport, the scalar-action formula at the same stage,
and semilinearity of an additive tensor map specified on pure tensors.

The finite-stage field equivalence is the existing `pbcRationalCoefficientEquiv`
composed with `Shrink.algEquiv`; localization extensionality proves uniqueness.
The concrete scalar-extension functor is identified with the existing
`pbcRationalScalarExtension` by its unique integral factorization. Its prescribed
pure-tensor formula proves semilinearity for the actual field inclusion. Equal
fields use the literal identity functor.

Private imports of all declarations of `Sheaf.Paper.PbcScalarExtension` and
`Sheaf.Paper.FiniteStagePairCategory` expose the already proved normalization
helpers. Existing public declarations, signatures, definitions, instances,
attributes and public imports are unchanged. The existing fraction equivalence is locally irreducible, and
proof elaboration uses unrestricted definitional matching; these settings do not
change the exported constructions. The owning DAG node now records the argument.
No other module is adapted and no new statement or node is introduced.

Searches through msearch used LeanFinder, Loogle and grep. LeanFinder and Loogle
identified `IntermediateField.adjoin.finiteDimensional`; the already proved
`FiniteCoefficientFields` module also uses exactly this fact. Reading the actual
finite-stage and rational scalar-extension APIs supplied the shorter route
through the existing normalized coefficient equivalence and tensor formula.

## Proved and sorry left

Seven existing holes closed, zero holes added, zero split off:

- `CategoryTheory.StageSystem.qbarScalarField_finite`.
- `CategoryTheory.StageSystem.qbarScalarField_mem`.
- `CategoryTheory.StageSystem.qbarScalarRep_rel`.
- `CategoryTheory.StageSystem.qbarScalarHom_mkHom`.
- `CategoryTheory.StageSystem.qbarScalarHom_laws`.
- `AlgebraicGeometry.Scheme.qbarStageFieldEquiv_exists`.
- `AlgebraicGeometry.Scheme.pbcQbarScalarCompatible`.

No `sorry` remains in the delivered module. The existing source-library and Sheaf
lemmas are used with their existing proofs; no new intermediate assumption is added.
The finite-stage equality case is covered explicitly, including scalar zero and
unit. Nothing assumes nonzero morphisms or nonempty objects of a stage category.

## No longer needed

Removed redundant private imports of
`Sheaf.NumberTheory.Padics.IntegersLocalizationUniformizer`,
`Mathlib.LinearAlgebra.TensorProduct.Basic`, and
`Mathlib.RingTheory.Localization.Away.Basic`. Their APIs are already public through
the existing required imports. No public import, module or node is withdrawn.
No former proof dependency is pruned: the owning node previously had no proof steps
or proof dependencies. The finite-stage, common-stage, cone and Verdier structures
are retained, so the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The rework row records an older quarantine caused by an import of
`Sheaf.AlgebraicGeometry.ProjectiveLineGenusZero`. The item source is now present
under `lean/` and has no such import. Work starts from that current source,
preserving its category and all seven named theorem signatures; the quarantined
archive is neither withdrawn nor modified.

The owning node was a definition-only record with no proof steps, despite the
current module's seven named construction-property theorems. Its proof record is
now filled to match those proofs. No mathematical statement or target changes.
The current blueprint snapshot has reorganized the proper-base-change unit and
does not contain the old individual `def-weil-pbc-qbar-category.md` path; the
recorded node statement and the current Lean construction are preserved.

## Second reading by J7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
