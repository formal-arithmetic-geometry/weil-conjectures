## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.continuousScalarDerivedEncoding` in
`Sheaf.Paper.ContinuousScalarDerivedEncoding`, retaining its complete statement and
`ContinuousScalarDerivedEncodingData` unchanged. All auxiliary declarations are private
and proved in the same module.

The fixed ordinary adjunction and unit formula are reused from the proved private
helpers `Scheme.ordinaryAdjunction_exists` and `Scheme.reductionUnit_apply` in
`AdicCoefficientDatum`. The ordinary restriction comparison is constructed as the identity on sections.
Its linearity follows separately from the actual coefficient charts and the spectral
coefficient equality; this avoids retaining a large composed natural isomorphism. Its inverse mate
gives the ordinary extension comparison and its unit equation. The existing
`integralScalarExtension_exact` supplies exactness; equivalences transfer it to the
sectionwise functor. Universal left-derived uniqueness gives both specified comparisons,
with the original counits. The existing derived square API proves the all-complex
normalization. Direct localization constructs the sectionwise derived adjunction;
the proved cochain unit identity of `DerivedAdjointCochainCounit` verifies the fixed
internal adjunction. The shift is transported along the specified comparison.

Updated the item's DAG proof, proof dependencies and proof origin to this route, and
removed obsolete tool-use entries without adding or reordering approvals. Original
public imports are retained. Added proof imports for integral exactness, adjunction
mates/opposites and the derived square API. Proof-only `import all` opens the existing
proved ordinary adjunction/unit formula in `AdicCoefficientDatum` and the existing
proved cochain unit identity in `DerivedAdjointCochainCounit`. Explicit category
parameters prevent expensive instance searches in the derived adjunction. The generic assembly carries the two ordinary section predicates directly, avoiding
concrete projection rewrites. Generic private helpers isolate the quotient comparison and actual derived cochain unit before
specializing to the concrete coefficient categories. The main proof binds the existing
internal module category instances locally, avoiding repeated synthesis.

Return repair for 8670c41a6fd: current sheaf-dag moved the coefficient declarations
into `ContinuousIntegralCoefficientData` in 5e33c6e5290. Removed the obsolete sandbox copy of
`ContinuousIntegralCoefficients` from the packet, preserving its current reexport wrapper
and all relocated declarations. This is not a module withdrawal. The full theorem proof
is retained.

Validation: the current two-module packet is checked through `lcompile.py --all`;
`deliver3.py` supplies the final compilation, dry-run checks and preflight before pushing. The theorem and structure signatures
are unchanged. Every Lean line has at most 100 characters.

Reviewer correction (2026-10-25): the delivered `def` → `abbrev` change of
`integralScalarExtension` in the unclaimed `Sheaf.Paper.ContinuousIntegralCoefficientData`
was unnecessary. The proof compiles in 18.4 s against the unchanged `def`, so that module is
delivered identical to sheaf-dag. The change record
`coord/changes/V8-continuous-integral-scalar-alias.md` records the withdrawal; no declaration
other modules see changes.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.ProEtale.CondensedRing.continuousScalarDerivedEncoding`
(node `lem-weil-pbc-continuous-scalar-derived-encoding`).

Original item holes: 1. Holes closed: 1. Holes added: 0. Sorries left in the delivery: none.
No decomposition and no new assumptions. Existing dependency theorems are used with
their published statements.

## No longer needed

Removed these proof imports:

- `Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction`: its already proved
  application to the fixed `reductionChange` functor and the unit formula are reused
  from `AdicCoefficientDatum`, avoiding a repeated construction.
- `Sheaf.CategoryTheory.InternalSectionScalarAdjunction`: restriction is constructed
  explicitly from the specified charts; its inverse mate gives extension.
- `Sheaf.CategoryTheory.ScalarLocalizationSheafExact`: the already proved internal
  integral exactness theorem applies directly, then exactness transfers through encoding.
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`: the generic localization and
  universal left-derived uniqueness API suffices without its bounded-below package.
- `Sheaf.CategoryTheory.ExactDerivedComposition`: use the existing source-library
  normalized derived composition and natural-isomorphism API.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`: no separate resolution
  argument is needed for the sectionwise adjunction or the existing cochain unit identity.
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`: the sectionwise
  adjunction is localized directly from the exact ordinary adjunction.
- `Sheaf.CategoryTheory.SheafTensorStructure`: no separate packaged tensor structure
  is used; the statement's existing module categories supply their structures.
- `Sheaf.SixFunctors.OpenTensorNormalizationData`: use the generic localization formula
  directly rather than this specialized exact-adjunction wrapper.

Removed obsolete `tool_uses` entries `lem-sfb-internal-section-scalar-adjunction`,
`lem-pur-sheaf-ring-derived-coefficient-adjunction`, `lem-pc-kflat-resolution`, and
`def-weil-exact-derived-adjunction`, retaining the other approvals in their original order.

Accordingly removed from this node's proof dependencies:
`def-weil-exact-derived-adjunction`, `det-def-sfb-sheaf-tensor-structure`,
`lem-pc-kflat-resolution`, `lem-pur-sheaf-ring-derived-coefficient-adjunction`,
`lem-sfb-internal-section-scalar-adjunction`,
`lem-weil-pbc-continuous-coefficients-immersion-restriction`,
`lem-weil-pbc-exact-functor-derived-functor`, and
`lem-weil-pbc-scalar-localization-sheaf-exact`.

The completion/immersion-restriction statement is background interpretation of the
coefficient data; the concrete Lean scalar square follows directly from coefficient
chart naturality and the spectral coefficient equality. Its original public import is
retained. These are dependencies not used directly by this proof, not claims that no
other target consumer needs them. No library module or declaration is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement defect or unit-route error was found. The seven-step plan's separate
K-flat resolution argument is unnecessary after exactness: direct localization already
normalizes the sectionwise derived adjunction on every complex. The actual internal
adjunction has a proved cochain unit identity in the existing library.

Edge cases impose no extra condition: the construction does not assume a nonempty
site object, faithfulness of scalar extension, a torsion-free module, boundedness,
constructibility or completeness of a complex. All section formulas use sheafified
tensor sections. No target signature, source-library declaration, or coefficient construction changed.

## Forced adaptations

None. The proposed transparency change of `integralScalarExtension` was withdrawn by the
reviewer (see What changed).

## Second reading by V8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
