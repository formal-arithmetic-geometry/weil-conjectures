## What changed

Proved `AlgebraicGeometry.Scheme.completedKoszulTensorQuotientAugmentation_exists`
with its original signature and docstring unchanged. The construction is the actual total tensor
of the finite coefficient augmentation, followed by the canonical tensor-with-single isomorphism.
Naturality in both variables assembles the strict tower transformation. A private general tower
assembly lemma keeps the categorical construction abstract during kernel checking.

Added one new proved coefficient module, `CompletedKoszulQuotientProjection`, which
constructs a normalized degree-zero residue projection that kills the incoming differential. The
degree-zero unit isomorphism is supplied by P5 landed module `Sheaf.Paper.CompletedKoszulUnitZeroIso`
and node `lem-weil-pbc-completed-koszul-unit-zero-iso`; the duplicate P6 module and node were
removed as required by the merge repair. Constant-module sheafification followed by the normalized
scalar-extension adjunction supplies the latter projection. The main module imports these only
for its proof. Its original public import is unchanged. No existing definition, instance, public
signature, attribute or shared module was changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.completedKoszulTensorQuotientAugmentation_exists`.

Also proved, without holes:
`AlgebraicGeometry.Scheme.completedKoszulQuotientProjection_exists`; the referenced
`AlgebraicGeometry.Scheme.completedKoszulUnitZero_isIso` is P5 landed theorem.
All private helpers have complete proofs. No holes were added, and no `sorry` remains in any
Lean module of this delivery. This is a proof, not a decomposition into new obligations.

Validation: the sandbox compiled cleanly in dependency order through `lcompile.py --all`: the
projection took 17.9 s, the unit isomorphism 13.8 s, and the item 41.2 s. All are below 60 s.
The original theorem signature was compared byte for byte, new node signatures were checked
against their Lean declarations, and the overlaid dependency graph was checked for missing
references and cycles.

The coefficient arguments include rank zero, the zero ring, the unit ideal and n = 0. The final
construction accepts arbitrary input cochain complexes, using the existing actual total tensor;
no additional boundedness or flatness hypothesis is introduced.

## No longer needed

Removed these original proof dependencies of the item's node:

- `lem-weil-pbc-noetherian-koszul-augmentation-pro-zero`
  (`Sheaf.Paper.NoetherianKoszulAugmentationProZero`): pro-zero homology is unnecessary for
  constructing a chain-level augmentation.
- `lem-weil-pbc-completed-constant-sheaf-reduction`
  (`Sheaf.Paper.CompletedConstantSheafReduction`): a completed/constant comparison is unnecessary
  because the residue projection is constructed in the actual completed scalar-extension model.

Neither module was imported by the original item, and neither is added. The retained
`lem-weil-pbc-completed-koszul-unit-zero-iso` and `def-weil-pbc-koszul-reconstruction-models` supplies the quotient units and their successor law.
No existing module or declaration is withdrawn. These are unused dependencies of this proof;
other consumers can still need them. An exploratory extra private-access import of
`CompletedAdicKoszulConstruction` was replaced in the new projection module by the precise
`CompletedIntegralCoefficients` import for its canonical sheafification instances.

## Where the brief, the DAG or earlier work was wrong

The existing proof plan cited pro-zero and completed/constant comparison results for a finite
strict augmentation. They are stronger than this construction needs. The degree-one Koszul
boundary formula and the residue normalization suffice. Once the degree-zero unit is invertible,
normalization uniquely determines the coefficient projection, so successor compatibility follows
by cancellation rather than a separate large compatibility obligation.

The proof reuses already proved general tools, including the rank-one constant-unit helpers in
`ScalarPerfectFiniteFree`, the scalar-extension unit comparison in
`ScalarExtensionConstraintCoherence`, the normalized ordinary adjunction in
`CompletedAdicCoefficientDatum`, and the generic Koszul boundary formula in
`WeilConjectures.RingTheory.KoszulProjectiveResolution`. These are generic algebra/sheafification
tools; no theorem requiring regularity of the chosen sequence is applied. The adopted source tree
is untouched. The proper-base-change unit route and its realized nodes are preserved.

Profiling the initial inline tower construction identified expensive kernel checking. Factoring
its assembly into a private categorical theorem avoids repeatedly checking the expanded concrete
Koszul tower. No timing limit or transparency setting was relaxed.

## New nodes

`new-p6-completed-koszul-quotient-projection` records the normalized degree-zero residue map
and its zero boundary composite, with its proved module
`Sheaf.Paper.CompletedKoszulQuotientProjection`. It contains no tensor, tower transformation or
naturality obligation. Both new nodes carry the three logged Mathlib searches, source proofs,
precise Lean signatures and the original proper-base-change unit. No change record is needed
because no existing definition or statement was changed.

## Second reading by P6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
