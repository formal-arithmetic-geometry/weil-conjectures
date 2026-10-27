## What changed

Reduced `WeilConjectures.IntegralPullbackStrictRoos.integralRoosDerivedPullbackUnit`
to four independent substeps: normalized chain data, resolving-class preservation and
counit invertibility, localized augmentation identities, and descent of those identities
to natural completion isomorphisms. The item proves the coefficient limit equality
and combines every conjunct from these steps. Its statement and public imports stay unchanged.

The general actual/quotient completion comparison is proved in a fifth new module by
reusing the existing private `actualCompletion_quotient` proof with a proof-only import.

A proved private logical assembly lemma keeps the nested existential eliminations abstract.
The chain witnesses are packaged in a generic product record. These changes avoid repeated
kernel reduction of the concrete functors while preserving all mathematical conditions.
All existing modules other than the item are unchanged; no definition repair is delivered.

## Proved and sorry left

Closed the original one hole in
`WeilConjectures.IntegralPullbackStrictRoos.integralRoosDerivedPullbackUnit` by decomposition.
The item has zero holes. Added four named holes:

- `WeilConjectures.IntegralPullbackStrictRoos.integralRoosChainRepresentatives`
  (`lem-sfb-integral-roos-chain-representatives`).
- `WeilConjectures.IntegralPullbackStrictRoos.integralRoosResolvingCounits`
  (`lem-sfb-integral-roos-resolving-counits`).
- `WeilConjectures.IntegralPullbackStrictRoos.integralRoosAugmentationLocalization`
  (`lem-sfb-integral-roos-augmentation-localization`).
- `WeilConjectures.IntegralPullbackStrictRoos.integralRoosCompletionIsomorphisms`
  (`lem-sfb-integral-roos-completion-isomorphisms`).

The auxiliary theorem
`WeilConjectures.IntegralPullbackStrictRoos.integralRoosCompletionReflectorComparison`
(`lem-sfb-integral-roos-completion-reflector-comparison`) is proved.
This is decomposition, not a net reduction in holes. Existing library holes are untouched.
No definition contains an added hole.

## No longer needed

Removed these original proof imports from the item:
`Sheaf.Paper.ConstantCompletionEquivalence`,
`Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`,
`Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit`,
`Sheaf.Paper.CartesianCoefficients`, `Sheaf.Paper.KFlatRingedToposPullback`,
`Sheaf.Algebra.Homology.KFlatScalarTowerRealization`,
`Sheaf.Algebra.Homology.DiagramKFlatReplacements`, and
`Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`.
The item imports the four substep interfaces it uses.

Replaced the original direct proof dependencies by those interfaces and the
coefficient-datum and completed-pullback definitions. Removed the original item's top-level
tool approvals: `lem-weil-l-adic-extension-integers-dvr`,
`det-prop-sfb-qlbar-colimit-x-integral-limit`, `sk-prop-sfb-cartesian-coefficients`,
`lem-weil-pbc-constant-completion-equivalence`,
`lem-weil-pbc-flat-scalar-restriction-kflat`, `lem-weil-pbc-ringed-topos-kflat-pullback`,
`lem-pe-kflat-scalar-tower-realization`, `lem-weil-tower-category-levelwise-abelian`,
`lem-weil-pbc-diagram-kflat-replacements`, `lem-weil-proetale-countable-products-exact`,
and `lem-weil-strict-roos-comparison`. Relevant mathematics remains under the substep nodes.
The two unused naturality clauses of IsLocalized are omitted from the localization substep.
No module is withdrawn and no global pruning is claimed. The unit route remains intact.

## Where the brief, the DAG or earlier work was wrong

The similar parent `integralPullbackStrictRoosNormalization` depends on this item in
the DAG. Applying it would be circular. This packet uses its definitions only.
The original plan did not supply a declaration packaging the needed normalized chain
witnesses or the full localized augmentation equations. These are explicit substeps now.
The descent step asserts neither those witnesses nor resolving-class preservation,
coefficient equality or completed-pullback compatibility, and is strictly smaller.

The direct assembly of both natural isomorphisms reached its final tactics but exceeded
the server limit while reducing concrete inverse-image and completion constructions.
No file was divided merely to evade the limit. The remaining mathematical descent of
localized representatives is explicitly stated as a new independent theorem with its
full proof in words. The coefficient-alias experiments were reverted. The final assembly uses a pure logical
helper with abstract types and predicates; it compiled in 55 seconds.
The new statements keep unbounded, noncomplete inputs, distinguish completed and constant
coefficients, and never assume the finite quotient terms are themselves K-flat over the
completed ring. Zero complexes and identity pullbacks preserve all formulas.

## New nodes

`lem-sfb-integral-roos-chain-representatives` supplies the strict comparison witnesses,
normalized augmentations and normalized Roos comparisons. It asserts no completion
isomorphisms or resolving-class preservation.

`lem-sfb-integral-roos-resolving-counits` preserves the flat-term K-flat resolving class
under the three operations and proves invertibility of the four canonical counits.
It contains no Roos coordinate data or localized augmentation equations.

`lem-sfb-integral-roos-augmentation-localization` assumes fixed normalized chain data
and identifies the three localized augmentation maps with their unit/comparison formulas.
It asserts neither existence of those data nor counit invertibility.

`lem-sfb-integral-roos-completion-isomorphisms` assumes invertible reduction counits
and the two localized unit equations, and constructs just the natural completion
isomorphisms preserving those units. It supplies no other clauses of the item.

`lem-sfb-integral-roos-completion-reflector-comparison` proves the unit-compatible
actual/quotient completion comparison for an arbitrary adic datum. It has no morphism,
Roos representative or resolving-class assumptions and reuses the existing private proof.

Each new hole has its own module, DAG node, source and complete proof in words. The
original node's proof follows the assembly. Searches covered the project's existing
strict-tower and completion APIs, Mathlib adic-completion and pullback APIs, and the current
blueprint's Roos, completion-unit and K-flat framework nodes. The logged searches found
no existing statement packaging these exact normalized clauses.

Validation: the main theorem compiled with only line-length warnings, which were then fixed.
All five supporting modules compiled. The delivery tool runs the final clean checks.

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
