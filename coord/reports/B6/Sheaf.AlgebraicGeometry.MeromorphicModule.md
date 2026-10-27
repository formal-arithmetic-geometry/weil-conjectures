## What changed

Completed all proofs in `lean/Sheaf/AlgebraicGeometry/MeromorphicModule.lean`.
The restriction map is constructed by quotient descent, with semilinearity and fraction
formulas proved directly. Fraction induction proves identity, composition, and naturality
of ordinary localization. A private presheaf isomorphism applies Mathlib's
`LocalizedModule.equivTensorProduct`; the monoidal sheafification tensorator proves the
existing tensor comparison. For unique extension, multiplication by a denominator is
invertible on the restricted localization presheaf. The restricted sheafification unit is
locally bijective, so its universal property descends the inverse. Sectionwise localization
lifts then form a natural transformation and descend uniquely by the sheafification
adjunction.

Added two proof imports: `Mathlib.RingTheory.Localization.BaseChange` and
`Mathlib.CategoryTheory.Sites.PreservesLocallyBijective`. Existing public imports,
public signatures, attributes, and definition bodies are preserved. All additional helpers
are private and fully proved. Updated the existing node's proof, proof dependencies, and
proof origin to record this argument. No other module is changed.

Validation: the complete module compiles through `lcompile.py` with no diagnostics
(28.6 seconds for the last proof compile). Edge cases require no exclusions: fraction
quotients handle zero rings and trivial localizations, and the sheafification argument
also applies to the empty scheme. No affine, reducedness, or nonemptiness assumptions
were introduced.

## Proved and sorry left

Closed 6 original holes, all attached to `def-sc-meromorphic-module`:

- `AlgebraicGeometry.Scheme.Modules.exists_meromorphicRestriction`
- `AlgebraicGeometry.Scheme.Modules.meromorphicRestriction_id`
- `AlgebraicGeometry.Scheme.Modules.meromorphicRestriction_comp`
- `AlgebraicGeometry.Scheme.Modules.meromorphicLocalization_natural`
- `AlgebraicGeometry.Scheme.Modules.meromorphicModule_tensor_iso`
- `AlgebraicGeometry.Scheme.Modules.exists_meromorphicSectionMap`

Holes added: 0. Holes remaining in the delivered module: 0. Split off: 0.
The scalar extension is chosen only after proving unique existence; restriction is
constructed explicitly by quotient descent in its now-proved existence theorem.

## No longer needed

No imports, nodes, or modules are withdrawn. The original node had no proof dependencies
to prune. The tensor proof needs no trivializing-open construction: the general sectionwise
localization-tensor comparison and monoidal sheafification suffice. The existing
invertibility hypothesis and all public imports are retained.

## Where the brief, the DAG or earlier work was wrong

The definition node had no numbered proof plan despite containing six theorem holes.
The delivery supplies the complete fraction and sheafification argument. The original
tensor theorem's docstring proposed gluing trivializations; the direct presheaf tensor
comparison is shorter, works for every module, and preserves the theorem's existing type.
The updated docstring and DAG describe that proof. Sources read: Stacks Divisors Tags
01X2 and 01X4, including the paragraph immediately preceding Definition 01X4, and Modules
Tag 01D1 (`lemma-simple-invert-module`). The proof of inverse descent through the locally
bijective sheafification unit is written by B6. There is no statement or definition repair
and no change to the unit route.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
