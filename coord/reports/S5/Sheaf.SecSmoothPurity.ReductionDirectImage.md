## What changed

Proved both declarations in `Sheaf.SecSmoothPurity.ReductionDirectImage`, with their
signatures and all public imports unchanged. Added proved private transport helpers for
intrinsic bounded constructible finite-Tor membership, the finite-window proper projection
argument, and a generic categorical cocycle-pasting lemma. No definition interface or
consumer was changed.

The unit route remains compactification, open scalar exchange, finite-free approximation
with a uniform cohomological window, and identification of the specified proper counit
mate. The proper projection proof deliberately uses
`finiteConstantProjectionComponent_isIso`, rather than the full proper torsion projection
formula. The bound is the existing source theorem
`Etale.isZero_rightDerived_lowerStar_of_two_mul_lt`; it works over the given arbitrary
field and finite coefficient ring. The normalized scalar square identifies the actual
comparison, rather than choosing an unrelated isomorphism of its endpoints.

Tool requests for the independent reader: use
`lem-fix-etale-origin-scalar-projection-square` and
`def-fix-proper-etale-origin-scalar-data` for the existing canonical-mate API;
`lem-exc-intrinsic-tor-amplitude-transport` and
`new-etale-proetale-exceptional-object-comparison` for changes between the two fixed
coefficient presentations; and the canonical realization comparisons in
`lem-finite-compact-support-scalar-transport` for compact-support membership. These tools
perform presentation/normalization changes and preserve the unit's projection argument.
The finite-ring origin and finite-localizing preservation modules are imported with
`import all` to reuse their already-proved private presentation lemmas. No new theorem
with an unproved body is introduced.

## Proved and sorry left

Closed 2 of the item's 2 holes:

- `AlgebraicGeometry.ProEtale.reductionDirectImage_isIso`
- `AlgebraicGeometry.ProEtale.reductionDirectImage_cocycle`

Added 0 holes; split off 0 statements. There are no `sorry` occurrences in the item.
The proof uses existing declared dependencies, including
`SupportedEtaleTensorOrigin.supported_etale_tensor_origin` and
`etaleOriginScalarProjectionSquare`, whose unfinished proofs remain in their own modules.
This is a proof from the stated library dependencies, not an assertion that the entire
transitive dependency closure is axiom-free.

Both original theorem signatures were compared byte-for-byte through `:= by` and are
unchanged. All lines have at most 100 characters. Compilation and delivery checks are
recorded by the delivery tool.

## No longer needed

Removed direct proof imports:

- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.AlgebraicGeometry.ProEtaleOpenTensor`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.CategoryTheory.RingedSliceExtensionTensor`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB`
- `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy`
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel`
- `Sheaf.AlgebraicGeometry.Sites.FiniteTorsionEtaleCohomologicalDimension`
- `Sheaf.AlgebraicGeometry.Sites.TorsionEtaleCohomologicalDimension`
- `WeilConjectures.AlgebraicGeometry.InjectiveModuleDirectImageAcyclic`
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence`
- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`
- `Sheaf.Paper.SpDirectImageEtaleMate`
- `Sheaf.Paper.DirectImageChangeRingTranspose`

The original direct imports of `FiniteConstantProjectionFormula`,
`FiniteLocalizingExceptionalPreservation`, and `FiniteRingConstructibleDerivedOrigin`
are replaced by `import all` of the same modules to reuse proved private helpers.
All public imports remain.

The node no longer directly needs `def-kun-cd`,
`lem-weil-pbc-module-abelian-derived-direct-image-comparison`,
`lem-sp-direct-image-change-ring-transpose`, or
`lem-sp-direct-image-etale-mate-isomorphism`: the existing upstream module-coefficient
bound and the normalized etale-origin scalar square provide these interfaces already.
The same finite-window projection theorem and the same supported-etale-origin and
proper/open cocycle nodes are retained. This removes direct dependencies only; no
source-library declaration or module is withdrawn, and other users may still need them.
No module is claimed to be globally pruned.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The module and node had several equivalent coefficient
presentations. Their exact realization equivalence, homology comparison, and Tor transport
must be used explicitly; they are not silently identified. Finite homology support is
converted to and from boundedness, including the zero object. The finite-stratification
comparison includes the empty scheme and zero coefficient ring. Non-flat extensions such
as Z/ell^2 to Z/ell remain allowed: boundedness of the supported tensor comes from the
finite-Tor input, not from any finite projective dimension of B over A.

The current live item source was used. Its quarantine/rework entry was read; neither the
archive nor the Lean attachment was deleted. No forced adaptations and no new nodes.

## Second reading by S5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
