## What changed

Supplied proofs for all thirteen original holes in
`lean/Sheaf/Paper/RingedOpenStrictReduction.lean`. All original public declaration
signatures and public imports are preserved. The two endpoint definition bodies and the strict
complex comparison body now specialize generic computations, with checked
definitional equality to their originals. The new public definitions
`cbcModelComplexIso`, `cbcModelLeft` and `cbcModelRight` construct these maps. All other new helpers are private and proved; no other
Lean module is changed.

Finite coefficient restriction comes from continuous pushforward/sheafification
comparisons, and completed restriction from preservation of inverse limits. Their
naturality gives the quotient and projection squares. The module extension is exact
by slice transport and localized-system exactness. Scalar restriction is induced by
the identity on extension summands. Scalar extension is the unique comparison of
left adjoints of the commuting right-adjoint square, identified with the required
pure-tensor formula.

The inverse finite-level comparison commutes with quotient transitions by the
coefficient quotient square. These inverse maps assemble using
`NatTrans.ofOpSequence`; objectwise invertibility gives the strict tower isomorphism
with its prescribed forward maps. Generator calculations prove augmentation,
normalization and three-index coherence.

The concrete slice equivalence is an algebraic inverse image followed by scalar
extension along a ring isomorphism. The existing ringed-topos pullback theorem
therefore transports flat-term K-flat complexes to the slice. The ringed-open
resolution theorem then applies to the actual extension functor. The generic
resolving-class localization argument `modelPull_existsUnique` from
`ProEtaleConstantReductionModels` descends the inverse strict comparison. Inverting its
normalized equation gives the requested derived comparison and transfers uniqueness.
The derived-model records contain the existing completed-coefficient reduction
functors, counits, universal properties and computation laws. The generic helper
is instantiated with these actual module categories and maps.
Both endpoint computation maps are invertible on the specified representatives.

New proof imports expose the already proved private comparison APIs in
`CompletedAdicCoefficientDatum`, `AdicCoefficientDatum`,
`KFlatRingedToposPullback` and `ProEtaleConstantReductionModels`. The scalar-extension
ring-isomorphism theorem, the existing ordinary scalar-extension functor, and the
ringed-open flat-resolution theorem supply the remaining transport steps. These
imports are private; the original public import interface is unchanged.

The source citations are retained; the main theorem's proof narrative and the node's proof steps,
proof dependencies and proof origin record the implemented argument. No new node,
lemma or split-off module is introduced. The three computation definitions
are factored through their generic constructions to avoid repeated kernel
conversions of the completed coefficient category.
The proof-file commands are documented in
`coord/changes/C1-ringed-open-strict-reduction-private-proof.md`; the conservative
interface checker flags the three computation definition bodies and file-local commands.
The change record lists their users and requests the renewed meaning review.

Validation: the complete candidate, with all thirteen original theorem holes
filled and no new holes, passes the exact delivery axiom probe in 55.4 seconds.
The scan reports no direct `sorry` and no forbidden axiom. Its only warning is the
tool-supplied probe's long line, beyond the delivered source. The source has no
warnings. A separate Lean diagnostic proves all three definitions equal
to their original published formulas by `rfl` (8.5 seconds). A scalar diagnostic
also shows that binding the direct-sum carrier reduces two private component-formula
checks from about eight seconds each to about 0.15 seconds each. The required
delivery tool checks the final packet again before pushing it. No compiler or
heartbeat limit is raised.

## Proved and sorry left

Original holes supplied with complete proofs:

- `cbcFiniteSliceMap_isIso`
- `cbcCompletedSliceMap_isIso`
- `cbcRingedOpenExtension_exact`
- `cbcOpenScalarIso_existsUnique`
- `cbcOpenRestrictIso_existsUnique`
- `cbcQuotientSquare`
- `cbcProjectionSquare`
- `cbcCompletedTowerExtension_exact`
- `cbcStrictReductionIso_existsUnique`
- `cbcStrictReduction_augmentation`
- `cbcStrictReduction_normalization`
- `cbcRingedOpenStrictReduction`
- `cbcStrictReduction_cocycle`

Original holes closed: thirteen. Holes remaining in the candidate: zero. Holes
added: zero. Split-off statements: zero. Imported declarations are used as supplied
by the library; this does not claim their transitive proofs are all free of `sorry`.

## No longer needed

Removed original private imports:

- `Sheaf.CategoryTheory.RingedSliceExtensionTensor`
- `Sheaf.SixFunctors.OpenTensorNormalization`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Mathlib.CategoryTheory.Localization.Predicate`

The node's direct proof-dependency edges to
`lem-weil-pbc-ringed-slice-extension-tensor` and
`lem-sf-open-tensor-normalization` are replaced by the normalized adjunction
construction. The ordinary normalization and cocycle are proved for every complex,
so they do not need `lem-pur-kflat-change-of-rings`. Descent reuses the existing
generic resolving-class localization proof, so it does not directly use
`lem-pur-derived-change-of-rings` or
`lem-weil-pbc-site-derived-tensor-descent`.

These are removals of direct imports and dependency edges only. Some modules remain
transitive dependencies of the retained tools, and other consumers remain. No whole
module is claimed as pruned or withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement repair was needed. The endpoint and strict-complex computation bodies are factored
through generic definitions because repeated conversions of their completed
coefficient category exceeded the compile limit. All three changed bodies are
definitionally equal to the originals; the change record covers the renewed
meaning review. The coefficient comparisons use the actual
continuous-function coefficient sheaves and their completed inverse limits.
The ordinary scalar comparison admits a shorter normalized-adjunction argument.
The planned ringed-slice tensor theorem gives a presheaf-tensor isomorphism without
the section normalization required here. The normalization API supplies an
existential operations package. Applying them would still require comparisons
with the fixed scalar-extension functors in this module. The new proof instead
checks their adjunction and the prescribed section formula directly.
The tower normalization and cocycle hold on all ordinary complexes, before imposing
K-flatness. A checked generic localization argument already exists in
`ProEtaleConstantReductionModels`; using it preserves the blueprint's resolution and
descent route. The node records these changes.

Large constructions are kept behind proved component formulas and private
irreducibility attributes where necessary. The private scalar component formulas
use the explicit direct sum of the original module sections as their input type,
avoiding repeated reconstruction of scalar-restricted module structures. The final comparison supplies the existing functor-instance proofs explicitly.
Its generic ring-sheaf wrapper packages the actual reduction functors and counits
before specializing the completed coefficient rings. The generic helper proves
invertibility of the endpoint maps by composing factorization and counit
isomorphisms; its conclusion already has the final theorem's curried
representative hypotheses. The final comparison section respects local opacity,
with the computation wrappers left reducible. The two standard derived-category
instances have file-local priority 2000, as in the existing direct-image module.
No compile or heartbeat limit is raised.

A raw dependency traversal encounters the existing lower cycle
`lem-pc-ring-hom-extension-differential` →
`lem-pc-ring-hom-extension-differential-adjacent` →
`lem-pc-ring-hom-extension-differential`. The original shared item already reaches
this cycle. None of those nodes is changed. The added proof dependencies have no
path back to this item, so this delivery adds no cycle through the item.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
