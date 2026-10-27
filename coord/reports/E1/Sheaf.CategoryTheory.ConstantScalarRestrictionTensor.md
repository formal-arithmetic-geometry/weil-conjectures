## What changed

Filled nine theorem proofs in
`Sheaf.CategoryTheory.ConstantScalarRestrictionTensor`. All existing public signatures,
definitions and public imports are preserved. No source-library file was changed.

The restriction equivalence reuses `constant_ring_module_sheaves`, with explicit cancellation
isomorphisms for restriction along `constantCommuteCompose`. Additivity is sectionwise, and
exactness follows from equivalence preservation of limits and colimits. The canonical complex
comparison respects Koszul symmetry by checking its coproduct injections. Flatness transports
through the monoidal equivalence and its inverse; the existing abstract total-tensor equivalence
lemma supplies the K-flat tests. The fixed-coefficient flat cover is constructed by transporting
the existing ringed flat cover, including its natural epimorphic augmentation.

For the derived comparison, two mixed tensor counits are derived using the existing binary
derived-functor APIs. Their unique comparison, followed by `OplaxMonoidal.ofLaxSquare`, constructs
the strong monoidal structure with the required unit normalization. Its factorization is
monoidal, which proves both prescribed tensor and unit equations. The existing
`exactTensorFunctor_derived_braiding` proves compatibility with the independently fixed native
braidings. All category and derived-localization universes remain independent. The ordinary
comparison remains the existing named hole rather than a replacement statement.

Added only private proved helpers and private proof imports. Two declaration-scoped exclusions
of `GrothendieckTopology.hasSheafify_of_essentiallySmall` prevent its successor-universe instance
from interfering with the existing independent-universe sheafification and Grothendieck
instances. Their original bodies and signatures are unchanged; the exclusions do not propagate
to importers. The two existing node proof records now describe the implemented route. The preflight-requested
change record is `coord/changes/e1-constant-scalar-restriction-proof-scope.md`; it documents
the scoped elaboration commands and all 155 transitive importers. No consumer adaptation is needed.

Validation: the final complete module compiled through `lcompile.py` in 33.4 seconds with no
warnings. Direct elaboration of the total-symmetry and K-flat proofs at the concrete sheaf
categories initially timed out; proving their existing abstract-category formulations privately
before specialization resolved this without changing definitions or splitting the module.

Consumer validation: unchanged direct importers `OpenScalarFlatModelRealization`,
`IntegralAmbientTowerComparison`, `IntegralCoefficientModelRealization` and
`IntegralAmbientCoefficientPresentation` compile (21.0, 6.5, 15.0 and 31.6 seconds).
`FiniteComparisonPresentation` hits the 60-second limit both with this patch and after
recompiling the original unmodified item module (baseline item compile: 19.3 seconds).
Thus that unchanged consumer's timeout also occurs without this delivery. No consumer
adaptation is included; the delivery version was restored after this baseline comparison.

## Proved and sorry left

Closed 9 of the original 10 holes, all in namespace
`CategoryTheory.ConstantScalarRestriction`:

- `additive`
- `isEquivalence`
- `exact`
- `total_symmetry`
- `flat_iff`
- `kflat_iff`
- `fixedFlatResolutions`
- `derived_isEquivalence`
- `derived_comparison`

One original hole remains unchanged: `CategoryTheory.ConstantScalarRestriction.ordinary_exists`,
realizing `lem-sfb-constant-restriction-ordinary-monoidal` and the ordinary part of
`lem-sfb-constant-scalar-restriction-tensor`. Its source and full construction plan remain in
its docstring and existing node. The completed tensor-dependent proofs use that ordinary
structure as intended by the dependency plan.

Added holes: 0. Split off: 0. There is no `sorry` in a definition or private helper, and no new
public declaration or new module. `kflat_iff` uses the existing declared dependency
`CategoryTheory.Equivalence.exactMonoidal_totalTensor_kFlat`; its remaining proof work belongs
to that existing dependency, not to a new hole in this delivery.

## No longer needed

Removed these original private proof imports from the item:

- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.CategoryTheory.SiteCoveringAxioms`
- `Sheaf.CategoryTheory.BraidedSheafTensorGenerators`
- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`
- `WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone`
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`

The completed derived proof does not use
`lem-sfb-ringed-equivalence-resolving-tensor-descent`; its dependency edge is removed.
The more general ringed-site descent package is unnecessary for this exact monoidal
equivalence: native binary derived-functor comparison and the lax-square coherence theorem
suffice, including the unit equation and arbitrary K-flat representatives.

The item no longer directly uses `lem-weil-pbc-site-derived-tensor-descent`,
`lem-pc-tensor-mapping-cone-iso`, or `lem-pur-quasi-iso-cone-acyclic`; their obsolete top-level
`tool_uses` entries are removed. The cone argument is supplied by the already stated abstract
K-flat-equivalence dependency. These are removals of this item's direct proof edges, not claims
that these declarations are unused elsewhere in the library.

The bilinear-extension, module-sheafification-interface, sheaf-tensor-universal-property,
underlying-set-sheafification, local-lifting and ordinary constraint nodes remain needed by
the retained `ordinary_exists` hole. No such node or module is withdrawn. No blueprint unit
statement or realized unit proof step is bypassed, and no source declaration is removed.

## Where the brief, the DAG or earlier work was wrong

No statement was found false and no target or definition was repaired. The original derived
plan uses a larger ringed-site descent theorem than necessary. The existing source-library
binary derivability APIs construct exactly the normalized comparison at arbitrary independent
universes; the oplax-square theorem supplies coherence and fixes the unit at the same time.

The abstract exact-tensor braiding import exposes a high-priority sheafification instance
specialized to successor universes. At the independent universe `max u v`, it causes stuck
universe constraints in two unchanged instance bodies. Declaration-scoped exclusion of that
instance restores the original inference path. This is an elaboration issue, not a mathematical
hypothesis or interface change.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
