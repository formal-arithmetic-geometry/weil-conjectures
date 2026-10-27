## What changed

Proved `WeilConjectures.AmbientPullbackTensor.tensorData_existsUnique` from the
ordinary comparison on ringed sites, the unbounded total-tensor construction,
and uniqueness of its derived model. The ordinary-site proof retains independent
site and coefficient universes and the supplied adjunction. Its generator formula
is proved by evaluating the set-sheaf adjunction unit on the inverse-image pure pairing.

The generic construction and uniqueness results live in new Sheaf modules. The
ambient `TensorData` now abbreviates a generic bundle with the same two dependent
fields, avoiding expensive kernel unfolding of the selected ambient pullback.
A second generic record bundles the ordinary normalization and flatness properties,
avoiding an expensive specialization of their expanded conjunction. Its pure tensor
is the canonical sheafification construction, and all its data fields are explicit.
The ordinary construction also retains the scalar-extension functor through its
object and map presentation, so the tensor and flatness proofs use an abstract
functor rather than repeatedly unfolding its sheafification construction.
Pure-pairing evaluation and scalar multiplication are proved for abstract modules
before specializing to pullback objects. The geometric lift is retained through its ring and module presentation before
constructing the structural map. The exactness proof also abstracts that selected
pullback before using evaluation. The finite-limit proof uses a componentwise
natural isomorphism of the underlying section functors, so it can reflect limits
without unfolding an entire evaluation functor. Bundle extensionality and the normalized ordinary-to-derived assembly are checked
with an abstract exact functor before specializing to the ambient pullback.
The change record lists all declaration-search hits and identifies unrelated
short-name matches. The finite-colimit proof names the general preservation lemma explicitly, avoiding
a broad instance search on the selected pullback.
The new `TensorSection` module retains the explicit sheafified pure tensor at
independent universe sizes. The ordinary data definition and ambient `pure`
abbreviation use that constructor, with the ambient output type retained. This
shares the canonical construction before selecting the pullback.
No source-library declaration or target statement is changed.

Validation: all seven modules compiled, and the affected three modules were
rechecked after making the tensor-section wrapper an abbreviation. The final
exactness proof compiled; both unchanged consumer modules compiled. A universal
`rfl` probe verified that the revised ambient pure section equals the original
`SemilinearSections.tensorSection` for every finite or sequence site and every
section. The temporary consumer copies and probe are excluded from the packet.

## Proved and sorry left

Original holes: two. Closed:
`WeilConjectures.AmbientPullbackTensor.tensorData_existsUnique`.

Remaining original hole:
`WeilConjectures.AmbientPullbackTensor.ambientPullbackTensorCoherence`
(node `lem-sf-ambient-pullback-tensor-coherence`).

New declarations with complete proofs:
`WeilConjectures.SemilinearSections.sitePullbackTensorGenerators`,
`WeilConjectures.IndependentTensorModel.modelOfOrdinary`, and
`WeilConjectures.TensorModelUniqueness.tensorComparisonModel_unique`.
`WeilConjectures.SemilinearSections.BundledTensorComparison` and
`WeilConjectures.SemilinearSections.OrdinaryTensorPullbackData` have no sorry fields.
`SheafOfModules.sheafTensorSection` is an explicit definition with zero holes.
No new holes are added, and no axiom or hollow definition is introduced.

## No longer needed

The following private proof imports are removed from the ambient module because
its completed proofs do not use them:

- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison`
- `Sheaf.AlgebraicGeometry.ProEtaleTensorCompositionUnit`
- `Sheaf.CategoryTheory.ModulePullbackTensorIso`
- `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`
- `WeilConjectures.CategoryTheory.SiteMorphismComposition`
- `Mathlib.Algebra.Homology.ShortComplex.ExactFunctor` (the exactness proof now
  reflects finite limits directly).
- The redundant `Mathlib.Algebra.Homology.BifunctorShift` proof import (already public
  through the statement foundation).

The ordinary-site module keeps `PullbackExistsOfUniverses` as a private proof import.
Its public statement needs only the ordinary-data foundation and flatness API.
The ordinary-site module also omits
`Sheaf.Paper.RingedTopoiCanonicalTensorPullback`: it constructs the ordinary
comparison directly and uses the generic ringed-topos K-flat theorem. It omits `Sheaf.Paper.SystemOrdinaryTensorReduction` and
`lem-pur-system-ordinary-tensor-reduction`: the generic pure-section extensionality
lemma in `CochainTensoratorExistence` supplies its only needed consequence.

The unfinished ambient coherence theorem retains its planned dependencies in the
DAG. This packet does not withdraw those statements, any unit step, any source
library declaration, or any module. There is no claim that a dependency is globally
unused solely because this module no longer imports it directly.

## Where the brief, the DAG or earlier work was wrong

The theorem `tensorComparison_exists` in `VaryingRingTensorComparison` fixes
coefficients in universe `u + 1` for schemes in universe `u`. The ambient sequence categories require an independently enlarged
coefficient universe. The added ordinary, total and uniqueness interfaces state
that specialization explicitly; they preserve the planned ringed-site argument.
The original specialized `TensorData` structure also caused roughly thirty seconds
of kernel checking by unfolding the chosen ambient pullback. The generic bundle
keeps the same data while abstracting that functor. The final assembly is likewise
proved generically inside the ambient module before specializing to the selected
pullback, avoiding repeated kernel conversion through that construction.

## New nodes

`lem-sf-site-pullback-tensor-generators` records the normalized ordinary comparison,
its naturality and uniqueness, and preservation of flat-term K-flat representatives.
The statement includes identity, empty-site, zero-ring and nonflat structural-map
cases; it places no flatness condition on transitions of coefficient systems.

`lem-sf-exact-tensor-model-construction-independent` constructs the unbounded total
and derived comparison from a natural ordinary tensor isomorphism and preservation
of the representative class. Its chain and localization equations are proved.

`lem-sf-tensor-comparison-model-uniqueness` proves uniqueness on total summands and
then on all derived inputs by representative-localization faithfulness.

`def-sf-bundled-tensor-comparison` records the two-field generic data bundle.

`def-sf-ordinary-tensor-pullback-data` records the independent-size pure tensor,
normalization predicate, and the ordinary comparison record. The remaining record
fields are propositions, so the normalized ordinary family determines its data.

Change record: `coord/changes/ambient-tensor-data-bundle.md`.

`def-sf-common-sheaf-tensor-section` records the shared explicit sheafification image
of a pure tensor. It is a definition with no proof holes.


Additional change record: `coord/changes/ambient-pure-section.md`.

## Second reading by Y9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
