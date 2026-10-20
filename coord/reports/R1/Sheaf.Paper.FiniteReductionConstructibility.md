## What changed

Proved `AlgebraicGeometry.FiniteReduction.finiteReduction_constructibility` with its
original signature. Its concrete definitions are publicly re-exported from the new
`Sheaf.Paper.FiniteReductionSystem` module, allowing independent proofs without cycles.
Added the tensor comparison, flat-extension, universal derived-extension,
constructibility, system-coherence and system-existence modules listed below.

The quotient-composition proof in `ordinaryAssociator` is explicit to avoid unfolding
sheafification during elaboration. `System.originComparison` displays the same composite
isomorphism with explicit hom and inverse fields. The semantic identity, unchanged
signatures, consumer inventory, and review obligation are recorded in
`coord/changes/finite-reduction-system-interface.md`. No source-library file changes.
The coefficient definition node now attaches to the extracted module; the main node
records the actual shorter proof and the removed approvals.

All eight delivered Lean modules compile through `lcompile.py`, with no remaining
compiler warnings. The latest individual coherence/system checks took 27.2/43.8 seconds; the main theorem
compiled in 14.4 seconds. Generic private lemmas keep the comparison and resolution
calculations independent of the concrete sheafification constructions.
The sole direct consumer, the unchanged `Sheaf.Paper.ExceptionalCoefficientComparison`,
also compiled against the overlay (26.7 seconds); its temporary copy is not delivered.
The source declaration reader confirms identical moved and main theorem signatures.
The whole-blueprint search for finite reduction found no duplicate of these concrete
fixed-scalar interfaces; the existing finite-reduction definition is the broader
adic-coefficient construction, rather than these helper assertions.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.FiniteReduction.finiteReduction_constructibility`.

Added zero holes. Every new mathematical assertion is proved:
`extend_restrict_tensor` (a natural-isomorphism definition),
`flat_extend_of_surjective`, `nonempty_derivedExtension`,
`boundedConstructible_extend`, `System.coherentAt`, and `exists_coherent_system`,
all in `AlgebraicGeometry.FiniteReduction`. All private helpers are proved.
There are no remaining `sorry` declarations in the eight delivered Lean modules.
This is a proof, not a decomposition leaving new lower holes. Existing imported
statements elsewhere retain their own proof status; no source declaration is removed
or replaced by a hole.

## No longer needed

The following original private proof imports are removed from the item:

- `Sheaf.AlgebraicGeometry.EtaleTorAmplitude`
- `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`
- `Sheaf.AlgebraicGeometry.ComparisonTorInterval`
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`
- `Sheaf.Paper.ComparisonPullbackExact`
- `Sheaf.CategoryTheory.SiteInverseImageTensor`
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`
- `Sheaf.Paper.PbcActualScalarPullback`
- `WeilConjectures.ConstructibleSheaf.Refinement`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
- `Sheaf.Paper.LocallyConstantTensor`
- `WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`

The following original public imports are relocated unchanged to the extracted
interface, which the item publicly imports; these remain needed, and are not pruning:

- `Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`
- `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude`
- `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars`
- `Mathlib.CategoryTheory.Adjunction.Unique`
- `Mathlib.Data.ZMod.Basic`

The proof no longer follows these 18 original node dependencies:

- `lem-exc-comparison-tor-interval`
- `lem-sf-etale-flat-model`
- `lem-pc-bounded-above-flat-kflat-site`
- `lem-pur-kflat-change-of-rings`
- `lem-pur-derived-change-of-rings`
- `def-kun-tor-amplitude`
- `lem-sf-comparison-pullback-exact`
- `lem-weil-pbc-left-exact-site-inverse-image-tensor`
- `def-weil-pbc-site-comparison-morphism`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
- `def-weil-pbc-etale-constructible-sheaf`
- `lem-weil-pbc-constructible-stratification-intersection`
- `lemma-constructible-of-refines`
- `prop-weil-pbc-inverse-image-modules-exact`
- `lem-weil-pbc-exact-functor-complex-cohomology`
- `lem-weil-pbc-locally-constant-tensor`
- `lem-weil-pbc-finite-locally-constant-module-values`
- `def-pur-sheaf-tensor-product`

The generic proved Tor-amplitude/flat-model API replaces the specialized flat-model
and change-of-rings chain. The source tensor constructibility theorem replaces the
manual refinement/local-constancy argument. Exact fixed-scalar comparison and adjunction
uniqueness replace the ringed-topos tensor-pullback wrappers for construction and coherence.
No module or node is withdrawn: some still occur in unchanged statement dependencies
or in other consumers, including adopted source proofs. These are pruned from this
proof route only; global closure pruning is left to the ledger/maintainer.

The following obsolete entries are removed from `tool_uses`, retaining the finite-ring
origin entry in its original order:

- `lem-exc-comparison-tor-interval`
- `lem-pc-bounded-above-flat-kflat-site`
- `lem-pur-kflat-change-of-rings`
- `lem-pur-derived-change-of-rings`
- `lem-sf-comparison-pullback-exact`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
- `lem-weil-pbc-locally-constant-tensor`
- `lem-weil-pbc-left-exact-site-inverse-image-tensor`

## Where the brief, the DAG or earlier work was wrong

The original long plan is mathematically sound, but many supplied specialized lemmas
use ringed-topos or different-universe interfaces while this statement fixes ordinary
coefficient-ring sheaves. The already proved generic Tor and tensor APIs give the
required fixed-scalar statements directly. In particular flatness of the quotient
ring over the source is never assumed. Surjectivity is used only for preservation of
flat terms; the ordinary tensor comparison and universal derived extension work for
any coefficient map. No Noetherian hypothesis on the scheme is added.

The ordinary comparison square needs its canonical normalization: arbitrary derived
isomorphisms would not suffice. The proof establishes the exact representative equations
by universal derived-functor uniqueness, and uses adjunction conjugates to prove the
ordinary square before passing to resolutions. The argument includes exponent zero,
identity quotient maps, and zero complexes. The unit's `realized` record is empty;
no designated unit step is bypassed or removed.

## New nodes

`def-pur-finite-reduction-system` (`dag/nodes/sec-smooth-purity/def-pur-finite-reduction-system.json`) owns
`Sheaf.Paper.FiniteReductionSystem`. Owns the existing concrete scalar-extension interface, extracted without changing any signature or mathematical meaning.

`lem-pur-finite-reduction-restrict-tensor` (`dag/nodes/sec-smooth-purity/lem-pur-finite-reduction-restrict-tensor.json`) owns
`Sheaf.Paper.FiniteReductionRestrictTensor`. Proves the ordinary extension/restriction tensor identity for arbitrary coefficient maps.

`lem-pur-finite-reduction-flat-extension` (`dag/nodes/sec-smooth-purity/lem-pur-finite-reduction-flat-extension.json`) owns
`Sheaf.Paper.FiniteReductionFlatExtension`. Proves preservation of flat sheaves under a surjective map of Noetherian coefficient rings, using quotient reduction and transport through its ring equivalence.

`lem-pur-finite-reduction-derived-extension` (`dag/nodes/sec-smooth-purity/lem-pur-finite-reduction-derived-extension.json`) owns
`Sheaf.Paper.FiniteReductionDerivedExtension`. Constructs the universal derived extension using the proved K-flat derivability structure.

`lem-pur-finite-reduction-etale-constructibility` (`dag/nodes/sec-smooth-purity/lem-pur-finite-reduction-etale-constructibility.json`) owns
`Sheaf.Paper.FiniteReductionEtaleConstructibility`. Proves bounded constructibility after finite scalar extension for a finite-Tor object, using the source bounded-constructible tensor theorem and reflection through exact restriction.

`lem-pur-finite-reduction-system-coherence` (`dag/nodes/sec-smooth-purity/lem-pur-finite-reduction-system-coherence.json`) owns
`Sheaf.Paper.FiniteReductionSystemCoherence`. Proves the ordinary square by conjugate adjunction pasting, then the derived square using representative normalizations and flat resolutions.

`lem-pur-finite-reduction-system-existence` (`dag/nodes/sec-smooth-purity/lem-pur-finite-reduction-system-existence.json`) owns
`Sheaf.Paper.FiniteReductionSystemExistence`. Constructs the normalized system by universal derived-functor uniqueness on common resolutions and invokes the proved coherence result.

Change record: `coord/changes/finite-reduction-system-interface.md`.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
