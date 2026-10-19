## What changed

Proved four of the six original holes in
`lean/Sheaf/Paper/SfScalarExtensionComposition.lean`, preserving every existing declaration,
signature, visibility, definition and docstring.

The integral associator conjugates ordinary derived tensor associativity by the three
specified ordinary-to-completed comparisons. The integral unit conjugates the ordinary
derived tensor unit. Both natural isomorphisms lift to the intrinsic full subcategory;
extensionality of underlying hom components proves their normalization and uniqueness.

Two private, proved helpers transport morphisms across object equalities and localize an
integral natural isomorphism. The latter proves naturality by tensor induction: zero and
addition follow from additivity, and pure tensors reduce to integral naturality using the
published scalar-localization composition formula. Its component condition gives uniqueness.
The rational associator uses the prescribed pure-tensor maps of the two scalar transitions;
the intermediate coefficient-field equivalence cancels with its inverse. The rational unit
uses the identity coefficient embedding. This follows the existing proof plan's integral
conjugation, full-subcategory lifting, and componentwise rationalization steps.

Checks of the retained module passed without errors or warnings using lcompile.py:
the earlier single-file and complete-sandbox compiles took 38.3 and 41.5 seconds.
Earlier resumed validation took 41.8 seconds. The current retry recompiled the retained
module successfully in 54.8 seconds, with no errors or warnings.
No other module was changed. Removed the eight
proof-only imports listed below; all public imports are preserved.

## Proved and sorry left

Closed four original holes:

- `WeilConjectures.sfIntegralScalarComp_existsUnique`.
- `WeilConjectures.sfIntegralScalarUnit_existsUnique`.
- `WeilConjectures.sfRationalScalarComp_existsUnique`.
- `WeilConjectures.sfRationalScalarUnit_existsUnique`.

Two original holes remain, both attached to `lem-weil-scalar-extension-composition`:

- `WeilConjectures.sfIntegralOrdinaryComparison_existsUnique`: still needs the canonical
  comparison on intrinsic complete objects. The finite-free comparison module uses separately
  selected ordinary/derived scalar models and the older unrestricted completeness predicate;
  applying it here requires normalized identifications with the current models and predicate.
- `WeilConjectures.sfRationalScalar_coherence`: still needs the ordinary tensor unit and
  pentagon identities and their transport through completion and rationalization. Existence
  and uniqueness of the normalized associators alone do not supply those identities.

Added zero holes; split off zero statements. All remaining proofs are exactly the original
public named theorem sorries. The four closed holes depend on existing stated results,
including the remaining comparison theorem, as intended in stage 3.

## No longer needed

Removed these direct proof-only imports, unused by the four completed proofs:

- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`.
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`.
- `Sheaf.Paper.PbcActualScalarPullback`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.

The last three imports were added to the shared source after the initial sandbox copy;
they are likewise unnecessary for the completed proofs.

The ordinary derived tensor associator and unit are reused from the existing public import
`Sheaf.Paper.ScalarExtensionComposition`. No new K-flat or tensor construction is required
for the four closed holes. The unfinished comparison and coherence obligations retain the
original mathematical route and DAG plan: in particular the finite-free comparison remains
relevant to the first unfinished obligation. No DAG node is claimed globally obsolete and
no public dependency module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The assigned file was temporarily absent from the shared checkout at the first read and
became available during the next read; work used the published file once available.

No statement discrepancy was found in the four proved declarations. The generic rational
lifting argument also handles identity embeddings, coincident coefficient fields, zero
objects, and the empty scheme: it uses only functoriality, tensor composition, and object
equalities, with no nonemptiness or nonzero-object assumption.

The DAG's full proof plan remains applicable; this is a partial proof delivery, not a
replacement of the two unfinished arguments by existence or coherence assumptions.

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
