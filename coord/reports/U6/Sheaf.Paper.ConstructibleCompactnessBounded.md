## What changed

Proved both theorems of `Sheaf.Paper.ConstructibleCompactnessBounded` without changing
any public signature, public import, or the comparison-map definition. All changes
are confined to the item and its DAG records, including one new attachment of an
already proved source-library theorem. No source-library file was edited.

The proof uses `DerivedCategory.compactFor_of_isGE_of_isLE`, found in the adopted
source library, to perform exactly the blueprint's bounded-width induction. Private
helpers identify its finite-support factorization conclusion with the canonical
additive comparison, and prove injectivity using the coproduct coordinate projections.
`det_ind_heart_ii_sums` supplies the single-degree case, and the empty-sum clause of
`indConstructible_filteredColimits_and_sums` supplies zero membership of IndCons.

A private Ext transport preserves the item's explicitly bound derived localization:
nonnegative shifts use `Abelian.Ext.homAddEquiv` and Ext postcomposition; negative
shifts vanish by the standard t-structure. Shifting the input family changes its
bounds to `[a-s,b-s]`, retaining width `(b-a).toNat`. This covers every integer shift,
width zero, empty families, zero sheaves, and both coefficient rings. The auxiliary
finite field for the algebraic-closure case is explicitly the bottom subextension.

## Proved and sorry left

Closed 2 of 2 existing holes, both on node `det-constructible-compactness-bounded`:

- `AlgebraicGeometry.ProEtale.constructible_compactness_bounded`.
- `AlgebraicGeometry.ProEtale.constructible_compactness_bounded_padicAlgCl`.

Holes added: 0. Holes remaining in the item: 0. No split-off unproved statements.
Remote single-file validation passed in 19.4 seconds with no errors or warnings.
The new node attaches an existing source-library theorem whose own proof is complete.
This is a proof from existing declarations; it does not assert that all those
declarations' transitive proof dependencies are already free of holes.

## No longer needed

Removed the following private proof imports:

- `WeilConjectures.CategoryTheory.TruncationTriangle`.
- `Mathlib.Algebra.Homology.Embedding.CochainComplex`.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`.
- `Sheaf.Paper.LocalizingClosureExistence`.
- `Sheaf.Paper.AmbientIndDerivedSums`.

The explicit cochain truncation-triangle package
`lem-weil-pbc-truncation-triangle` is unnecessary: the reused bounded induction uses
Mathlib's standard derived t-structure triangles. The localizing-closure package
`det-def-localizing-closure-existence` is unnecessary: K-injective resolutions and
ambient coproducts come from the existing Grothendieck abelian category API.
`det-ambient-ind-derived-sums` is unnecessary: the reused generic homology-predicate
truncation lemmas need only repleteness and zero membership, supplied directly as above.
Removed the item's former tool-use entries for the first two packages.

The elementary derived-category, truncation-cohomology, Hom-exactness and triangulated
inputs are retained through the new attachment of the source-library induction.
All public imports are retained. No module is withdrawn; the pruning above concerns
this proof's dependencies, and does not claim that their other users disappear.

## Where the brief, the DAG or earlier work was wrong

The DAG plan had already been implemented, in a coefficient-independent form, in
`WeilConjectures.CategoryTheory.DerivedCategory.CompactOfBoundedExt`; the item did not
import it. Reusing that proof preserves the unit's induction and extension route.
The source-library extension argument needs only finite-support factorization on
the outer families: coordinate projections detect the vanishing boundary separately
in each summand, followed by two Hom-exactness lifts.

The Ext-sum theorem uses a fixed derived localization whereas this item explicitly
binds a choice. Applying the theorem directly would identify different category
presentations. The proved Ext transport supplies the required compatibility instead
of changing either theorem's signature.

The rework table has an older quarantine entry, but the item source is currently
present. The delivery preserves all existing declarations and attachments and does
not withdraw any archived or current module.

## New nodes

`lem-sfb-bounded-family-compact-devissage` attaches
`DerivedCategory.compactFor_of_isGE_of_isLE` in the existing adopted source module.
It states the abstract single-degree-to-bounded-family induction, with a replete
heart predicate containing zero, coproducts and K-injective resolutions. Its proof
uses the same truncation and extension steps as the blueprint. Searches with
LeanSearch, LeanFinder, Loogle and ripgrep found the adopted theorem and no complete
Mathlib match; the DAG search found no prior attachment. No new Lean module or
unproved theorem accompanies this node. No change record is required because no
public interface or shared module changes.

## Second reading by U6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
