## What changed

Implemented the five original theorem proofs without changing their signatures.
Exactness uses the existing canonical constant-coefficient pullback instances;
derived factorization and cohomology use the exact-functor API. The actual
base-changed strata are retained, including empty strata. Composition of module
pullbacks identifies their restrictions. Existing finite-local-constancy pullback
and stalk comparison lemmas give local constancy, finite stalks and finite generation.

For the specified trivializing covering, base change of the precoverage gives the
actual covering required by the statement. Private proved helpers transport module
sheaves to the AsSmall site, apply ringed-site localization, and show that pullback
preserves the same constant module model. The last comparison follows by uniqueness
of left adjoints to terminal-section functors, after restricting scalars along the
constant-ring unit. This avoids identifying slice sites with sites of covering schemes.
The two final theorems assemble constructibility and the unchanged vanishing interval.
The node's proof, proof dependencies and proof origin follow this implementation.

Validation: the complete item compiled through `lcompile.py` in 29.1 seconds,
with no warnings. The original five theorem signatures are unchanged. The interface checker reports
no downstream-visible changes; every helper instance is local.

## Proved and sorry left

Original holes closed (5):

- `AlgebraicGeometry.Scheme.intrinsicFiniteModulePullback_exact`
- `AlgebraicGeometry.Scheme.intrinsicFiniteModulePullback_derived`
- `AlgebraicGeometry.Scheme.intrinsicFiniteModulePullback_stratification`
- `AlgebraicGeometry.Scheme.intrinsicFiniteModulePullback_constructible`
- `AlgebraicGeometry.Scheme.intrinsicFiniteDerivedPullback_bounded_constructible`

Holes added: none. Sorry left: none. Split off: none. All new helpers are private
and proved in the item module. This is a proof from existing named declarations;
those declarations retain any pre-existing holes of their own.

## No longer needed

Removed proof imports:

- `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImageStalk`
- `Sheaf.SixFunctors.GeometricInverseImageConstantModule`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`

Removed these nodes from the item's direct proof dependencies and the top-level
`tool_uses` list, retaining the order of all other approvals:

- `lem-pe-constant-left-module-inverse-image`: exactness is already instantiated;
  finite local constancy is supplied by its existing pullback theorem.
- `lem-pur-proetale-inverse-image-stalk`: use that finite-local-constancy theorem
  and the existing intrinsic/fixed stalk finiteness equivalence.
- `lem-sfb-geometric-inverse-image-constant-module`: prove the same-model
  comparison directly by the section adjunction on the localized site.
- `lem-weil-proetale-weakly-etale-localization`: localize on the small site and
  transport along AsSmall, so no comparison with the site's covering scheme is needed.

These are direct dependency removals, not withdrawals: some remain transitively
needed by reused results. No source-library declarations or modules are removed.
The blueprint unit and its route are unchanged.

## Where the brief, the DAG or earlier work was wrong

The planned general ringed-site localization theorem has equal site-object,
site-morphism and coefficient universes. The concrete pro-etale site does not
meet that presentation directly. Apply it to the existing AsSmall site model and
transport the result back. This is an interface mismatch, not a disputed statement.
The earlier plan also repeats exactness and finite-local-constancy arguments
already implemented in the library; those existing results suffice here.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
