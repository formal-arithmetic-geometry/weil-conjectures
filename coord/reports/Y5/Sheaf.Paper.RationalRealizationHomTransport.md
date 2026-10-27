## What changed

The original rationalRealizationHomTransport statement and
rationalRealizationLocalizedLinear construction are unchanged. The item obtains the
actual ordinary tensor-localization functor and its exactness from the proved
scalarLocalization_sheaf_exact, with independent site universes. A generic
rationalLocalizationModulesLinear wrapper installs the existing constant-section action
on its pbcModules category; it contains no hole or choice of unproved data.

The new rationalRealizationOrdinaryLocalization supplies an additive ordinary module
equivalence G0, its scalar equation and an ordinary tensor-composition comparison.
G0.mapDerivedCategory is an equivalence. The proved exact_derived_semilinear descends its
scalar compatibility. leftDerivedUnique compares exact termwise extension with the
specified pbcDerivedExtend using its universal counit. mapDerivedCategoryCompIso and
mapDerivedCategoryNatIso give the natural functor comparison.

The new scalarLocalization_telescopeOfUniverses supplies the normalized localization
telescope on the actual site and its scalar equation. The already proved generic
hom_comparison_of_telescope gives the Hom comparison from these data. The private
homConjugation and transportHomComparison helpers explicitly transport the linear Hom
equivalences. Functor.CommShift.ofIso transfers shifts, naturality gives the fraction
formula, and scalarHomComparison_of_normalized supplies all compatibility equations.

Proof imports are the two new modules and
WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor. The existing
scalar-localization module is additionally imported with import all to reuse its proved
private generic helpers. All existing public imports, signatures and definitions are
preserved. No other existing module is changed.

## Proved and sorry left

Closed in the item: AlgebraicGeometry.Scheme.rationalRealizationHomTransport (one of one
original holes), by reduction to the following two independent intermediate statements.
There is no sorry in the item or inside a definition. The full sandbox compiled with
profiling; its only remaining warnings were development options and letI style, removed
for delivery. The generic Hom transport also compiled separately before its scratch
file was removed. Final compilation and preflight are performed by deliver3.py.

Added: AlgebraicGeometry.Scheme.rationalRealizationOrdinaryLocalization, node
lem-per-rational-realization-ordinary-localization, in the new module of the same name.
This concerns only ordinary module sheaves, their scalar actions and tensor extension.
It contains no derived functor, Hom equivalence or Hom-continuity predicate.

Added: CategoryTheory.scalarLocalization_telescopeOfUniverses, node
lem-weil-pbc-scalar-localization-telescope-of-universes, in
Sheaf.CategoryTheory.ScalarLocalizationTelescopeOfUniverses. This concerns the derived
localization adjunction, its telescope triangle, leg/shift normalization and scalar
compatibility. It contains no Hom equivalence or Hom-continuity predicate and applies
to arbitrary ringed sites with independent universe levels.

This is a decomposition: one original hole is replaced by two genuine parts of the
argument, for net minus one holes closed. Each new theorem has its complete proof in
words and source in its docstring and DAG node. The remaining theorems are not the item
under a different name or with its hypothesis repackaged. No new definition chooses an
arbitrary witness from a theorem with sorry; existence witnesses are eliminated only
inside proofs.

## No longer needed

No existing import, node or module is removed or withdrawn. The original
lem-pur-ring-iso-derived-transport and
lem-weil-l-adic-integers-localization-uniformizer are inputs of the new ordinary
coefficient-comparison lemma. The original exact-derived-functor and factorization
inputs remain in the derived comparison. The scalar-localization-derived-Hom module
remains needed for its proved generic Hom and normalization helpers. The small-category
specialization scalarLocalization_derivedHom cannot itself be applied to X.ProEt; its
mathematical telescope argument is retained through the new independent-universe step.
No module is claimed as pruned. The blueprint unit statement and route stay unchanged.

## Where the brief, the DAG or earlier work was wrong

The plan's direct application of scalarLocalization_derivedHom overlooks a universe
restriction: it assumes a SmallCategory, with the same universe for objects and arrows.
The actual X.ProEt has object universe u+1 and morphism universe u. The compiler rejected
the proposed ringedLocalizationRing as having Sheaf.{u+1,...} where pbcModules requires
Sheaf.{u,...}. The first attempt timed out while elaborating this action; the generic wrapper exposed
the universe mismatch directly.
The existing RingedSectionLocalizationOfUniverses and the coefficient-action API in
RationalContinuousCoefficientDerivedLocalization already handle the actual site. This
delivery uses them and isolates the missing telescope interface; no shared definition or
universe binder is changed, and no compile limit is raised.

The rework row records quarantine following an import of SfP1ProjectionTraceFalseTail.
The current item source is present and has no direct import of that module. This delivery
preserves the item and its Lean attachment and deletes no quarantined file. There is no
current Y5 return entry. LeanFinder was unavailable; LeanSearch, Loogle and local searches
were used and recorded in the new nodes.

Edge cases: localization is sheafified and allows locally varying denominators. Ordinary
ring-isomorphism restriction is an equivalence for zero and torsion modules and on the
empty scheme. The independent-universe telescope includes t=0 and nilpotent t; no scalar
injectivity, nonzero object or regularity assumption is introduced.

## New nodes

lem-per-rational-realization-ordinary-localization records the normalized ordinary
coefficient presentation, scalar-compatible module equivalence and tensor comparison.
Its source, chapter/unit and blueprint ancestry come from the item's coefficient step.

lem-weil-pbc-scalar-localization-telescope-of-universes records the existing normalized
telescope argument on a site with independent universe levels. Its source and proof in
words specify either direct degreewise construction or transport through AsSmall. The
item's node records the actual exactness, derived comparison, generic Hom calculation and
transport route. No change record is needed: no existing signature, public import,
definition or consumer is changed.

Blueprint searches: the full imported blueprint search for telescope found only the
generic homotopy-colimit preservation lemma; localization gave broader coefficient
results, with no matching normalized coefficient comparison or independent-universe
telescope statement. The new nodes inherit the original item's recorded perverse
ancestry and realize its coefficient/telescope computation steps.

## Second reading by Y5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
