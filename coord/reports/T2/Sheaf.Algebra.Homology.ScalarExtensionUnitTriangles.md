## What changed

Proved `SheafOfModules.exists_scalarExtensionUnit_triangles` with its public
signature unchanged. Constructed the ordinary coefficient map from the module
extension/restriction adjunction unit followed by module sheafification, proved
its naturality, and proved restriction exact by reflecting limits and colimits
through the underlying abelian sheaf functor.

Added two supporting modules, both with complete proofs:
`DerivedCoefficientMapDescent` proves preservation of the resolving right Kan
extension under postcomposition, descends the coefficient map, and proves shift
compatibility by Kan uniqueness. `ScalarExtensionCounitProperties` compares the
specified universal pair with the existing cochain model, transfers K-flat counit
invertibility, and identifies its shift with the existing triangulated shift.
The assigned theorem then constructs every resolution comparison, proves the roof
formula and uniqueness by cancellation and localization, and constructs the three
triangle squares. No existing public definition or statement changed.

On resumption, all three modules compiled against the current published build.
Preflight identified added file-level commands in the retained version. The
coefficient proofs now use explicit tensor constructors, and the two private
lemmas state their binders explicitly, avoiding both a file-level notation scope
and helper-level `omit` commands. The structural check reports no existing
interface changes. The retained shift calculation already includes the explicit
identity-map simplification missing from the older failed compile log.

## Proved and sorry left

Closed the one original hole:
`SheafOfModules.exists_scalarExtensionUnit_triangles`
(lem-weil-pbc-scalar-extension-unit-triangles).

The two supporting theorems are also proved:
`CategoryTheory.Functor.exists_derivedCoefficientMap`
(lem-sbc-derived-coefficient-map-descent) and
`SheafOfModules.scalarExtension_counit_properties`
(lem-sbc-scalar-extension-counit-properties).

No `sorry` remains in any delivered Lean module. Holes closed: one; holes added:
zero. Existing imported declarations may still depend on `sorry`; this delivery
proves the assigned theorem from their stated interfaces.

## No longer needed

Removed these direct proof imports from the current assigned module:

- `Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent`
- `Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Algebra.Homology.DerivedScalarExtensionCounitShift`
- `Sheaf.Algebra.Homology.KFlat`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`

The counit model and counit-shift modules are now used by the proved supporting
counit theorem. The resolving-class machinery remains a transitive dependency.
The proof uses no tensor-bifunctor descent or K-flat-subcategory equivalence:
lem-weil-pbc-site-derived-tensor-descent is removed from the parent's proof
route and its obsolete tool approval is removed. No globally unreachable module
is claimed: other users may retain any of these imports.

The other removed direct parent proof dependencies are
`def-pc-kflat-complex`, `def-weil-abstract-derived-category`,
`lem-pur-derived-change-of-rings`, `lem-pur-left-derived-from-kflat-class`, and
`lem-sbc-derived-scalar-extension-counit-shift`. These remain statement or
transitive dependencies of the proved supporting lemmas; they are not separate
steps in the parent proof any more.

Reading the current source import graph, the following additional library
modules leave this item's import closure (with no claim about other targets):

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients`
- `Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent`
- `WeilConjectures.Mathlib.Algebra.Homology.Bifunctor`
- `WeilConjectures.Mathlib.Algebra.Homology.Monoidal`
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive`

The current-source comparison also removes
`Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits` from this item's closure.
Other Mathlib modules listed in the retained report are now reached through
current dependencies and are not claimed as pruned.

## Where the brief, the DAG or earlier work was wrong

The retained report described two new holes, but the resumed sandbox already
contained proofs under development for both. The coefficient-descent comparison
needed explicit elimination of identity maps introduced by functor associators
before cancellation. The earlier claim of a complete compile did not apply to
these later proof bodies; validation is repeated on the actual delivery.

The original route used localization of the K-flat subcategory. The replacement
uses the declared resolving-class essential-constancy and pointwise-Kan bridge
on the whole homotopy category, preserving the unit's route (sk-rem-rest has no
realized statement or proof steps). The source is Stacks derived.tex,
lemma-find-existence-computes (06XN), lemma-compose-derived-functors-general
(essentially constant limits commute with functors), lemma-derived-shift (05SU),
and sites-cohomology.tex lemma-derived-base-change (06YY).

The generic descent statement accommodates identity/zero coefficient maps,
empty and zero categories, and arbitrary resolving properties. Its proof does
not assume that every complex computes the derived functor. The counit theorem
uses the existing computation theorem for all K-flat complexes; it adds no
termwise flatness hypothesis.

## New nodes

lem-sbc-derived-coefficient-map-descent records the proved generic descent of a
termwise coefficient map through a resolving universal counit. It supplies the
all-complex factorization and shift equation, without asserting roof uniqueness
or triangulatedness. Its proof uses the existing essential-constancy and
pointwise-Kan bridge declarations, plus Mathlib's Kan-extension API.

lem-sbc-scalar-extension-counit-properties records the proved transport from the
existing cochain model to an arbitrary specified universal pair, including its
K-flat computation and triangulated shift. It constructs no coefficient unit.
Both new modules have source citations and complete proof descriptions.
There are no change records because no existing public interface changed.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
