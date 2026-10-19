## What changed

Retained the earlier exactness proof and completed three strictly smaller construction
lemmas in separate modules: exact scalar extension, ordinary comparisons and the
derived mate. The item now constructs the
actual exact derived restriction functors, descends the inverse comparison through
localization, forms the direct comparison as a mate, and proves the adjunct equation
from the general mate-unit identity. The original theorem signature is unchanged.

## Proved and sorry left

Closed the original hole in
`CategoryTheory.FlatRingedDiagramInput.flatRingedDiagramRestriction`.
All four delivered modules contain zero `sorry`s; no holes are added or split off.
The three new, proved construction theorems are:

- `SheafOfModules.flatRestriction_exact_leftAdjoint`
  (`lem-weil-pbc-flat-restriction-exact-left-adjoint`): explicit sheafification of
  sectionwise scalar extension, its tensor adjunction, and finite-limit preservation
  by comparison with the flat tensor functor.
- `CategoryTheory.FlatRingedDiagramInput.flatRestriction_ordinary_comparisons`
  (`lem-weil-pbc-flat-restriction-ordinary-comparisons`): linear inverse comparison
  from the operation equations; direct comparison from its mate and the counit.
- `CategoryTheory.FlatRingedDiagramInput.flatRestriction_derived_mate`
  (`lem-weil-pbc-flat-restriction-derived-mate`): normalization directly from the
  supplied transpose formulas and ordinary counit; invertibility on K-injectives,
  then on all objects using resolutions and localization.

The main proof constructs actual exact derived restrictions and their inverse
comparison by localization, packages the derived mate, and proves the adjunct
identity. The discarded earlier helper was never delivered and is not counted as
an additional library hole closed. Data constructions use tensor universal properties,
proved linear maps, and canonical localization, not arbitrary unproved witnesses.

## No longer needed

Removed these proof-only imports from the item:

- `Sheaf.CategoryTheory.DiagramSiteRealization`
- `Mathlib.Algebra.Category.Grp.FilteredColimits`
- `Mathlib.CategoryTheory.Abelian.FunctorCategory`
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`
- `Sheaf.CategoryTheory.GeometricModuleTransport`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantInd`
- `Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantPro`
- `Mathlib.RingTheory.TensorProduct.Basic`
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
- `Sheaf.CategoryTheory.RingedSiteModules`

Also removed the unused direct sheafification import from the ordinary-comparison
helper; its interface already imports module sheafification through module abelianness.

The tensor, scalar-Hom and module-sheafification nodes are used by the now-proved
scalar-extension construction. K-injective resolutions remain needed, now supplied
directly by the source library
for the Grothendieck abelian category of small module diagrams. Diagram-site
realization, K-injective Hom-comparison, and fraction-normalization constructions
are unnecessary for this proof. The direct proof uses neither geometric
module transport's existential construction nor the KInjectiveTotalDerived and
ExactFunctorDerivedFunctor existence theorems: derived functors are supplied by the
original hypotheses, while restriction uses Mathlib's canonical exact localization.
Their modules are not asserted to be globally unreachable. No unit-level route changes.
The revised proof does not use these former proof dependencies:

- `lem-weil-pbc-diagram-site-realization`
- `lem-weil-pbc-geometric-module-transport`
- `lem-weil-pbc-kinjective-total-derived`
- `lem-weil-pbc-exact-functor-derived-functor`
- `def-pc-essentially-constant-ind-diagram`
- `def-pc-essentially-constant-pro-diagram`
- `lem-weil-pbc-kinjective-hom-derived`
- `lem-pc-pre-derived-adjoint-functors-general`

Removed obsolete tool approvals `lem-weil-pbc-kinjective-hom-derived` and
`lem-pc-pre-derived-adjoint-functors-general` from the item's top-level `tool_uses`:
the counit and mate identities replace their fraction-Hom argument.

## Where the brief, the DAG or earlier work was wrong

The retained report described two unfinished split-offs although the current Lean
files already contained proofs. The ordinary helper had elaboration errors in component transport,
scoped-option placement, counit rewrites and an underspecified isomorphism instance. These were
repaired against current sources. Profiling also found expensive rewriting through
restriction-of-scalars presentations. A generic naturality-pasting identity and
explicit congruence calculations now replace those searches. The ordinary helper
compiles cleanly in 33.6 seconds, within the unchanged 60-second limit.

The full fraction-normalized Hom argument is unnecessary: the supplied transpose
formulas already determine the derived normalization by testing the ordinary counit.
The direct comparison can be constructed as the mate of the inverse comparison,
both before and after deriving. Its normalization proves invertibility on
K-injectives, and source-library resolutions extend it to every derived object.
No unit-level route or existing statement or definition changes.

The resumed preflight flagged the item's additional module-wide namespace openings
as an interface change. Scoped those openings to the private helpers that need
them. The static comparison now reports no interface changes, no public-import
changes, and no existing signature changes. The downstream source scan found no
other module mentioning the theorem by name; no consumer adaptation is needed.

## New nodes

`lem-weil-pbc-flat-restriction-exact-left-adjoint`: proved single-site exact
scalar-extension adjunction, used twice and then whiskered to diagrams.

`lem-weil-pbc-flat-restriction-ordinary-comparisons`: proved ordinary inverse
comparison and its direct mate, with their underlying-sheaf normalizations.

`lem-weil-pbc-flat-restriction-derived-mate`: proved invertibility and right-derived
unit normalization of the specified mate, using the already constructed restriction
factors and inverse comparison. All new nodes have zero remaining holes.


Current-source verification: the original theorem signature and public imports
are unchanged; every delivered module has zero holes, satisfies the line-length
limit, and has proof dependencies equal to the union of its recorded proof steps.
The required initial dry run compiled all four modules and reported four
`letI` style warnings in the main proof. Replaced those proof-local declarations
with `let` and reran the required dry run. No launcher scripts or limits changed.

The updated dry run passed with no compilation warnings (commit 2784ecf0a6),
review class CODEX for the three new proved modules and node updates. The tool
reported that optional axiom probes for the scalar-extension and main modules
received no answer from the compile service within 198 seconds; it explicitly
defers those probes to the merge. Ordinary compilation and server preflight passed.

Resumed verification after the interrupted provider call: the required dry run
passed again at 5361c577c5 with all four modules compiling without warnings and
server preflight passing. Its optional axiom probe for the ordinary-comparison
module received no answer from the compile service within 191 seconds; the tool
defers that probe to the merge. The retained theorem statement and public imports
remain unchanged, and the delivered sources contain zero holes.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
