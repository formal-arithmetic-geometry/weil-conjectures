## What changed

Completed `AlgebraicGeometry.ProEtale.supported_cohomology_hom` without changing its
signature. Added the proved underived identification
`AlgebraicGeometry.ProEtale.supported_sections_hom` in
`Sheaf.Paper.SupportedSectionsHom`. Its proof transports the existing intrinsic
constant-coefficient cokernel presentation to fixed-scalar sheaves, identifies the
constant and open Hom groups by adjunction and evaluation at 1, and uses the
cokernel universal property to identify the support kernel. Naturality is proved
by composing with the monic kernel inclusion.

The derived proof uses exact scalar forgetting, uniqueness of right derived
functors, and the existing natural RHom roof comparison. The private helper
`exactPostcompositionDerivedIso` supplies the exact-postcomposition comparison
without requiring the support functor to preserve injectives. The DAG records
this route. Public imports and all existing declaration signatures are preserved.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.supported_cohomology_hom`
(node `lem-pur-supported-hom`). The new theorem
`AlgebraicGeometry.ProEtale.supported_sections_hom`
(node `lem-pur-supported-sections-hom`) is also proved. All private helpers are
proved. No holes added, no holes split off, and no `sorry` remains in either
delivered Lean module. Existing imported theorems retain their own proof
obligations; none is duplicated or weakened in this delivery.

## No longer needed

The original geometric calculation of locally constant sections, local
surjectivity and extension-presheaf cokernels is supplied by the existing
`lem-pur-proetale-supported-constant-presentation`. The underived calculation
uses the constant-sheaf adjunction directly rather than a second free-Yoneda
presheaf construction. Enough injectives is the existing Grothendieck-abelian
instance for fixed-scalar sheaves, so there is no need to construct a second
termwise K-injective resolution here.

Removed direct proof imports:

- `Sheaf.AlgebraicGeometry.AbelianEtaleProEtaleCohomologyComparison`
- `Sheaf.Paper.ComparisonPullbackExact`
- `Mathlib.CategoryTheory.Sites.PreservesSheafification`
- `Sheaf.Paper.ConstantSheafSectionsLocallyConstant`
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Mathlib.CategoryTheory.Sites.EpiMono`
- `Mathlib.AlgebraicGeometry.AffineScheme`
- `Sheaf.CategoryTheory.LocalizedModuleExactIndependent`
- `Sheaf.CategoryTheory.ExtensionByZeroPresheaf`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`
- `Mathlib.Algebra.Category.ModuleCat.Ulift`
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective`
- `Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
- `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`

Pruned direct proof dependencies of `lem-pur-supported-hom`:

- `lem-cbc-abelian-etale-proetale-cohomology-comparison`
- `lem-sf-comparison-pullback-exact`
- `lem-weil-pbc-ring-sheafification-underlying-sets`
- `lem-weil-pbc-constant-sheaf-sections-locally-constant`
- `lem-weil-proetale-weakly-etale-localization`
- `def-weil-proetale-module-direct-image`
- `def-weil-pbc-proetale-site`
- `lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective`
- `lem-weil-pbc-affine-scheme-qcqs`
- `lem-pur-site-restriction-module-adjunction-exact`
- `def-weil-extension-by-zero-presheaf`
- `def-weil-presheaf-modules-sheafification`
- `def-weil-sheaf-of-modules-category`
- `prop-pur-kinjective-resolutions-exist`
- `lem-pur-kinjective-degreewise-existence`
- `lem-weil-pbc-closed-immersion-base-change`
- `lem-weil-pbc-free-yoneda-presheaf-module`

These are no longer direct prerequisites of this module. Some remain transitive
requirements of the reused constant-presentation theorem or of existing category
instances. This report does not claim that they are globally unreachable.
The blueprint unit's statement and steps are retained.

## Where the brief, the DAG or earlier work was wrong

The interrupted sandbox had no report, and its two principal theorems still
contained `sorry`. The preserved helper construction had several coercion and
naturality errors, repaired in this session. The shared library now provides
the needed constant-coefficient cokernel presentation, making the original
geometric proof-dependency list longer than necessary. No mathematical statement
was found false and no target or definition was changed.

The first required dry run reported `report.md is missing`. Compilation is
performed only by the authorized remote `lcompile.py` interface. Its occasional
busy-server responses were retried without changing the tools or time limits.

On resuming after the provider interruption, the underived module compiled, but
the derived comparison exposed unresolved universe constraints. The private
`exactPostcompositionDerivedIso` now explicitly names its object, morphism and
derived-category universes. The proof also supplies Mathlib's scalar-forgetting
colimit instance at the concrete coefficient universe. The main module compiles
without warnings; no public signature changed.

The resumed dry run compiled the files but rejected the missing LeanSearch
record and the added global `open CategoryTheory.Functor` command. Ran and
recorded LeanSearch, restored the original global `open`, and narrowed the
underived proof import from the full pro-etale comparison module to the
constant-sheaf pullback API. The new module docstring names its blueprint node.

The next resumed dry run found four remaining unqualified whiskering calls after
that namespace cleanup. Qualified each as `Functor.isoWhiskerLeft` or
`Functor.isoWhiskerRight`; no global namespace opening or interface change is needed.
Preflight also detected the helper's added file-level universe names as an interface
command change. Bound those names explicitly on the private definition itself,
restoring the original `universe u` command and avoiding any interface change.

## New nodes

`lem-pur-supported-sections-hom` records the underived natural Hom identification
from Milne, Section 9, proof of Theorem 9.4, and the original node's steps 1–4.
Its Lean theorem is fully proved, not a new proof obligation. Empty support,
full support, empty schemes, and the zero ring are covered by the same cokernel
and kernel universal properties. The blueprint search found no separate node
for this underived assertion. No change record is required: there are no changes
to existing statements, definitions, or public visibility.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
