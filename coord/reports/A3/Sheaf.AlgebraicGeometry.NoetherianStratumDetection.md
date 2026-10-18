## What changed

Proved all three holes in `Sheaf.AlgebraicGeometry.NoetherianStratumDetection` without changing
any existing signature, public definition, public import, or visibility. Added only proved
private helpers. They present the actual noncommutative ring adjunction unit on the small
model and identify module inverse image with abelian inverse image. Exactness transfers
through the faithful conservative forgetful functor.

For sheaf detection, composite pullback is compared with successive pullbacks. Existing
pro-etale cover conservativity removes the chosen covers, with their arbitrary index universe
`w` preserved. The proved private `AlgebraicGeometry.ProEtale.abDetectMaps` declaration in
`ProEtaleAbelianClosedSupport` applies directly to the finite jointly surjective family of
quasi-compact stratum immersions. It is accessed by a proof-only `import all`.

For derived detection, exact pullback commutes with homology, so abelian detection applies
in every degree after forgetting module actions. A distinguished cone and Mathlib's zero-cone
criterion then detect isomorphisms. The existing theorem docstrings retain the original proof
plan; the updated DAG and the Lean proof record the shorter finite-family argument.

Checked the full module with `lcompile.py`; the compiler accepted all three proofs. Final
validation also checks the pruned imports and runs the delivery tool's declaration/axiom probe.

## Proved and sorry left

Closed 3 of 3 original holes, by declaration name:

- `AlgebraicGeometry.Scheme.proEtaleRingModuleInverseImage_exact`.
- `AlgebraicGeometry.Scheme.proEtale_isZero_of_stratum_cover`.
- `AlgebraicGeometry.Scheme.proEtale_derived_stratum_cover_detection`.

All three realize `lem-weil-pbc-noetherian-stratum-detection`. No sorry remains in the item.
Added 0 holes and split off 0 statements. Imported declarations may have their own recorded
proof obligations; none is copied or restated here.

## No longer needed

Removed these original proof-only imports:

- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`: available through the exact-functor
  homology API.
- `Sheaf.CategoryTheory.SitePullbackAbelianExact`: Mathlib's representably flat pullback,
  adjunction and exact module-forgetting APIs suffice.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`: the existing cover-conservativity
  theorem and `upperStarIsoLocalizationRestriction` supply precisely the needed restriction API.
- `WeilConjectures.ConstructibleSheaf.Pullback`: no base-changed stratification is constructed.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: already available through the public
  inverse-image definitions; no additional proof declaration from this module is used.
- `Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection`: finite quasi-compact detection applies
  directly, so neither the module open/closed theorem nor its ringed localization sequence is used.
- `Sheaf.CategoryTheory.RingedSiteModules`: redundant with the unchanged public imports.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: redundant with `ProEtaleRingInverseImage`.

The item's proof no longer needs these original proof dependencies:

- `def-weil-closed-immersion` and `lem-weil-pbc-noetherian-open-subscheme-noetherian`: no
  immersion factorization into closed/open pieces or inductive complementary open is needed.
- `lemma-constructible-pullback-stratification`: no pullback stratification or stratum deletion.
- `lem-exc-open-closed-detection`: replaced by the existing generic finite-family detection
  declaration, applied to the stratum immersions themselves.
- `lem-weil-proetale-weakly-etale-localization`: the cover restriction identification is already
  provided by the source library's localization API.
- `lem-weil-pbc-site-pullback-abelian-exact`: direct existing exactness instances suffice.
- `lem-sf-derived-homology-long-exact` and `lem-weil-pbc-hom-into-triangle-exact`: the existing
  derived homology comparison and zero-cone criterion package these categorical arguments.

Removed the obsolete top-level `tool_uses` entries for `lem-exc-open-closed-detection`,
`lem-weil-pbc-site-pullback-abelian-exact`, `lem-weil-proetale-weakly-etale-localization`, and
`lemma-constructible-pullback-stratification`. The new derived homology comparison is an
already proved source-library tool, not a replacement of a unit-level proper base-change step.
No claim is made that a dependency is globally unreachable when other modules still import it.

## Where the brief, the DAG or earlier work was wrong

No assigned statement was changed or found false. The DAG's finite-stratum induction is a
valid longer plan, but an existing proved finite quasi-compact-family detection declaration
already covers the stratum step. Every stratum domain has Noetherian underlying space via
its actual immersion embedding, so the required quasi-compactness follows without assuming
reduced strata or quasi-separatedness separately. Empty schemes, zero rings, empty strata,
arbitrary chosen-cover index universes and unbounded derived objects are covered by the same
proofs. The unit's realized statement and steps are unchanged. No new nodes or public interface
changes were needed.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
