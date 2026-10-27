## What changed

The statement of `native_weil_ringed_presentation` is unchanged. Its proof now
constructs the action-site equivalence from an ordinary Frobenius-compatible
coefficient realization and the existing twisted action-site presentation. The
proof establishes essential surjectivity of fixed-pair transport, additivity,
and transport of the internal-Hom comparison to the inverse equivalence.

`Sheaf.Paper.NativeActionSiteHomComparison` defines the actual functor `toWeil`
by restriction followed by `IsoAlgebra.mapOfNatIso`. It proves that its ordinary
Hom comparisons intertwine the native Weil structure maps and are natural in
both arguments. In particular the source structure map is inverted, as required
for contragredient internal Hom.

`Sheaf.Paper.NativeFrobeniusRingedModel` states the remaining ordinary geometric
comparison. Its fields refer to actual native adic modules and actual native
Frobenius pullback. They include the ordinary Hom isomorphism, its naturality,
and its Frobenius compatibility before any invertible structure maps are
introduced. No definition obtains data from a theorem containing `sorry`.
The sole unfinished existence theorem is used only inside theorem proofs.

The existing node's proof and proof dependencies now describe this route.
No existing public signature, definition, attribute, or public import changes.
No source-library module changes. No consumer adaptations are necessary.

Validation: `lcompile.py --all` accepted all three final modules with exit code
zero and no errors or warnings. Temporary profiler options were removed.

## Proved and sorry left

The original hole in
`AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_ringed_presentation`
is replaced by a complete proof from named dependencies.

The new theorem
`AlgebraicGeometry.ProEtaleWeilSheaf.native_action_site_hom_comparison`
is proved without `sorry`, including its structure-map and naturality equations.
The private fixed-pair equivalence and inverse Hom comparison are also proved.

One new hole remains:
`AlgebraicGeometry.ProEtaleWeilSheaf.native_frobenius_ringed_model`, node
`lem-sf-native-frobenius-ringed-model`. It concerns ordinary modules only; it
neither asserts existence of an equivariant category presentation nor its Hom
comparison. The action-site/fixed-pair argument combining this ordinary datum
with the existing twisted action-site theorem is fully formalized here.

Counts: one original hole closed, one lower hole added, zero holes left in the
item module, one hole across the delivery. This is a decomposition, with net
hole reduction zero, rather than a complete proof of all dependencies.

## No longer needed

No existing public imports are removed. The new ordinary-model module imports
only native adic Hom and the native Weil category, rather than derived Hom.
`DerivedHom` is needed in the new lift module to state the bifunctor comparison.

The removed direct proof dependencies of the item are:

- `def-weil-pbc-internal-abelian-sheaf-module-equivalence`, module
  `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`: the native adic
  section-module equivalence is the appropriate ordinary coefficient model.
- `lem-sf-weil-frobenius-action-resolutions`, module
  `Sheaf.Paper.WeilFrobeniusActionResolutions`: its small-site geometry remains
  a source for the residual ordinary construction, so this module is not
  globally pruned.
- `def-sf-native-weil-closed-models`, module
  `Sheaf.Paper.NativeWeilClosedModels`: this remains a statement dependency and
  public import; its duplicate proof-dependency entry is unnecessary.

No global module withdrawal or global pruning is claimed. The internal-abelian
comparison and action-resolution modules also remain needed by other consumers.

## Where the brief, the DAG or earlier work was wrong

The original step 1 identifies an internal-abelian module model with native
adic sheaves without specifying their comparison. These are different ambient
categories: the native coefficients are sheaves of Weil-coefficient modules,
whereas the action-resolution model uses internal modules in abelian sheaves.
The proved native `adicSectionModuleEquivalence` and ordinary Hom comparison
provide the appropriate sectionwise model, but their compatibility with the
small-site Frobenius translation must still be established.

An additive equivalence by itself need not preserve internal Hom. The ordinary
model therefore explicitly requires Hom comparisons and the ordinary Frobenius
square. These equations are the input used in the proved lift; no Hom assertion
is inferred from additivity alone. The square applies before choosing the two
Weil structure maps, so it is strictly below the equivariant assertion.

The unit record's realized route has no additional mandatory step bypassed by
this proof. Empty geometric fibers and zero modules require no extra hypothesis.

## New nodes

`lem-sf-native-frobenius-ringed-model` records the ordinary small-site native
coefficient realization and its Frobenius-compatible ordinary internal Hom.
Its theorem is the only split-off unfinished statement. Its docstring explains
the site, coefficient ring, section-module equivalence, comparison of pullbacks,
and evaluation calculation. The statement contains no fixed-pair categories or
equivariant internal-Hom assertion.

`lem-sf-native-action-site-hom-comparison` records the proved lift of that
ordinary comparison to invertible structure maps. Its real proof expands the
native Hom action, uses the ordinary Frobenius square, composes source and target
structure maps, and proves two-variable naturality.

There are no change records: only the item module, two new modules, and their
corresponding node files are changed.

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
