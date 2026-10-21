## What changed

Prove `CategoryTheory.element_restriction_hom` without changing its statement.
Private helpers construct the natural sheaf-Hom and Hom-complex comparisons,
descend them through K-injective resolutions, identify iterated element sites,
and compare the ordinary slice site with the element site of its sheafified
representable. The latter comparison uses the canonical dense-subsite functor,
so no subcanonicity or pullback hypothesis is introduced.

The proof uses the existing ringed-equivalence module comparison to transport
module categories along equivalences of sheaf categories. All added imports
are private proof imports. No existing definition or public signature changes.
The added private instances and local attribute command are documented in
`coord/changes/element-restriction-hom-private-helpers.md`, as preflight requires.
The node's proof and dependency records follow this argument.

## Proved and sorry left

Closed: `CategoryTheory.element_restriction_hom` (one original hole).
Holes added: zero. Holes left in the delivered module: zero.
No statement is split off. The proof uses the existing declaration
`CategoryTheory.ringed_equivalence_module_hom`; its separately tracked proof
obligation is not changed by this delivery.

## No longer needed

The direct import of `WeilConjectures.Algebra.Homology.HomComplex` is replaced
by its product-projection API in
`WeilConjectures.Algebra.Homology.HomComplexProjections`. The redundant direct
import of `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom` is
also removed; it is publicly imported by that Hom-complex API.

The proof does not use
`lem-weil-pbc-localized-sheaves-over-representable` or
`exists_localizedSheavesOverRepresentable_general`: the canonical functor from
`C/U` to the element category is proved dense using local surjectivity and
local injectivity of the sheafification unit. No module is withdrawn, and no
adopted source declaration is removed.

`lem-weil-pbc-ringed-sheaf-slice-adjunction` is used through the existing
`RingedPresentationData` API rather than by destructuring its comparison
record; it remains a dependency of that API and is not claimed as pruned.

## Where the brief, the DAG or earlier work was wrong

The old plan described the final equivalence by transporting operations through
the localized fibre equivalence. The canonical dense-subsite construction gives
the same required comparison and lets the already stated ringed-equivalence
module theorem supply the module and derived-Hom transport. The node records
this route and its added dependencies. The original statement is unchanged.

## Second reading by V7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
