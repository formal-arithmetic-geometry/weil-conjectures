## What changed

Proved `DerivedCategory.module_localization_tower_vanishing_iff` with its signature,
universes, visibility, and public imports unchanged. The only Lean file delivered is
`lean/Sheaf/RingTheory/ModuleLocalizationTowerVanishing.lean`.

The proof follows the free two-term telescope resolution in Stacks Tag 091P directly,
rather than specializing the ringed-site internal-Hom criterion. Private, completely
proved helpers construct the finitely supported free module, its injective telescope
map, its cokernel universal property, and the resulting distinguished triangle.
Coproduct and product universal properties identify the two Hom endomorphisms with
`(x_n) ↦ (x_n - f*x_(n+1))`. Shifted triangle exactness and detection of isomorphisms
by shifts of the projective module `ULift A` finish the comparison with the given
Roos triangle. The proof treats arbitrary unbounded complexes and arbitrary `f`.

The only added Sheaf proof dependency is
`Sheaf.RingTheory.ModuleLocalizationFilteredColimit`, using
`ModuleCat.localization_away_colimit` to identify the telescope cokernel. This is a
generic algebraic tool from `lem-sc-module-localization-filtered-colimit` (unit
`sk-thm-picard-duality`), not a replacement for any unit statement or realized proof
step. Its formula on every colimit coprojection uniquely determines its linear
isomorphism, so this is not arbitrary data chosen from mere existence. No new
maintainer `tool_uses` approval was added; this use is explicitly submitted for review.

The proved source-library APIs used are
`DerivedCategory.isColimitCofanMkQObj`,
`DerivedCategory.singleFunctorZeroHomEquiv`, and the Grothendieck-category
K-injective-resolution instance. Ordinary proof imports add the necessary module,
short-exact-sequence, and localized-module APIs. The existing node's `proof`,
`proof_deps`, and `proof_origin` now describe this direct route. Its obsolete
top-level `tool_uses` entries were removed. The unit route is unchanged.

Validation: the final module compiled through `lcompile.py` in 6.6 seconds with
exit code 0 and no diagnostics. A literal comparison confirms the original
theorem signature and all public imports are unchanged; no line exceeds 100
characters.

## Proved and sorry left

Closed 1 of the item's 1 holes:
`DerivedCategory.module_localization_tower_vanishing_iff`
(node `lem-weil-pbc-module-localization-tower-vanishing`).
There are zero `sorry`s left in the delivered Lean file and zero holes added
anywhere. No split-offs and no new modules. Every private helper is proved;
there are no hollow definitions or additional axioms.

The already stated `ModuleCat.localization_away_colimit`
(node `lem-sc-module-localization-filtered-colimit`) remains an existing imported
obligation, not a hole added or closed by this delivery. Thus the theorem is proved
from that existing declaration, as stage 3 permits, and this report does not claim
its whole transitive axiom closure is complete.

## No longer needed

Removed these proof imports and the corresponding proof dependencies:

- `Sheaf.Algebra.Homology.DerivedInternalHom`:
  `def-pur-derived-internal-hom`.
- `Sheaf.Algebra.Homology.HomComplex`: `def-pur-hom-complex`.
- `Sheaf.CategoryTheory.RingedSiteModules`:
  `def-weil-sheaf-of-modules-category`.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`:
  `prop-pur-kinjective-resolutions-exist`.
- `Sheaf.Paper.LocalHomTowerCriterion`:
  `lem-weil-pbc-local-hom-tower-criterion`.

The direct telescope argument uses none of these ringed-site/internal-Hom results.
The obsolete top-level `tool_uses` approvals removed are
`def-weil-sheaf-of-modules-category`, `prop-pur-kinjective-resolutions-exist`,
`def-pur-hom-complex`, and `def-pur-derived-internal-hom`.

Also removed redundant direct imports
`Mathlib.Algebra.Homology.DerivedCategory.KInjective` and
`WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`.
The first remains used transitively by the proved derived-coproduct API, and its
Mathlib leaf `lem-weil-pbc-kinjective-hom-derived` stays in the node's dependencies.
The second is already provided by the unchanged public Sheaf derived-limit wrapper;
`def-weil-derived-limit` stays needed. `def-weil-abstract-derived-category` stays needed.
No module is withdrawn: whether the removed dependencies remain target-reachable
through other parents is left to the maintainer's closure calculation.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable definition was found. The previous DAG plan's
one-object-site equivalence and internal-Hom comparison are unnecessary for this
module. The cited source itself provides the shorter free-telescope proof; its
missing colimit identification is already stated as
`ModuleCat.localization_away_colimit`. No definition, public statement, target, or
consumer was changed, so no change record or forced adaptation is needed.

Edge cases: injectivity of the telescope map is proved by induction starting at
coordinate zero and never cancels `f`; this covers zero divisors, `f=0`, and the
zero ring. For a unit the localization is the original ring and the same argument
applies. Both triangle comparisons quantify over every integer shift, so no
boundedness is introduced. `ULift` and the transported Grothendieck instance keep
`u`, `v`, and the derived-category universe `w` independent as in the original.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
