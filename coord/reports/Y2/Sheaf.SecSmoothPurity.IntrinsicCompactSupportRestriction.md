## What changed

Prove `AlgebraicGeometry.ProEtale.intrinsicCompactSupportRestriction_comp` in its
existing intrinsic constant-ring coordinates. Keep the public definition and both
public signatures unchanged. The private helpers identify ordinary maps on sections,
apply the proved `FiniteFreeDirectImage.rightTower` unit-normalization calculation,
invert the result, and combine it with `sfOpenRestriction_derived_comp` by naturality.
The two `import all` proof imports reuse proved private calculations; no public import
is changed. The node copy records this route. The elaboration settings and consumer check are
recorded in `coord/changes/Y2-intrinsic-compact-restriction-proof-context.md`.

Validation: the final module, after pruning redundant imports, compiles cleanly
through `lcompile.py` in 28.4 seconds (exit 0, no warnings). The public definition
and theorem signature were checked verbatim against the original. The delivery
contains zero `sorry` tokens and no new nodes. `deliver3.py` runs the final probe
and preflight checks before pushing.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.ProEtale.intrinsicCompactSupportRestriction_comp`
(node `lem-sf-compact-support-restriction-of-scalars`). The original module has one hole.
No holes added or split off. All new helpers are private, complete proofs or explicit
abbreviations of existing constructions. No `sorry` remains in the item source.

## No longer needed

The fixed-module direct-image cocycle
`lem-sf-direct-image-scalar-restriction-cocycle` is not used: the definition in this
item uses the intrinsic ring-sheaf comparison. The already proved generic `rightTower`
calculation applies directly to that comparison's published unit normalization,
without transporting through a coefficient-realization equivalence. This avoids
assuming that the fixed-module and intrinsic derived direct images are definitionally
equal. The original direct-image restriction dependency remains a statement dependency;
its fixed-module computation is not needed by this proof.

Removed original proof imports: `Sheaf.CategoryTheory.KInjectiveDerivedMapComputation`,
`Sheaf.CategoryTheory.NormalizedDerivedComparisonCommonResolution`,
`Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`, and
`Sheaf.CategoryTheory.RingedSiteModules`. Their resolution calculations are not used.
Also removed redundant private imports
`Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`,
`Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`,
`Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact` (already provided by the
public statement dependencies), and unused
`Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage`.
The obsolete proof `tool_uses` entry for
`lem-weil-proetale-direct-image-restriction-of-scalars` is removed from the node.
No module or declaration is withdrawn; no unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The proposed direct-image cocycle has been formalized in the equivalent fixed-module
presentation. It cannot be substituted definitionally for the intrinsic comparison
specified in this item. The library already contains the needed ring-sheaf calculation
as a proved generic private helper in `FiniteFreeDirectImageBalancingCoherence`.
Its `rightTower` theorem has no finite-free or scalar-model hypotheses. We reuse it
without changing that module or its public interface. The ordinary normalization
proves the cocycle also for identity maps, zero rings, empty schemes and nonflat
coefficient maps; no preservation of K-injectives by restriction is assumed.

Shortest-route searches: `msearch.py` LeanFinder for natural-isomorphism composite
cocycles returned unrelated cohomology/shift results and `CatCommSq.vComp_iso_hom_app`;
Loogle for `mapDerivedCategorySquareIso` returned no hits; the search service grep for
`rightTower|derived_comp_ext|mapDerivedCategorySquareIso_comp` returned no hits.
Repository `rg` found the proved open cocycle and the existing generic `rightTower`
helper, whose complete signature and proof were read before reuse. Sources read:
Stacks `sites-modules.tex`, `lemma-extension-by-zero` (03DI);
`sites-cohomology.tex`, `lemma-derived-pushforward-composition` (0D6E);
`derived.tex`, `lemma-K-injective-defined` (070Y).

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
