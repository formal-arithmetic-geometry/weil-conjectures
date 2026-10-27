## What changed

Filled `AlgebraicGeometry.Scheme.Hom.exists_affineChart_stalk_differentials` without changing its statement, definitions, universes or public imports. The proof chooses affine neighbourhoods, constructs the canonical ring-localization equivalences, verifies their square on coordinate sections using localization uniqueness, and transports flatness through those ring equivalences.

For differentials, the proof imports the existing affine-section comparison and affine quasi-coherent germ-localization theorem. Their composite is a localization of the coordinate differential module; its inverse gives the required additive equivalence and the formula on germs of `da`. Scalar extension along the localized stalk ring proves the specified semilinearity. A proved private helper transports finite spanning families in both directions, including rank zero. All new imports are private proof imports. The affine-section and affine germ theorems are used as generic tools: neither changes the geometric route of this unit. The DAG proof and dependency list now record this route. The exact original theorem signature and the 100-column limit were checked against the shared source. All three added source-module imports passed `import_direction.py may`. No source-library file is edited and no new node is introduced.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.Scheme.Hom.exists_affineChart_stalk_differentials` (node `lem-trf-affine-chart-stalk-differentials`). The private helper `spanning_family_transport` is also fully proved. There are zero `sorry` declarations left in this module and zero holes added or split off. The existing dependency proofs are used as published; this report does not claim to close any holes inside them.

## No longer needed

Removed the direct proof imports `Mathlib.AlgebraicGeometry.OpenImmersion` and `Mathlib.AlgebraicGeometry.Modules.Tilde`: the proof uses the higher-level affine module germ API instead of manipulating open-immersion or tilde stalk comparisons itself. Existing public imports remain unchanged.

Removed the direct proof dependency `lem-weil-pbc-spec-map-stalk-localization`: equality of ring maps follows by localization uniqueness and the germ equations. Replaced the direct proof dependency `lem-weil-pbc-spec-tilde-stalk-localization` with the existing `lem-sbc-affine-module-germ-localization` and `lem-sc-relative-differentials-affine-sections`, which give exactly the normalized module localization needed. The tilde-stalk lemma remains used within the underlying affine theory; no claim of global withdrawal or deletion is made. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The statement and four mathematical steps are sound. The source library already exposes the affine differential-section comparison and a general quasi-coherent affine germ localization result, so the explicit restriction-to-Spec stalk transport in old step 3 is unnecessary. Old step 2 can also use localization uniqueness directly. These are shorter implementations of the same affine argument, not changes to the unit route. Sources checked: Stacks `morphisms.tex`, `lemma-differentials-restrict-open` (01US) and `lemma-differentials-affine` (01UT); `schemes.tex`, `lemma-spec-sheaves` (01HV), clauses 6 and 7. No new statement or definition requires an edge-case repair.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
