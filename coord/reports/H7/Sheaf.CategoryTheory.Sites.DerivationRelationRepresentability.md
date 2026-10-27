## What changed

Filled `CategoryTheory.SheafDerivationRelations.relation_cokernel_represents` in
`Sheaf.CategoryTheory.Sites.DerivationRelationRepresentability` following the existing
seven-step proof of Stacks 04BL and 04BN. Private, proved helpers give extensionality
on free generators, construct the three natural assignments and their unique linear
relation map, build the derivation induced by a map killing the relations, and show
that every derivation extends to a map killing them. The cokernel property then gives
the stated equivalence, inverse formula, both naturality identities, the unique
normalized comparison isomorphism and its transported cokernel property.

The existing statement, definitions, public imports and proof dependencies are retained.
No other existing module is changed. The item's node records the concrete free-module and cokernel APIs used in its
existing seven steps; its proof dependencies and unit route are unchanged.

Searches through leanfinder, loogle, the Mathlib sources and both library roots found
presheaf differential universal properties and the general cokernel API, but no theorem
for this specific sheafified relation presentation. Used the already proved
`SheafFreeModule.freeModule_restrict_bijective` and
`SheafFreeModule.freeModule_extend_inverse`, and Mathlib's
`CokernelCofork.IsColimit.desc'`, `Cofork.IsColimit.hom_ext` and
`CokernelCofork.IsColimit.ofπ`.

## Proved and sorry left

Closed one of one original holes:
`CategoryTheory.SheafDerivationRelations.relation_cokernel_represents`
(node `lem-trf-sheaf-derivation-relation-representability`).
No holes remain and no holes are added or split off. All added private helpers are proved.

Validation: the remote single-file compiler passed with no warnings in 47.0 seconds.
`#print axioms relation_cokernel_represents` lists exactly `propext`,
`Classical.choice` and `Quot.sound`. The original theorem signature and all original
definitions were also compared verbatim with the repository source.

## No longer needed

None. No imports, declared proof dependencies, nodes or modules are pruned.
The free-module universal property and the module-sheaf category are both used.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The supplied plan applies as stated, including
its distinction between free-sheaf generator extensionality and global generation of
sections. The unit route is preserved.

## Second reading by H7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
