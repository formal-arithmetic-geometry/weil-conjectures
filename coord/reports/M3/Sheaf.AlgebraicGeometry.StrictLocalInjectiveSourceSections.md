## What changed

Closed the original hole in `Sheaf.AlgebraicGeometry.StrictLocalInjectiveSourceSections`,
without changing its statement or existing docstring. Its proof constructs
`strictLocalInjectiveSourceIso`, assembles the two compatibility equations, and derives
its conjugated transition formula by cancelling the comparison homomorphism in Lean.

`StrictLocalInjectiveSourceComparison` constructs the comparison entirely: the injective
right-derived direct-image unit, full faithfulness of the bounded-below inclusion,
K-injective localization of Hom, the Hom-complex cohomology isomorphism, free-generator
sections evaluation, and the underived stage-sections isomorphism. All its data and
proofs are complete. In particular, no isomorphism is chosen from an unproved mere
existence theorem. The stage-sections isomorphism uses an explicit identity object,
rather than unfolding the arbitrary terminal object of the site.

The two deferred equations live separately in `StrictLocalInjectiveSourceTransition`
and `StrictLocalInjectiveSourceRestriction`. Each has its own module, node, source,
complete proof in words, and a whole-theorem `sorry`. The parent imports both for its
proof only. Its public import is unchanged. The parent DAG now records this route.
No existing definitions, signatures, universes or visibility were changed; there are
no forced adaptations.

Validation: all four modules compile cleanly through `lcompile.py --all`. The final
required `deliver3.py --no-push` checks compilation, axioms, nodes and delivery shape.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.exists_strictLocalInjectiveSourceSections`
(node `lem-weil-pbc-strict-local-injective-source-sections`), 1 original hole.
There are no remaining sorries in the original module.

Added holes, 2:

- `AlgebraicGeometry.Etale.strictLocalInjectiveSourceIso_transition`
  (node `lem-weil-pbc-strict-local-injective-source-transition`): the uncancelled
  naturality square for the specific constructed source comparison.
- `AlgebraicGeometry.Etale.strictLocalInjectiveSourceIso_restriction`
  (node `lem-weil-pbc-strict-local-injective-source-restriction`): the cone-leg
  equation for that same specific comparison.

This is a decomposition: one upper hole closed, two strictly smaller compatibility
holes added; it is not a complete sorry-free proof of the original mathematical result.
The construction module has no sorry. Its sections naturality theorem
`sourceFreeSectionsEquiv_comp` and every proof inside its definitions are complete.

## No longer needed

No pre-existing import was removed: `EtaleInjectiveSectionsComparison` is required by
the original signature. The construction uses its definitions but does not use its
holed theorem `injectiveSections_strictLocal_comparison`.

The original proof-plan node `lem-weil-pbc-site-restriction-injectives` and module
`Sheaf.Paper.SiteRestrictionInjectives` are unnecessary on this route. The source
comparison computes Hom into `f_*J`, which is injective termwise by exact inverse
image and right adjunction, then evaluates its free generator. It never needs an
injective replacement of the stage restriction. This is pruning below the unit
level; `dag/units/sk-prop-h2.json` has no realization binding this item.
The inverse-image localization comparison remains needed for underived sections,
and the right-derived injective unit and K-injective Hom localization remain needed.
No claim is made that the pruned module is unreachable from every other target route.

Discarded unlanded artifacts of the earlier attempt:
`lem-weil-pbc-strict-local-injective-source-sections-iso-transition`,
`lem-weil-pbc-strict-local-injective-source-sections-restriction`, and their
`strict-local-source-intermediates.md` change record. Neither declaration is imported
or delivered.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt's restriction lemma was false as stated: it allowed an
arbitrary family e of source isomorphisms, without fixing free-generator evaluation.
Even a natural family can be modified by a sign automorphism, changing its restriction
formula while the fixed germ/mate map stays the same. The repaired statement uses
only `strictLocalInjectiveSourceIso`, whose construction fixes that normalization.
The earlier attempt also put the holes in the parent module, lacked the parent DAG
update, provided incomplete new-node proofs, and wrote its own second-reading section.
Those artifacts have been replaced; the second reading is left to the next worker.

Edge-case checks: the comparison is constructed for every integer n, including negative
n and degrees below the injective complex's bound. Its components are all isomorphisms,
so zero complexes yield the unique zero-group comparison. The explicit terminal
identity object and base-change projection work for empty schemes; identity transition
maps are identity chain restrictions. The cone lemma retains the derived-sections unit
at the limit and makes no injectivity or invertibility assumption there. The comparison
uses the supplied q naturally, rather than a separately chosen representative.

Searches: LeanFinder found general sheaf-cohomology and Ext/Hom-complex infrastructure;
Loogle found `CohomologyClass.homAddEquiv`; Mathlib grep found
`CochainComplex.IsKInjective.Qh_map_bijective` and its variants. These are used directly.
LeanSearch returned Internal Server Error and is recorded as unavailable. Repository
search found no existing theorem for the two normalized compatibility equations;
`nonempty_strictLocalMateProjectionData` depends on the original item and cannot be
used without a cycle. Sources read: Stacks Tags 03Q8 and 03Q9 at their official pages.

## New nodes

`def-weil-pbc-strict-local-injective-source-comparison` records the explicit comparison
and its proved auxiliary constructions in `StrictLocalInjectiveSourceComparison`.
It leaves no new hole and chooses no arbitrary object from a holed theorem.

`lem-weil-pbc-strict-local-injective-source-transition` records only the naturality
square, without any existence or cone/mate clause, in `StrictLocalInjectiveSourceTransition`.

`lem-weil-pbc-strict-local-injective-source-restriction` records only the cone-leg
equation for the fixed normalized comparison in `StrictLocalInjectiveSourceRestriction`.
There is no statement correction or change record: the existing interface is unchanged.

## Second reading by M3

1. **Visible changes and statements.** I diffed the delivered item against the repository version. The target theorem signature and existing declarations are unchanged; added declarations are in new modules and recorded by DAG nodes.

2. **Proof and compilation.** I compiled all four delivered modules with `lcompile.py --all`; they compile without errors. The only remaining `sorry`s are the two named compatibility theorems, each public and documented. No definition contains `sorry`, and no forbidden axiom or unsafe declaration was found.

3. **New statements.** The comparison, transition, and restriction nodes are strictly smaller than the parent statement. Their declarations, sources, proof descriptions, and module paths agree, and repository search found no duplicate existing declarations. The compatibility statements concern the explicitly constructed `strictLocalInjectiveSourceIso`, rather than arbitrary isomorphism families.

4. **Pruning and route.** The parent proof uses exactly the comparison plus the two compatibility nodes. Its updated `proof_deps` matches those uses, and removed old dependencies are listed above. The unit record has no realized step for this item, so the route does not bypass a realized unit step.

5. **DAG agreement.** The parent node proof and origin describe the actual Lean route; each new node has the required statement, source, proof, dependency, Lean, and creation fields. No statement or definition change record is needed.

I changed only this second-reading report section after reviewing the worker delivery; the Lean modules and DAG records otherwise pass the checks above.
