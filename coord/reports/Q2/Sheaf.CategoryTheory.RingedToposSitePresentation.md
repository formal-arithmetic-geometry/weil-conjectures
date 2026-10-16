## What changed

Proved the body of `CategoryTheory.ringedTopos_sitePresentation` with its original signature
and visibility unchanged. The proof constructs compatible small finite-limit generator
categories, their epimorphic precoverages and comparison equivalences, proves cover
preservation and the direct-image comparison from the original adjunction, conjugates
that adjunction, and applies the remaining fixed-square ring/module transport theorem.

The three new completed helper declarations are in `ToposCompatibleGenerators`,
`SiteOfSheafGenerators`, and `ToposSitePresentation`. The only unresolved helper is in
`RingedToposSquareTransport`. All four have corresponding new nodes.

Second reading corrected proof-only public imports in the generator module, removed
redundant helper imports, added the missing module header/documentation to
`ToposSitePresentation`, and removed the item's unused public cohomology import. The
last removal has the change record
`coord/changes/ringed-topos-site-presentation-cohomology-import.md`. The sole direct
importer also imports cohomology explicitly and imports this item privately; its
scratch copy compiled cleanly against this delivery, without adapting or delivering it.

## Proved and sorry left

Original hole closed: `CategoryTheory.ringedTopos_sitePresentation`, node
`lem-weil-pbc-ringed-topos-site-presentation` (1 of 1 original holes).

New completed declarations: `CategoryTheory.topos_compatibleGenerators`,
`CategoryTheory.siteOfSheafGenerators`, and `CategoryTheory.topos_sitePresentation`.

Hole added and left: `CategoryTheory.ringedTopos_squareTransport`, node
`lem-weil-pbc-ringed-topos-square-transport`, in
`lean/Sheaf/CategoryTheory/RingedToposSquareTransport.lean`. Its entire proof is
`by sorry`; there are no other direct holes and none inside a definition. Its expanded
docstring constructs the ring operations, the lifted structural map and all induced
module actions, and explains the final equality and module_linear calculation.

This is a decomposition: one original hole is replaced by one strictly smaller fixed-square
transport hole, so the direct hole-count net is zero. The site construction and its
continuity/direct-image comparison are complete reductions, not assumptions repackaged
as a restatement. No ledger-based whole-library progress figure is claimed.

Explicit `#print axioms` checks show that the three new completed helpers use only
`propext`, `Classical.choice`, and `Quot.sound`. The item and the unresolved transport
theorem additionally use `sorryAx`, solely for that named transport obligation.

## No longer needed

Removed item imports: `Mathlib.CategoryTheory.Sites.Sheafification`,
`Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`,
`Sheaf.CategoryTheory.SiteInverseImageTensor`,
`Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects`,
`Sheaf.CategoryTheory.SheafSubcategoryComparison`, and
`Sheaf.CategoryTheory.SiteCoveringAxioms`.

`Sheaf.CategoryTheory.SiteInverseImageTensor` is absent from the new item import closure.
The algebraic-objects, comparison, and site-covering modules remain needed transitively;
the removal of their direct imports is not whole-library pruning. Mathlib sheafification
is likewise still used for the generator construction.

For completeness, all ten old direct `proof_deps` are replaced by the new site-presentation
and fixed-square nodes:

- `lem-weil-pbc-site-sheaf-sets-limits-sectionwise`
- `def-weil-pbc-sheafification`
- `lem-weil-pbc-sheaf-subcategory-comparison`
- `lem-weil-pbc-site-sheaf-sets-epi-kernel-pair-coequalizer`
- `lem-weil-pbc-presheaf-colimits-sectionwise`
- `def-weil-pbc-sites-and-cohomology`
- `lem-weil-pbc-left-exact-site-inverse-image-tensor`
- `lem-galois-yoneda-hom-bijection`
- `lem-weil-pbc-sheaf-algebraic-structures-objects`
- `lem-weil-pbc-left-adjoint-preserves-colimits`

Of these, sectionwise sheaf limits, sheafification, subcategory comparison, site-covering
notions and algebraic objects remain used in the helper construction or its signatures.
Kernel-pair coequalizers, presheaf colimits, the left-adjoint-colimit theorem, the site
tensor/inverse-image theorem, and `yonedaEquiv` are unnecessary for this argument. The
new nerve comparison uses the given adjunction's Hom equivalence directly; the earlier
report incorrectly claimed that the tensor and Yoneda steps survived in that helper.

## Where the brief, the DAG or earlier work was wrong

The old continuity route expanded coproducts, kernel pairs, and presheaf colimits.
Joint cancellation transferred through the adjunction proves cover preservation directly.
The existing comparison API then identifies the two nerves without a separate Yoneda or
site inverse-image construction. The first worker's new helper node proof records did
not describe this actual argument; second reading corrected them.

The four helper nodes reused the same irrelevant generator searches, and their Lean
signature strings contained literal Unicode escapes. Second reading ran relevant searches
for each statement, recorded the actual service responses (LeanSearch returned HTTP 500,
recorded as unavailable), inserted verbatim Lean signatures, and made the site and
fixed-square statements self-contained. No new statement duplicates an existing theorem:
Mathlib limit closure is reused, the existing prescribed comparison theorem is specialized,
and the existing ring-object transport is reused in the remaining hole's plan.

The remaining transport is too substantial for a few-minute formal closure: besides ring
transport it needs the geometric ring-map fields, three additive module functors, and their
generalized-element scalar-action equations. Searches found the existing finite-product
ring functor and geometric module construction; the former is included in the plan. The
latter's operation comparisons do not alone supply the fixed square and RingedToposMorphism
fields. No extra proof hole is introduced for these substeps.

## New nodes

`lem-weil-pbc-topos-compatible-generators`: Mathlib limit closure of terminal/pullback
shapes, a small model, and the essential-image lift supply compatible generators.
Its module is `ToposCompatibleGenerators`; the theorem is complete.

`lem-weil-pbc-site-of-sheaf-generators`: specializes the existing prescribed comparison
lemma, proves its support criterion and the strong precoverage axioms. Its module is
`SiteOfSheafGenerators`; the theorem body is complete, depending on the existing comparison.

`lem-weil-pbc-topos-site-presentation`: combines those two lemmas and the Hom adjunction
into cover preservation and the natural direct-image comparison. Its module is
`ToposSitePresentation`; the theorem body is complete.

`lem-weil-pbc-ringed-topos-square-transport`: only ring and module transport on an already
fixed geometric square; it constructs no site, generator, cover or continuity proof.
Its module is `RingedToposSquareTransport`, and it is the one remaining named hole.

## Second reading by Q2

1. Compared every delivered module with the repository. Only
   `RingedToposSitePresentation` already exists there; its full theorem signature is
   byte for byte identical. There are no changed definitions, extra hypotheses or weakened
   conclusions. The other four modules are new. The unused public cohomology import is the
   only existing visibility change and is declared in the change record above. No module
   held by another group is changed.
2. Read the complete proof bodies and locally compiled all five modules. The single direct
   `sorry` is exactly the report's fixed-square theorem, with source and full proof docstring.
   All actual constructions (including private limit closures and Hom isomorphisms) have
   real terms. There is no axiom, unsafe, opaque, implemented_by or extern declaration.
   The explicit axiom probe confirms only the three allowed axioms for every completed
   helper, and additionally sorryAx for the item and the named transport hole. The
   delivery tool also checks every declaration, including private helpers.
3. Read [03CR](https://stacks.math.columbia.edu/tag/03CR),
   [03CI](https://stacks.math.columbia.edu/tag/03CI),
   [03A1](https://stacks.math.columbia.edu/tag/03A1),
   [03A2](https://stacks.math.columbia.edu/tag/03A2), and
   [03CJ](https://stacks.math.columbia.edu/tag/03CJ). The fixed-square statement is the
   ring/module portion of the argument after the geometric square has been supplied.
   For the generator result, terminal closure is included even if the original category
   is empty; the image family is small in the same universe. For comparison, full
   faithfulness, representable inclusion and preservation of pullbacks are all supplied.
   Empty covering families are allowed and joint cancellation handles them without a
   nonemptiness assumption. For transport, the identity-equivalence case gives the usual
   ring maps and module actions, and the zero-ring/zero-module case uses no nonzero scalar.
   The construction is valid on empty sites as it only uses finite products. Alpha need
   not be chosen as an adjunction mate: full faithfulness lifts the displayed conjugated
   ring map for any natural square isomorphism. The docstring now gives that equation
   rather than saying only that the mate identities work. Searched Mathlib through
   msearch.py and the local upstream and Sheaf libraries with alternate terms (internal
   rings, geometric module construction, joint epimorphy, dense subsite, and limit closure).
   The existing finite-product ring-functor theorem is reused in the plan. The remaining
   helper is strictly smaller than the item because all site/generator/continuity work
   has been discharged before it is applied.
4. Checked the top-down route and every import. The first worker's actual proof already
   uses Mathlib limitsClosure and direct Hom-adjunction cancellation; retained that proof.
   Proof-only closure imports are now private, redundant imports are removed, and the
   pruning section above enumerates every former direct DAG dependency. Read
   `dag/units/sk-thm-properbasechange.json`: its realized statement nodes are torsion
   assembly/bounded-below PBC, and its realized steps are projective-line PBC, reduction
   to projective line/prime PBC, and torsion assembly. None is replaced or bypassed by this
   supporting site lemma; the unit file is unchanged.
5. Checked the node statements, Lean records and proof routes against the modules. Fixed
   the escaped signatures, self-contained node statements, actual search records and
   proof_origin. The generator closure uses Mathlib, the comparison helper cites the
   existing comparison, the geometric helper cites just its two construction helpers,
   and the item cites that geometric helper plus fixed-square transport. The proof_deps
   lists are exactly the unions of the proof steps' uses. The single unresolved node
   now gives the explicit structural-map and module-action construction in its plan.

Second reading changed imports and module documentation, expanded the remaining proof
sketch, repaired the four new-node records, and corrected the pruning and hole-count
report. The valid proof bodies and the existing theorem signature were retained.
