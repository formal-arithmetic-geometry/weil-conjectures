## What changed
The existing `Sheaf.CategoryTheory.SheavesAlgebraicStructuresRing` signature and
public imports are unchanged. Its proof obtains the sectionwise construction
from `SheavesAlgebraicStructuresRingCore`, then applies the proved
`SheavesAlgebraicStructuresRingMorphism` criterion to the same functors.
Both new imports in the existing module are proof-only.

## Proved and sorry left
`CategoryTheory.sheavesAlgebraicStructuresRing` has a complete reduction proof
(node lem-weil-pbc-sheaf-algebraic-structures-ring-component), conditional on the
construction component. `CategoryTheory.sheavesAlgebraicStructuresRing_morphism`
is proved without sorryAx (node lem-weil-pbc-sheaf-algebraic-structures-ring-morphism).
Only `CategoryTheory.sheavesAlgebraicStructuresRing_core` remains sorry
(node lem-weil-pbc-sheaf-algebraic-structures-ring-core).

## No longer needed
The old proof dependency `lem-weil-pbc-sheaf-algebraic-structures-objects`
(`Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects`) is no longer used by
this component: that module itself imports and applies this component, so using
it here would be circular. This does not make the objects module globally
unreachable: it remains the caller realizing the larger correspondence.
Removed redundant imports `Mathlib.CategoryTheory.Monoidal.CommGrp_` from both
new modules and `Mathlib.Algebra.Category.Grp.Limits` from the core module.
Their needed declarations are already publicly supplied by the retained imports.
The existing module's public import surface is unchanged.

## Where the brief, the DAG or earlier work was wrong
The first worker's two new proof plans cited the parent component as their proof
dependency, creating a cycle. They also had abbreviated proof descriptions,
duplicate blueprint markers, and long-line warnings. The parent node was not
updated to describe the actual reduction. These have been repaired. The morphism
criterion needs no separate sectionwise argument: fullness of F suffices. Its
hypothesis h₁ is retained (named _h₁) but unused.

## New nodes
`lem-weil-pbc-sheaf-algebraic-structures-ring-core` states the construction and
operation compatibility, strictly omitting the morphism criterion; its only
non-elementary planned dependency is the existing Mathlib leaf
`lem-weil-pbc-algebraic-sheaf-iff-underlying-sets`.
`lem-weil-pbc-sheaf-algebraic-structures-ring-morphism` is a proved categorical
lemma with no project proof dependencies. Both are in
`dag/nodes/sec-proper-base-change/`. No change record is needed: no existing
statement, definition, or public import changed.

## Second reading by R1
1. Compared the existing module with the repository using diff. The existing
   theorem's signature and docstring are byte for byte unchanged; only private
   proof imports and its proof body changed. There are no definitions to alter.
2. Compiled all three modules locally. No forbidden declarations or hollow
   definitions occur. The only remaining sorry is the named core theorem.
   Scratch #print axioms checks give only propext, Classical.choice and Quot.sound
   for the morphism theorem; the core and target additionally use sorryAx from
   the core. The morphism proof uses naturality, categorical fullness and
   AddGrpObj.neg_comp, not the core theorem.
3. Read Stacks 00YR and 00YV online (the local sites.tex is absent). The ring
   sextuple description supplies the construction route. The docstring now
   details section operations, naturality, both reconstructions and strict
   identities. Checked the empty site, singleton/zero-ring sections, and general
   restriction maps: there is no nontrivial-ring or nonempty-site hypothesis.
   The categorical morphism proof applies to arbitrary strict inverses over the
   forgetful functor, independent of the sectionwise formulas. Searched with
   leanfinder, loogle and grep through msearch using different queries and read
   Mathlib Monoidal/Ring.lean, Monoidal/Cartesian/Ring.lean, Monoidal/Grp.lean,
   Monoidal/Cartesian/Grp.lean and Functor/FullyFaithful.lean. No exact existing
   construction was found; yonedaCommRing is a presheaf of hom sets rather than
   this sectionwise correspondence. Loogle does not know CommRingObjCat, recorded
   as unavailable for that identifier, not an exhaustive negative result.
   LeanSearch returned Internal Server Error, recorded as unavailable.
   Local rg searches of lean/Sheaf and upstream WeilConjectures found the existing
   parent correspondence, which depends on this component and cannot prove it.
4. The shortest categorical route closes the morphism split completely. Core is
   a proper construction subproblem, now separated from a genuine proved part of
   the argument. Checked dag/units/sk-def-exchange.json: its realized statement
   nodes are def-weil-pbc-derived-exchange and
   lemma-weil-pbc-derived-exchange-replacement; it has no proof steps and this
   component is not a realized unit node. The ring correspondence route stays.
   Every old parent proof dependency is listed under No longer needed.
5. Updated the parent proof/proof_deps/proof_origin to the two actual components.
   Removed circular parent dependencies from new nodes. The core plan cites the
   existing underlying-set sheaf criterion; the morphism node describes the
   actual Mathlib proof and has no project proof_deps. New Lean signatures match
   their node records, with required source, creation, blueprint and search data.

Second reading changed: proved the morphism lemma, expanded both docstrings,
removed redundant new-module imports and warnings, corrected circular DAG plans,
updated the parent node, and rewrote the report to distinguish the conditional
reduction from a theorem proved without sorryAx.
