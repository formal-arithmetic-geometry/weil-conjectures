## What changed

Completed the existing sandbox proof of
`AlgebraicGeometry.Scheme.Modules.exists_isIso_tensorPullback_of_isIso_moduleStalkMap`
without changing its signature. Added two proved supporting modules,
`Sheaf.AlgebraicGeometry.FiniteLocallyFreeStalkHomLift` and
`Sheaf.AlgebraicGeometry.FiniteLocallyFreeStalkHomEquality`, as proof-only imports.
The argument extends the stalk inverse, shrinks both inverse identities, intersects
those neighbourhoods and compares restriction with tensor pullback by uniqueness
of left adjoints. Updated the original node to describe these actual dependencies.
Removed unused coordinate-basis and projection-evaluation helpers from the earlier attempt.

Repair of the landing refusal: deleted the duplicate private declarations
`unit_hom_ext_top`, `exists_restrict_eq_of_free_germs_eq`, and
`restrict_map_injective_of_isIso` from the equality helper. Added the proof-only
`import all Sheaf.AlgebraicGeometry.FiniteFreeStalkMapEquality`; Lean now resolves
the two helper applications to that module's existing private declarations.
`unit_hom_ext_top` is used by the imported finite-germ helper and needs no local
copy. No existing library module or signature was changed. The equality node
now records this reused dependency. The old second reading was removed because
the repaired delivery requires a fresh independent reading.

The lifting construction uses actual sections representing finitely many germs;
no definition takes arbitrary data from an unproved theorem. The supporting lemmas
allow an arbitrary target sheaf. Empty frames use empty sums and intersections;
no positive-rank, affine, noetherian or reduced hypothesis is added.


Repair of the current return (duplicate coordinate proofs): removed the entire
private `Coordinates` section from `FiniteLocallyFreeStalkHomLift`, including
`coordinateAdd_germ`, `coordinateLinear_germ_of_le`, `localBasisGerm_eq`,
`local_sum`, and `sum_coordinate_basis` and their duplicate constructions.
Added the proof-only `import all Sheaf.AlgebraicGeometry.FiniteLocallyFreeStalkFinrank`.
All coordinate references now resolve to the existing private declarations;
no existing library file, signature or visibility changed. Replaced the direct
`FlatPullbackStalk` import, which was needed only by the removed constructions.
Updated the lifting node to record the reused coordinate dependency. Removed
the stale second reading so a second worker can review this repair afresh.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.Scheme.Modules.exists_isIso_tensorPullback_of_isIso_moduleStalkMap`
(node `lem-sc-finite-locally-free-stalk-iso-neighborhood`).

Also proved the two new declarations:
`AlgebraicGeometry.Scheme.Modules.exists_restrict_stalk_hom_lift`
(node `lem-sc-finite-locally-free-stalk-hom-lift`) and
`AlgebraicGeometry.Scheme.Modules.exists_shrink_restrict_hom_eq_of_germs`
(node `lem-sc-finite-locally-free-stalk-hom-equality`).

No sorry remains in any delivered module, and no holes were added or split off.

## No longer needed

No downstream modules are pruned. The lifting helper no longer directly imports
`WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk`: its coordinate
construction and expansion are reused from `FiniteLocallyFreeStalkFinrank`.
The five duplicated lemmas and six duplicate coordinate constructions are removed.
Their existing implementations remain in that module; no DAG node is pruned. The repair removes three
duplicate private proofs; their original declarations remain in
`Sheaf.AlgebraicGeometry.FiniteFreeStalkMapEquality` and are reused. No node or
module is pruned by that reuse. The original dependency
`def-weil-open-immersion` is not a separate proof input: open inclusions and their
restriction comparison are supplied by the scheme-module API. The original
`def-sc-finite-locally-free-sheaf` proof input is used in the supporting nodes.
The statement dependencies remain unchanged. No part of the unit's route is bypassed.

The second reader removed the unused public import
`Sheaf.Algebra.Homology.ModuleStalkFunctor` from the new equality module.
Its statement and proof use presheaf germs and Mathlib's restriction-stalk
comparison, already available from `Mathlib.AlgebraicGeometry.Modules.Sheaf`.
This removes no module from the targets' import closure: the item's statement
and the lifting helper still need `ModuleStalkFunctor`. The fresh second reader
also removed `def-pc-module-stalk-functor` from the equality node's proof dependencies
and first proof step: that proof uses additive presheaf stalks, not the module-stalk
functor. Its statement dependencies remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The current return correctly identifies five coordinate lemmas duplicated from
`FiniteLocallyFreeStalkFinrank`. Their binders and meanings agree, and `import all`
permits reuse of both their private constructions and proofs. The preceding
reading missed this duplication; this repair removes it rather than renaming it.

The returned delivery duplicated three private lemmas already present in
`FiniteFreeStalkMapEquality`. Its previous reading incorrectly treated private
visibility as a reason not to reuse them. A proof-only `import all` makes these
existing declarations available without changing their visibility or interfaces.

The earlier attempt had compiling Lean proofs but no report or DAG records for its
two new supporting modules. This delivery supplies them and removes two unused
private helpers. The node's elementary matrix steps concealed the substantial
coordinate-colimit and restriction-comparison glue now implemented in the helpers.

Checked Stacks Tags 05GF (lemma-map-between-finitely-presented) and 00O0(3).
The auxiliary results are the finite free sheaf versions of the generator and
relation argument, rather than verbatim statements of those affine module lemmas.
Blueprint duplicate search for "finite locally free stalk" returned no matches;
repository and Mathlib searches found germ representation/equality and free-frame
APIs, but no existing public theorem with either supporting statement.
LeanSearch was unavailable (Internal Server Error); the earlier worker's recorded
LeanFinder, Loogle and grep searches were retained and checked against the APIs used.

## New nodes

`lem-sc-finite-locally-free-stalk-hom-lift`: a linear stalk map with finite locally
free source extends near the point. Its proved construction uses finite free
coordinates and representatives of the finitely many image germs.

`lem-sc-finite-locally-free-stalk-hom-equality`: equality of local-section germs
for two maps with finite locally free source holds as equality of maps after
shrinking. Its proof shrinks finitely many basis equations and uses the free
coproduct universal property. Both nodes are in `dag/nodes/sec-abelian-varieties/`.
No statement changes, forced adaptations or change records are needed.

## Second reading by T3

1. **Interfaces: PASS.** Compared the item with the repository using `diff -u`.
   Its existing theorem signature and visibility are byte for byte unchanged;
   only the proof, two plain imports, and whitespace differ. Both supporting
   modules and their nodes are new; no existing definitions or other modules
   are adapted. No change record is needed.
2. **Proof and axioms: PASS.** Compiled all three files in import order with
   `lcompile.py --all`, without errors or warnings. Scanned every delivered
   Lean file: no sorry, axiom, unsafe, opaque, implemented_by, extern or kernel
   bypass. A scratch copy with `#print axioms` for all three public theorems
   reports only propext, Classical.choice and Quot.sound. The delivery tool
   additionally audits every declaration. The lifting definitions construct
   sections and morphisms explicitly; their choices use proved germ
   representation and proved finite local trivialization, never an unproved
   existence assertion.
3. **Supporting statements: PASS.** No statement is split off with sorry.
   Read both proved helper statements and their complete docstring arguments.
   Lifting requires finite local freeness only of the source and works for an
   arbitrary target. Equality likewise needs only finite local freeness of the
   source. Empty finite frames give empty intersections/sums, and an empty
   scheme has no point at which a witness is required. These are proper parts
   of the argument, not restatements of the isomorphism-neighbourhood theorem.
   Independently searched the repository, upstream module sources and Mathlib,
   and repeated LeanFinder with "A homomorphism from a vector bundle stalk is
   represented by a sheaf homomorphism locally" and "Finite generation of the
   source makes equality of sheaf maps at a point hold on an open set".
   Results concern general section/stalk extensionality and ring spreading,
   not either supporting statement. Loogle on "exists_germ_eq" confirms the
   germ representation API used here. Checked reuse of the coordinate helpers
   in FiniteLocallyFreeStalkFinrank and the finite-germ equality helper in
   FiniteFreeStalkMapEquality directly against their source.
4. **Route and pruning: PASS.** Read top down: extend the inverse, shrink both
   inverse identities, intersect the opens, transport restriction to tensor
   pullback by uniqueness of left adjoints. No shorter existing theorem was
   found with these hypotheses. Public imports supply the signatures; the
   supporting/coordinate/equality imports are proof-only, including `import all`.
   Every removed original proof dependency is accounted for under
   `## No longer needed`: finite local freeness is used through the helpers,
   and the separate open-immersion definition is supplied by the scheme API.
   Read `dag/units/sk-prop-av-cube.json`, including its currently empty
   `realized.statement` and `realized.steps` arrays. This auxiliary node does
   not realize a unit step; the cube/general-cube route is unchanged. No module
   is pruned from the targets' import closure.
5. **DAG: PASS.** Compared the existing node with the repository: only proof,
   proof_deps and proof_origin change. Read both new nodes, their statements,
   verbatim Lean signatures, sources, searches, creation records, blueprint
   provenance and chapter/unit fields. Their proof dependencies are exactly
   the unions of the step uses and describe the declarations actually reused.

Second-reading repair: removed the remaining duplicate private theorem
`stalk_map_eq_of_natIso` from FiniteLocallyFreeStalkHomEquality. Its three uses
now apply the existing `map_eq_of_iso` from FiniteFreeStalkMapEquality to the
inverse natural isomorphism. Updated the equality node's proof and proof_origin
and this report. No public signature, definition or import changed in this
repair. One original hole closed, zero holes added; both new helpers are proved.
