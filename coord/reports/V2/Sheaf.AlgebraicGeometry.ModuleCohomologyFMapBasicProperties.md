## What changed

Completed `Sheaf.AlgebraicGeometry.ModuleCohomologyFMapBasicProperties` without changing
any existing public statement or definition. The identity clause is proved directly:
when h is the identity, K with the composite augmentation is an injective resolution
of F, so two applications of derived-functor comparison naturality cancel the vertical
homology isomorphism. The private helpers are fully proved.

The other clauses are assembled from three strictly smaller statements in separate
new modules: scalar compatibility, the degree-zero augmentation square, and naturality
in the target for arbitrary resolution data. Linearity is bundled explicitly;
left exactness provides canonical degree-zero isomorphisms, whose cancellation gives
the displayed degree-zero square; uniqueness of left adjoints gives the restriction
isomorphism and its unit equation. None of the new statements repeats the four-clause
parent theorem. Each has its source, proof in words, and DAG node.

Added proof-only imports of the three new modules and
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits`. Public imports are unchanged.
Updated the parent's proof plan and dependencies to match this argument. No forced
adaptations, public interface changes, or change records are needed.

Validation: all four delivered modules compile without warnings through lcompile.py.
The final deliver3.py --no-push dry run printed OK, including the appended axiom
probes without timeout or disallowed-axiom findings. Its only deferred check is the
second reading, which the next worker writes. Nothing was pushed. Earlier diagnostic
runs timed out; specifying the scalar-restriction target and scoping transparency
options to tactic proofs brought the final checks within the per-file limit.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.moduleCohomologyFMap_basic_properties`.
The identity clause is proved from existing library/Mathlib declarations; the theorem
as a whole is a decomposition, not a fully sorry-free transitive proof.

Added exactly three holes, each the whole proof of a named public theorem:

- `AlgebraicGeometry.Scheme.Modules.ModuleCohomologyFMapData.map_smul`:
  `lem-weil-pbc-module-cohomology-fmap-scalar-compatibility`.
- `AlgebraicGeometry.Scheme.Modules.ModuleCohomologyFMapData.map_zero_augmentation`:
  `lem-weil-pbc-module-cohomology-fmap-zero-augmentation`.
- `AlgebraicGeometry.Scheme.Modules.ModuleCohomologyFMapData.map_target_naturality`:
  `lem-weil-pbc-module-cohomology-fmap-data-target-naturality`.

No sorry remains in the item's module. No private helper or definition contains sorry.
Existing dependencies may still have sorry; they are not newly added holes.

## No longer needed

The second reading also removed the redundant public import
`Sheaf.Topology.RingedSpaceModuleCohomology` from each of the three new modules:
`ModuleCohomologyFMap` already exports it through `PQFCohomology`.

Removed direct proof imports:

- `Sheaf.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy`.
- `Sheaf.AlgebraicGeometry.PushforwardInjectivesSectionsQuasiIso`.
- `Sheaf.AlgebraicGeometry.SchemeModulesEnoughInjectives`.
- `Sheaf.AlgebraicGeometry.TensorPullback`.
- `Sheaf.Paper.PQFCohomology`.

The identity case no longer needs lifting along an injective quasi-isomorphism,
uniqueness up to homotopy, K-injective localization, or acyclic-map nullhomotopy.
The new target-naturality node still needs K-injective comparison and homotopy
uniqueness. Pushforward-sections invertibility is already part of D.invertible;
its construction remains a dependency of ModuleCohomologyFMap, rather than a
second direct proof dependency of this theorem. Enough injectives is taken from
the existing ringed-space theorem. The tensor pullback definition remains in the
statement and is available through the public import ModuleCohomologyFMap.
PQFCohomology's delta-functor theorem is not used; moduleCohomology itself is used.

Removed parent direct DAG proof edges to:
`def-pc-module-pullback`, `def-sp-left-exact-additive`,
`def-weil-sheaf-of-modules-category`,
`lem-weil-pbc-acyclic-map-to-injective-nullhomotopy`,
`lem-weil-pbc-kinjective-hom-derived`,
`lem-weil-pbc-lift-along-injective-quasi-iso`,
`lem-weil-pbc-lift-to-injective-unique-up-to-homotopy`,
`lem-weil-pbc-module-pushforward-injectives-sections-quasi-iso`,
`lem-weil-pbc-scheme-modules-enough-injectives`, and `pqf-def-cohomology`.
Some are still reached through statements, definitions or the new lemmas;
no claim is made that these modules leave the entire targets' import closure.
The item realizes no unit statement or unit proof step, and the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt left the parent theorem unfinished and provided neither
node records nor a report. Its identity proof needed reassociation before cancelling
the homology inverse. Its scalar statement needed an explicit target module carrier,
and the zero-augmentation statement needed the target ring in the forgetful functor.
The target-naturality proof description had an inconsistent direction for the resolution
comparison; it now uses c:D.I -> E.I and e:D.K -> E.K throughout.

Mathlib's `ModuleCat.ofHom` needs its target specified explicitly for restriction of
scalars (as noted beside `semilinearMapAddEquiv` in Mathlib); omitting this produced
failed instance searches and slow elaboration. No definition change was needed.

Searches found abstract derived-functor and homology comparison lemmas, but no exact
library statements for the three remaining resolution-data equations. LeanSearch was
unavailable (Internal Server Error); this is recorded without a fabricated verdict.
Loogle, LeanFinder and local Mathlib/library searches were available. The second reading replaced the parent's obsolete stage-3 proof-plan docstring
with the actual reduction and its three remaining obligations.

## New nodes

`lem-weil-pbc-module-cohomology-fmap-scalar-compatibility` is the scalar equation
before bundling a linear map. Zero rings, zero modules, and degree zero require no
extra hypothesis; injectivity of the vertical homology map is enough to transfer
scalars through its inverse, without inverting the structure-ring homomorphism.

`lem-weil-pbc-module-cohomology-fmap-zero-augmentation` is the square for the
canonical maps from sections to degree-zero derived sections, before using left
exactness to invert them. It is valid for arbitrary D by D.compatible and D.sections.

`lem-weil-pbc-module-cohomology-fmap-data-target-naturality` is the comparison
for b:F -> Fprime with arbitrary choices D and E. No invertibility of b is asserted
or needed; zero and identity b are included. The quasi-isomorphisms that are inverted
are only the vertical maps already declared invertible in the resolution data.

All three nodes are in `dag/nodes/sec-proper-base-change/` with the corresponding
single-statement modules in `lean/Sheaf/AlgebraicGeometry/`. No change records.

## Second reading by V2

1. **Interface: pass.** Compared the delivered parent module with the repository
   using diff and checked its theorem signature byte for byte. It is identical.
   Both existing public imports remain. No existing definition or statement changed,
   no forced adaptations and no change records. The new private comparison definition
   is an explicit composition of canonical isomorphisms, with no postponed data.
2. **Proof: pass as a decomposition.** All four modules compile through lcompile.py.
   The parent and its private helpers contain no sorry; the only three new sorries
   are the complete proofs of the named public theorems listed above. No axiom,
   unsafe, opaque, implemented_by or extern declarations occur. Axiom probing is
   performed by deliver3.py for every delivered declaration. The existing choice of
   resolution data uses the already proved nonempty theorem; the adjunction determines
   its unit uniquely. No arbitrary data is chosen from a newly unproved existence claim.
3. **Split statements: pass.** Read each signature and its complete docstring proof,
   checked the directions of all comparison maps and matched its node. The scalar
   identity uses restriction of scalars and needs no inverse ring map; zero rings,
   zero modules and p=0 give the same identity. The augmentation equation follows
   from the degree-zero compatibility square, including zero sections. Target
   naturality includes b=0 and b=identity and asserts no invertibility of b.
   All three are strictly parts of the four-clause parent argument, not a renamed
   copy of it. Fresh LeanFinder, Loogle and Mathlib grep searches found generic
   restriction-of-scalars and augmentation comparison tools only. Searched both
   library roots: the apparent target-naturality match in ModuleCohomologyFMapFunctorial
   imports this parent and derives its result from it, so using it would be cyclic.
   Formalizing the remaining three resolution equations needs further homology
   comparison work; none has an immediate existing-lemma proof.
4. **Route and pruning: pass.** The identity clause directly uses Mathlib resolution
   comparison naturality twice, without new holes. The other clauses perform the
   linear-map bundling, degree-zero isomorphism cancellation, and left-adjoint unit
   comparison explicitly. Checked sk-thm-p1.realized: this parent and all three new
   lemmas are below its recorded statement and steps, so the unit route is kept.
   The No longer needed list contains all ten removed parent proof edges and all
   five removed direct imports. Removed three redundant imports from new modules;
   no whole module is claimed to leave the targets' import closure.
5. **Nodes: pass.** The existing node changes only proof, proof_deps and proof_origin.
   Checked proof_deps equals the union of step uses in all four nodes. New nodes
   have their source, proof, searches, creation, blueprint, chapter, unit and verbatim
   Lean signature records. The scalar proof text now agrees with its corrected
   docstring. No target statement or unit record changes.

Changes made by this second reader: corrected the scalar proof description to say
that the vertical map is O_Y(Y)-linear on restriction of scalars (rather than assigning
it a semilinear map in the wrong direction); synchronized its node; replaced the
obsolete parent proof-plan docstring; removed the three redundant imports; recorded
fresh searches and this review. No Lean proof body or theorem signature was changed.
The accounting remains one original hole closed and three added (net -2 holes),
a decomposition with a fully written identity clause, not a sorry-free proof.
