## What changed

Proved `AlgebraicGeometry.injective_restriction_surjective` in
`lean/Sheaf/AlgebraicGeometry/InjectiveRestrictionSurjective.lean`, preserving its entire
signature and both conclusions. Added proof-only imports
`Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator` and
`Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`.

The free Yoneda presheaf on an open is the extension-by-zero presheaf of the source.
The sheafification adjunction and free Yoneda equivalence identify its sheafified Hom
with sections. Naturality identifies precomposition with restriction. The map of free
presheaves is sectionwise injective, since all Hom sets of opens are subsingletons;
left exact module sheafification preserves this monomorphism. `Injective.factors`
then lifts an arbitrary section. For the difference map, lift to the first factor
and set the second factor to zero.

Updated the item's DAG proof, proof dependencies and proof origin to this route.
The unit `sk-thm-curveestimate` realizes only `thm-sc-proper-cohomology` as its statement
and has no realized steps; this local simplification bypasses no unit statement or step.
No definitions, theorem signatures or public imports changed.

## Proved and sorry left

Proved `AlgebraicGeometry.injective_restriction_surjective`
(node `lem-sc-ringed-space-injective-restriction-surjective`): one of one original
sorries closed, including both the restriction and difference-map clauses.
No sorry remains in the delivered module, and none was introduced elsewhere.
Local single-file compilation succeeds without warnings.

The proof applies uniformly to the empty space, empty opens, equal opens, and zero
structure rings or modules: the free module on an empty indexing set is zero;
subsingleton injectivity requires no nonemptiness or nonzero ring hypothesis.
No finiteness or separation hypothesis is used.

## No longer needed

Removed proof-only imports:

- `Sheaf.Algebra.Homology.ModuleStalkExact`.
- `Sheaf.Topology.PresheafModuleStalkFunctor`.

Removed from the item's proof dependencies:

- `def-weil-pbc-module-stalk`
  (`Sheaf.Topology.PresheafModuleStalkFunctor`).
- `lem-weil-pbc-stalk-sheafification-space`
  (`TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`).
- `lem-weil-pbc-module-stalk-exact`
  (`Sheaf.Algebra.Homology.ModuleStalkExact`).

These are unnecessary for this proof; other targets or modules may still need them.
The original public imports stay because the signature uses `moduleRings`,
`SheafOfModules` and `Injective`.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The DAG's stalk argument is valid but
unnecessary: sectionwise injectivity and Mathlib's left exact module sheafification
provide the monomorphism directly. Existing Mathlib-leaf nodes
`lem-weil-pbc-free-yoneda-presheaf-module` and
`lem-weil-pbc-ringed-site-module-sheafification-exact` now record the APIs actually used.
The original docstring is preserved; its stalk proof remains a valid alternative,
while the inline comment and updated DAG explain the implementation's shorter route.

The source file is absent locally. Read Stacks Tag 01EA at
https://stacks.math.columbia.edu/tag/01EA and checked the arbitrary ringed-space,
nested-open and injective-module hypotheses against the unchanged Lean statement.
Searches executed with msearch: LeanFinder for injective restriction surjectivity,
Loogle for `PresheafOfModules.freeYonedaEquiv`, and grep for
`injective.*restriction|flasque|freeYonedaEquiv`; also searched both library roots
and read the relevant Mathlib declarations. No direct matching theorem was found;
the free Yoneda and sheafification APIs suffice to complete the proof.

## Second reading by B3

1. Interface: compared the entire delivered module against the repository with `diff`;
   the existing theorem signature is byte-for-byte identical. Only its proof and two
   proof-only imports changed. No definitions, declarations or public imports changed;
   no change record is required. Pass.
2. Proof: local single-file compilation succeeds without errors or warnings. There are
   no sorries or forbidden declarations. A scratch copy with `#print axioms` reports
   exactly `propext`, `Classical.choice`, and `Quot.sound`. Read the free Yoneda equivalence,
   sheafification adjunction and finite-limit-preservation instance in pinned Mathlib;
   checked the naturality equation and the orientation of the injective factorization.
   Equal opens, empty opens, the empty space and zero rings need no extra assumptions.
   Both conclusions follow as stated. Pass.
3. Split statements: none were added, and no sorry remains. Independently searched both
   library roots and Mathlib for flasqueness and surjective restrictions. The upstream
   `AlgebraicGeometry.Scheme.Modules.isFlasque_of_injective` proves the analogous result
   for schemes, rather than arbitrary ringed spaces, so it cannot replace this proof.
   Its argument uses the same free-module construction. No duplicate general theorem
   or split-off restatement was found. Pass.
4. Route and pruning: the proof directly uses proved Mathlib APIs and injectivity,
   with no open library theorem. Both added imports are proof-only and used. The report
   lists all three dependencies removed from the old `proof_deps`, together with both
   removed imports. Read `dag/units/sk-thm-curveestimate.json`: its realized statement
   is `thm-sc-proper-cohomology` and its realized steps are empty; this local route
   bypasses neither. Pass.
5. DAG: compared the node JSON with the repository. Only `proof`, `proof_deps` and
   `proof_origin` changed. The dependency list is exactly the union of the proof steps'
   `uses`; the referenced free-Yoneda and exact-sheafification nodes match the Mathlib
   APIs used by Lean. No new node or statement change was introduced. Pass.

Changes by the second reader: added this review and clarified the search result by
recording the existing scheme-only analogue. No Lean or node repair was needed.
