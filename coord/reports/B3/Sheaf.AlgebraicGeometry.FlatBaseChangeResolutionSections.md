## What changed

Reduced `AlgebraicGeometry.Scheme.Modules.flatBaseChangeResolutionBeta_sections` to
 two independent parts of the existing source argument: a generic section formula
for the homology mate of a map of complexes, and the restricted augmented lift's
comparison with `moduleCohomologyFMap` before sheafification. The parent combines
these equalities by congruence and transitivity. The canonical open map is built
from the given section-complex map and specified source and target isomorphisms;
it uses no postponed theorem or arbitrary existence witness.
The existing statement, definitions and public imports are unchanged.
The resumed attempt removed an unnecessary local `irreducible` attribute that
triggered the interface-change check. The parent compiles without it. Its
signature is byte-identical to the original, and all four node Lean statement
records match their declarations.

## Proved and sorry left

Closed the original direct hole of
`AlgebraicGeometry.Scheme.Modules.flatBaseChangeResolutionBeta_sections`
(node `lem-weil-pbc-flat-base-change-resolution-sections`) by decomposition.
Added exactly two holes, both strictly partial arguments:

- `AlgebraicGeometry.Scheme.Modules.flatBaseChangeResolutionBeta_openMap_sections`, node
  `lem-weil-pbc-flat-pullback-homology-sections`, in
  `Sheaf.AlgebraicGeometry.FlatPullbackHomologySections`.
- `AlgebraicGeometry.Scheme.Modules.flatBaseChangeRestrictedLift_homology`, node
  `lem-weil-pbc-flat-base-change-restricted-lift-homology`, in
  `Sheaf.AlgebraicGeometry.FlatBaseChangeRestrictedLiftHomology`.

This is a decomposition, not a complete proof of the mathematical result.
One direct hole is closed and two are added: the delivery has net -1 holes closed
before any separate import-closure pruning measurement. Neither new obligation
is proved here; the parent still depends on `sorryAx`.
The section-transport lemma has no augmented-lift condition or cohomology h-map;
the restricted lemma has no flatness, beta or derived-image comparison maps.
The new definition `flatBaseChangeResolutionOpenMap` has no holes. It separates
the genuine section-complex map from the augmentation-dependent identification.
Small cases checked mathematically: p = 0 uses ordinary cycles with zero incoming
boundary; zero complexes and zero maps give zero on both sides; empty opens have
zero section groups; the identity base map gives ordinary homology naturality.
The restricted statement uses augmentation-preserving comparisons, so it cannot
silently change sign when choosing another resolution isomorphism.

## No longer needed

Removed these direct proof imports from the original module:

- `Sheaf.Algebra.Homology.BoundedBelowInjectiveResolutionMono`:
  node `lem-weil-pbc-complex-injective-resolution-mono`; retained as a dependency
  of the restricted-lift obligation, not globally pruned.
- `Sheaf.AlgebraicGeometry.PushforwardInjectivesSectionsQuasiIso`:
  node `lem-weil-pbc-module-pushforward-injectives-sections-quasi-iso`; retained
  for the restricted-lift obligation, not globally pruned.
- `Sheaf.AlgebraicGeometry.ModuleCohomologyFMapFunctorial`:
  node `lem-weil-pbc-module-cohomology-fmap-functorial`; retained for the
  restricted-lift obligation, not globally pruned.
- `Sheaf.Paper.HigherDirectImagePresheaf`:
  node `lem-weil-pbc-higher-direct-image-presheaf`; none of its five conclusions
  is needed. The generic obligation works directly with the canonical theta
  construction and its naturality. This proof route no longer depends on that
  theorem or module.
- `Sheaf.AlgebraicGeometry.FlatModulePullbackExact`:
  node `lem-weil-pbc-flat-module-pullback-exact-pushforward-injective`; already
  publicly supplied by `FlatBaseChangeMapSectionsDefs` and needed by the generic
  obligation, so not globally pruned.
- `Sheaf.AlgebraicGeometry.ModuleCohomologyFMap`:
  node `def-weil-pbc-module-cohomology-fmap`; already publicly available through
  `FlatBaseChangeMapSectionsDefs`, and still needed in statements.

No unit statement or realized unit proof step was bypassed. Both new nodes are
inside the existing node's argument; the unit record `sk-thm-p1` is unchanged.

## Where the brief, the DAG or earlier work was wrong

The previous node compressed two distinct section calculations into one step;
the existing dependencies do not themselves state either calculation. They are
now explicit obligations rather than an invocation of a theorem with a different
conclusion. No existing statement was changed or found false.

The documented local literature source was absent in this checkout; the four
cited Stacks tags were read on the official Stacks website. LeanSearch returned
Internal Server Error, recorded as unavailable. LeanFinder, Loogle, Mathlib grep,
and searches of both library roots found ingredients but no duplicate.

## New nodes

`lem-weil-pbc-flat-pullback-homology-sections` states the homology/adjunction section
formula through the canonical open map for any complex lift, without augmentation. Its proof uses exactness of flat pullback,
the degreewise adjunction identity, passage from cycles to their quotient classes,
and naturality of sheafification. The dependency on the tensor adjunction is the
existing node `lem-pc-module-pullback-adjunction`.

`lem-weil-pbc-flat-base-change-restricted-lift-homology` states the comparison
before applying theta. Its proof restricts the given lift, checks its augmentation
using `D.unit_square`, resolves the pushed target, cancels the invertible section
homology map, and applies independence of the recorded choices. Both nodes have
complete Lean statements and proof docstrings. There are no change records.

`def-weil-pbc-flat-base-change-resolution-open-map` records the real construction
of the intermediate map, with one definition in its own module. Its source and
target isomorphisms are the fixed resolution and section comparisons. This
definition changes no existing interface.

## Second reading by B3

1. Interface: PASS. Compared every delivered module with the repository. Three
   modules are new. In the existing parent only private proof imports and the proof
   body change. Checked the original theorem signature byte for byte, including
   both flatness assumptions, the augmentation equation, all quantified choices,
   and the conclusion. No existing definition, public import, or docstring changes;
   no interface change record is required.
2. Proof and axioms: PASS as a decomposition. All four modules compile separately
   in dependency order through lcompile.py, without errors or warnings. The parent
   evaluates the restricted map equality at xi, applies targetClass, and composes
   it with the homology-mate section equality. The only direct sorries are the two
   reported public named obligations; both have source/proof docstrings and nodes.
   Checked all four declarations with #print axioms in a scratch file: the open-map
   definition uses only propext, Classical.choice, Quot.sound; both obligations and
   the parent additionally use sorryAx. No forbidden declaration or attribute and
   no hollow definition occurs. The open map is an explicit composition of actual
   specified maps and isomorphisms, with no new existence witness selected.
3. Split statements: PASS. Read the definitions of Q, beta, sourceClass,
   targetClass, theta, both choice structures, and ModuleCohomologyFMapData.map.
   The generic obligation cancels the target resolution comparison and transports
   the homology mate through the sheafification unit; it requires no augmentation
   or cohomology h-map. The restricted obligation uses augmentation preservation
   and the unit square to identify the pre-sheafification cohomology map; it needs
   neither flatness nor beta. Neither is the parent under another name. Checked
   p=0 (zero incoming boundary), empty opens, zero complexes, zero t in the generic
   statement, and identity base maps. Changing the restricted comparisons cancels
   against their inverse homology comparisons; their augmentation equations rule
   out an unaccounted sign in the restricted identification. Read official Stacks
   [01FB](https://stacks.math.columbia.edu/tag/01FB),
   [01EZ](https://stacks.math.columbia.edu/tag/01EZ),
   [01E4](https://stacks.math.columbia.edu/tag/01E4), and
   [02N7](https://stacks.math.columbia.edu/tag/02N7) against the docstring arguments.
   Independent LeanFinder, Loogle, and local library/Mathlib searches found
   naturality ingredients, including HigherDirectImageResolutionNaturality, but
   no duplicate or immediate proof of either remaining transport calculation.
   The two holes require substantial comparison work, so neither closes in a
   few-minute application of the existing lemmas.
4. Route and pruning: PASS. The parent uses both new obligations directly. Its
   public definition import is necessary for the unchanged signature; both added
   imports are private proof imports. The new modules publicly import the open-map
   definition because it occurs in their statements. All six old proof-dependency
   nodes and their import disposition are listed under No longer needed. The
   injective-replacement, quasi-isomorphism, and independence imports remain in
   the restricted obligation's plan; flat exactness and cohomology-map definitions
   remain available through the public definition imports. HigherDirectImagePresheaf
   leaves this proof route; this is not a claim that it leaves the whole target
   closure. Checked sk-thm-p1.json and its realized statement and steps: untouched,
   with the decomposition confined below its unit route.
5. Nodes: PASS. All four recorded Lean statements match the declaration source
   verbatim. Every proof_deps list is the union of its proof steps' uses. The parent
   proof and proof_origin describe the actual transitivity/congruence reduction.
   The three new nodes have the required creation, source, search, blueprint,
   chapter, unit, and Lean records. Existing-node edits are confined to proof,
   proof_deps, and proof_origin.

Second reading changed no Lean code. Added independent search records to the
three new nodes (including the missing Loogle search for the restricted-lift node),
made the net -1 hole count and remaining sorryAx explicit, and appended this review.
