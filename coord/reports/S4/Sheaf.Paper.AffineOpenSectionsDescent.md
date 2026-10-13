## What changed

Replaced the sole sorry in `Sheaf.Paper.AffineOpenSectionsDescent` by a complete
Lean reduction. Its signature and visibility are unchanged. The proof now obtains
an inverse-image unit representative on an arbitrary étale X-object, factors its
underlying geometric map through an affine stage, and uses pullback extensionality,
unit naturality and the supplied cocone component equation to construct the requested
stage section.

Added two proof-only imports and two modules:
`Sheaf.Paper.AffineOpenEtaleMapFactorization` is proved directly from Mathlib's
`Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`;
`Sheaf.Paper.AffineOpenInverseImageUnitRepresentatives` states the remaining
inverse-image/sheafification step. No existing definitions or interfaces change,
and no other existing module is adapted. Updated the existing node's proof route
and added matching nodes for both helper declarations.

## Proved and sorry left

Closed the original hole `affineOpenSections_descent` (1 of 1 in the item).
Its proof is complete but depends on the new named section lemma below; this is
one-hole-to-one-hole decomposition, not an axiom-free proof or a net hole reduction.

Also proved `affineOpenSections_etale_map_factorization`, node
`affine-open-etale-map-factorization`, using existing Mathlib geometry. It needs no
sheaf-continuity sorry and adds no hole.

The only newly added sorry is
`affineOpenSections_inverse_image_unit_representatives`, node
`affine-open-inverse-image-unit-representatives`. It concerns representation on an
arbitrary étale X-object, without the conclusion's prescribed stage. Its docstring
supplies the affine-basis section construction, finite-cover descent, adjunction,
and localization argument. The real geometric factorization and the proof converting
that representative into the required stage section are separate and complete.
There are no sorries left in the item's module or in the geometric helper, and no
sorries inside definitions. Singleton systems, zero sheaves and empty limits are
addressed in the remaining lemma's proof text; cofilteredness excludes empty J.

## No longer needed

No original imports were removed: the item initially had only three public
statement imports. No claim of a whole-module prune or a net closure decrease is made.

The original node's five dependencies are no longer direct dependencies of the main
proof: `lem-weil-pbc-affine-etale-site-colimit`,
`lem-weil-pbc-cofiltered-limit-directed-reindex`, `lem-weil-pbc-colimit-of-sites`,
`lem-weil-pbc-etale-inverse-image-restriction`, and
`lem-weil-pbc-filtered-colimit-sets-elementwise`. Cofiltered reindexing, finite-family colimit sites, localization restriction,
and elementwise filtered-colimit representation remain in the new section lemma's
plan, so they are not claimed as globally pruned. The implemented module
`Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit` (node
`lem-weil-pbc-affine-etale-site-colimit`) is not needed for this route: the remaining
lemma instead cites finite-diagram and finite-cover descent components and the
finite-family colimit-site construction. Other target paths may still reach the
old affine-site module. No unused proof imports were retained.

## Where the brief, the DAG or earlier work was wrong

The original site route reaches
`Sheaf.AlgebraicGeometry.AffineEtaleColimitPresentation`, whose declarations already
carry `STATEMENT-DISPUTED`: finite presieves cannot satisfy unrestricted indexed
composition closure. Its current proof uses a refutation and a sorry-bearing
strictification assertion. This delivery does not import that route or use its
contradiction. The remaining section lemma's plan requires finite indexed covers,
as in the corrected colimit-site statement, together with the geometric component
descent theorems.

Direct use of the general sheafification/Kan-extension interfaces encountered a
universe mismatch: the current scheme objects are in universe u+1, their full étale
site objects in u+2, while the fixed coefficient category is AddCommGrpCat.{u+1}.
Existing broad continuity interfaces expect the larger coefficient universe. No
signature was enlarged to evade this issue; the remaining lemma keeps exactly the
item's universes and requires the affine-basis construction.

`tools/blueprint_refs.py ancestor affine-open-sections-descent` did not resolve the
ancestor through the existing module-name `created.item` chain. The new nodes use
the existing node's explicit blueprint ancestry, appending this node to `via`.
The unit statement and its realized steps remain unchanged.

## New nodes

`affine-open-etale-map-factorization`, module
`Sheaf.Paper.AffineOpenEtaleMapFactorization`: source [Stacks Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM),
morphism descent, and the existing Mathlib factorization node. It proves only the
geometric part of the section argument, with no sheaf hypothesis. Its Lean proof
supplies qcqs and affine-transition instances, the map over X, and both equations.

`affine-open-inverse-image-unit-representatives`, module
`Sheaf.Paper.AffineOpenInverseImageUnitRepresentatives`: sources
[Stacks Tag 0A35](https://stacks.math.columbia.edu/tag/0A35),
[Tag 0EYL](https://stacks.math.columbia.edu/tag/0EYL), and
[Tag 03Q6](https://stacks.math.columbia.edu/tag/03Q6).
This is the inverse-image section part; its conclusion has no prescribed stage,
no section on D(j), and no cocone. The main proof performs geometric descent and
checks the cocone compatibility rather than forwarding the original goal.
No change record is needed because no existing interface changes.

## Second reading by S4

1. Compared every delivered module with the repository using `diff`. Only the main
   module already existed. Its declaration signature is byte-for-byte unchanged;
   the declaration-table check reports no interface, visibility or public-import
   change. No definition or target was altered and no change record is required.
2. Compiled all three modules in import order using lcompile.py, without errors
   or warnings. Scratch-copy `#print axioms` checks give only propext,
   Classical.choice and Quot.sound for affineOpenSections_etale_map_factorization;
   the main theorem and the unit-representative lemma additionally use sorryAx.
   The latter is the sole named sorry delivered. No forbidden declarations,
   hollow definitions or arbitrary data chosen from unproved existence occur.
3. Read the new declarations, their nodes, and Stacks Tags 0A35, 0EYL, 03Q6 and
   01ZM. The geometric lemma is directly proved by the Mathlib factorization
   theorem. The remaining lemma is the inverse-image section step, strictly
   before the geometric factorization and cocone calculation, not the original
   conclusion renamed. Checked singleton systems (localization), zero coefficients,
   empty limits (finite empty-cover descent), and nonempty cofiltered indices.
   Repeated LeanFinder, Loogle and grep searches with different queries; inspected
   ColimitSiteAbelianSectionRepresentatives, EtalePullbackUnitPointedWitness and
   LocalStalkSectionsDescentSections. These require different site data, coefficient
   universes or point hypotheses and do not directly discharge this statement.
   Closing the remaining section lemma would require the affine-site comparison
   construction, not a short omitted application.
4. Followed the main proof from the target downward: representative, proved
   finite-presentation factorization, pullback extensionality, unit naturality.
   Both new proof-only imports are used; the original public imports support its
   signature. All five former proof dependencies are explicitly listed above.
   Read dag/units/sk-thm-p1.json, including its realized statement and steps;
   this is a reduction below those steps and does not bypass the unit route.
5. Compared the Lean argument with all three nodes. The main node records the
   two helpers and the elementary naturality calculation; the geometric node
   records its exact Mathlib dependency; the remaining node records its sourced
   construction plan. New nodes have their statements, sources, search records,
   creation data, ancestry and verbatim Lean signatures. Existing-node changes
   are confined to proof, proof_deps and proof_origin.

Changes by this reader: expanded the new section lemma's proof docstring to
specify canonical pullback coherence (or strictification of the fibred diagram),
finite affine-cover refinement and common-stage overlap equalities; explicitly
listed every old direct dependency under No longer needed. No proof or statement
was changed. This remains one hole closed and one added, hence a decomposition
with net zero holes, plus one axiom-free geometric helper.
