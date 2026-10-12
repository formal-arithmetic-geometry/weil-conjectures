## What changed

Reduced `AlgebraicGeometry.Scheme.Modules.flatBaseChangeMap_sections` to three
strict parts of its argument, each in a new module: pairwise equality of the
resolution constructions, existence of compatible restricted choices, and the
section formula for one specified augmented lift. The final proof chooses actual
injective resolutions, constructs an augmented lift, defines beta by the original
resolution construction, and uses pairwise equality again to transport the section
formula for every other resolution pair.

Proved `flatBaseChangeResolutionLift`: a private generic lemma extends the degree-zero
map across the monic augmentation, extends in degree one by exactness, then uses
`CochainComplex.mkHom` and exactness in each positive degree. This specializes the
Mathlib `InjectiveResolution.desc` method to a general degreewise injective target,
which need not itself resolve the pushed-forward module. The only imported theorem
used by this specialization is flat pushforward's preservation of injectives.

Moved the nine existing construction declarations, with identical names, signatures,
bodies and public visibility, into `FlatBaseChangeMapSectionsDefs`. The original
module publicly re-exports them. This avoids import cycles between the theorem and
its new proof modules. Change record:
`coord/changes/flat-base-change-resolution-construction-module.md`.
No existing module other than the item was adapted. The new construction module
contains no sorry and chooses no new data from an unproved existence statement.

## Proved and sorry left

Closed the one original hole, `AlgebraicGeometry.Scheme.Modules.flatBaseChangeMap_sections`
(node `lem-weil-pbc-flat-base-change-map-sections`), by decomposition.
This is a decomposition, not a net reduction in the number of holes: one closed,
three added, local declaration count net minus two. This is not a measured target-closure
ledger figure; imported outstanding statements remain outstanding. No sorry remains in the item's module.

Additionally proved `AlgebraicGeometry.Scheme.Modules.flatBaseChangeResolutionLift`
(node `lem-weil-pbc-flat-base-change-lift`) and its private generic helper `augmentedLift`.
All nine extracted construction declarations retain their original completed bodies.

Every added sorry:

- `AlgebraicGeometry.Scheme.Modules.flatBaseChangeResolutionBeta_independent`
  in `FlatBaseChangeResolutionIndependence`, node
  `lem-weil-pbc-flat-base-change-resolution-independence`.
- `AlgebraicGeometry.Scheme.Modules.flatBaseChangeMap_sections_choices`
  in `FlatBaseChangeOpenChoicesExist`, node
  `lem-weil-pbc-flat-base-change-open-choices-exist`.
- `AlgebraicGeometry.Scheme.Modules.flatBaseChangeResolutionBeta_sections`
  in `FlatBaseChangeResolutionSections`, node
  `lem-weil-pbc-flat-base-change-resolution-sections`.

These are respectively the first, second, and third-through-fifth steps of the
original plan. None repeats the full conclusion or postulates an arbitrary beta.
The section lemma only describes the actual beta of a specified augmented lift.
The pairwise independence lemma contains neither open choices nor a section formula.
The open-choice lemma contains no beta. Edge-case review: p=0, the zero coefficient
module, and empty opens need no added hypotheses; all maps and comparisons remain
canonical. Arbitrary compatible D is retained, as required by the original signature.

## No longer needed

The lift no longer needs the model-category lifting leaf
`lem-weil-pbc-lift-along-injective-quasi-iso`:
`CochainComplex.Plus.modelCategoryQuillen.instHasLiftingPropertyOfMonoOfWeakEquivalenceOfFibration`
from `Mathlib.Algebra.Homology.ModelCategory.Injective`. The degreewise proof uses
exactness and injectivity instead. Resolution comparison lifts in the independence
step are supplied by Mathlib `InjectiveResolution.desc`; uniqueness still uses the
existing homotopy theorem. No unit statement or unit proof step is bypassed.

The original item's proof-only imports were removed from the construction module
and moved to the appropriate outstanding statement modules when their proof plans
need them: `BoundedBelowInjectiveResolutionMono`, `LiftToInjectiveUniqueUpToHomotopy`,
`ModuleCohomologyFMap`, `ModuleOpenRestrictionInjectives`,
`PushforwardInjectivesSectionsQuasiIso`, `TensorPullback`, and
`HigherDirectImagePresheaf`. `ModuleCohomologyFMap` and `TensorPullback` are already
publicly available through the original foundational imports and need no redundant
import. The original public dependencies are all re-exported through the construction
module. No existing Sheaf module is claimed to be removed from the full target closure.
The source plan still needs higher direct image/sheafification and the section-map
comparison; those dependencies remain on the relevant new nodes.

Every old proof dependency removed from the parent's direct `proof_deps` is
accounted for here (these are direct dependencies, not claims of global pruning):

| Old node | Disposition |
| --- | --- |
| `def-pc-module-pullback` | Used by the construction and restricted-choice nodes. |
| `def-weil-pbc-module-cohomology-fmap` | Used by the fixed-lift section node. |
| `def-weil-pbc-sheafification` | Already embodied in `sectionCohomologyTheta` and the higher-direct-image comparison; no separate invocation in the reduction. |
| `lem-weil-pbc-complex-injective-resolution-mono` | Used by the fixed-lift section node. |
| `lem-weil-pbc-flat-module-pullback-exact-pushforward-injective` | Used by the lift, independence, sections, and construction. |
| `lem-weil-pbc-higher-direct-image-presheaf` | Used by the fixed-lift section node. |
| `lem-weil-pbc-lift-along-injective-quasi-iso` | Replaced for the augmented lift by the proved degreewise construction. |
| `lem-weil-pbc-lift-to-injective-unique-up-to-homotopy` | Used by pairwise independence. |
| `lem-weil-pbc-module-open-restriction-injectives` | Used by compatible restricted choices. |
| `lem-weil-pbc-module-pushforward-injectives-sections-quasi-iso` | Used by the fixed-lift section node. |
| `lem-weil-pbc-termwise-adjunction-homotopy` | Used by pairwise independence. |

`lem-weil-pbc-scheme-modules-enough-injectives` remains a direct parent dependency.
The second reader removed the redundant proof-only Mathlib injective-resolution
import from the lift and independence modules; it is already exported by the
construction's dependencies. No existing module is certified globally pruned.

## Where the brief, the DAG or earlier work was wrong

The existing restriction theorem is stated using `SheafOfModules.overFunctor`, whereas
`FlatBaseChangeOpenChoices` uses `Scheme.Modules.restrictFunctor` on the open subscheme.
Their canonical equivalence and the pinned section identifications are nontrivial
Lean glue; the restricted-choice node records that remaining work explicitly.

The basic properties theorem for `moduleCohomologyFMap` does not expose an equality
with an arbitrary specified choice-data map. The fixed-lift section node therefore
includes the required comparison with the recorded cohomology-map choices, rather
than pretending that basic properties alone prove it.

A scratch edit initially touched the repository copy; it was restored byte-for-byte
from the original before subsequent work. All final source changes are in this sandbox.
LeanSearch returned an internal server error; Lean Finder, Loogle and local searches
worked. Stacks sources were read from the local literature mirror, since this remote
clone does not contain the untracked literature files.

## New nodes

`def-weil-pbc-flat-base-change-resolution-construction`: records the existing actual
Q, C, Beta and class-map constructions in their new acyclic supporting module.

`lem-weil-pbc-flat-base-change-lift`: proved existence of an augmented lift into the
flat pushforward of the target resolution; no sorry added.

`lem-weil-pbc-flat-base-change-resolution-independence`: pairwise comparison of two
valid resolution constructions, following the resolution/homotopy part of step 1.

`lem-weil-pbc-flat-base-change-open-choices-exist`: the full canonical compatibility
of restricted resolutions, unit and sections required by step 2.

`lem-weil-pbc-flat-base-change-resolution-sections`: the section computation for one
fixed augmented lift, following steps 3–5, without existential beta or independence.

The original node's proof and proof_deps now follow the actual Lean combination.

## Second reading by R2

1. **Interfaces: pass.** Compared all six delivered modules with the repository.
   The original theorem signature is byte-for-byte identical. The nine extracted
   declarations, including their docstrings and definition bodies, are one
   byte-identical block. Their public visibility and the original public
   dependencies are retained by the re-export. The extraction has its change
   record. No other existing module is adapted. The current downstream scan
   finds zero transitive importers and the name search finds no external users;
   corrected the unsupported earlier count of 213 in the change record.
2. **Proof and trust: pass, with the three declared holes.** Compiled all six
   modules through lcompile.py. Independently read augmentedLift degree by
   degree: mono extension in degree zero, exactness for degree one, and the
   d-squared equation for the induction. The final proof constructs beta from
   actual resolutions and a lift, then combines independence, compatible
   choices and the fixed-lift section formula. Scratch #print axioms on all
   fourteen public declarations showed only propext, Classical.choice,
   Quot.sound and sorryAx. The latter remains both in the three new statements
   and in upstream outstanding prerequisites (including flat exactness).
   No forbidden declaration, hollow definition, or new arbitrary witness
   chosen from a sorry existence theorem occurs. The private generic helper
   also has a completed body and is included in deliver3's declaration probe.
3. **Split statements: pass.** Independence does not assert existence or the
   section formula; choices asserts neither beta nor its action; the section
   lemma fixes an actual augmented lift and proves just its local action.
   Thus each is a strict part, rather than a renamed original theorem.
   Checked degree zero, zero coefficients, empty opens, and identity-square
   special cases mathematically. Augmentations pin the resolution comparison
   on cohomology; pinned section components rule out arbitrary twists;
   unit_square pins psi through the fully faithful open pushforward. No
   additional hypotheses are required in these cases. Each named hole has a
   source, a complete proof in words, its own module and a matching node.
   Independent Lean Finder, Loogle and local searches found generic ingredients
   but no duplicate of a whole split statement. The existing
   moduleCohomologyFMap_independent does handle the choice-comparison substep:
   added its proof-only import and node dependency to the section lemma.
4. **Route and pruning: pass.** Inspected the parent plan and
   dag/units/sk-thm-p1.json realized statement and four steps. The item is below
   those unit steps; the reduction retains its independence, restriction and
   section-calculation route and changes no unit realization. The completed
   lift uses elementary injective extensions instead of model-category
   lifting. The other holes require substantial comparison glue, so none could
   be responsibly closed in a few minutes. Existing restriction proof code
   in ModuleSectionsAcyclicOfCohomologyVanishing can guide the choices proof;
   recorded it rather than duplicating a new restriction theorem. Enumerated
   every removed parent dependency above. Proof-only imports remain private;
   removed two redundant Mathlib imports. Global module pruning: none claimed.
5. **Nodes: pass after repair.** The existing node changes only lean, proof,
   proof_deps and proof_origin. New nodes have the required provenance, source,
   statement dependencies, searches, unit/chapter and Lean records. Replaced
   flattened new signatures by their literal multiline Lean headers, expanded
   the lift's proof record to its actual degreewise construction, removed stray
   doc-comment terminators from proof text, added targeted second-reader search
   results and the missing cohomology-map-independence dependency.

Second reading changed imports, DAG records, dependency/pruning documentation
and the downstream count; it changed no theorem signature, definition body, or
completed proof. The result is still one original hole decomposed into three,
not a fully proved flat base-change theorem.
