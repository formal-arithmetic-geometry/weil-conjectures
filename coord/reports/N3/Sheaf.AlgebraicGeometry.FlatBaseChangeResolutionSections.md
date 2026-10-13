## What changed

Replaced the sole `sorry` of
`AlgebraicGeometry.Scheme.Modules.flatBaseChangeResolutionBeta_sections` by a Lean
proof combining two strictly separate comparisons. The original declaration,
its binders, its conclusion, its visibility, and every existing definition remain
unchanged. The proof factors both section class maps, applies left and right
naturality of the tensor-pullback adjunction, cancels the source resolution
isomorphism, composes the two homology equalities, and evaluates at `xi`.
The private `section_diagram_cancel` proves the associative cancellation in
additive groups; it contains no hole.

Added `FlatBaseChangeSectionComplex` with concrete definitions of the evaluated
complex map, the cocycle class map, and the resolution-to-section-homology map.
These are evaluation and existing comparison maps, without new choices or
postponed data. Its proved `resolutionSectionClass_factor` is the factorization
of the existing `resolutionSectionClass`.

Added `FlatPullbackHomologyAdjointSections` and
`FlatBaseChangeRestrictedLiftHomology`, each with one public intermediate theorem.
The first concerns arbitrary complexes and a flat map, with no resolution or
augmentation. The second identifies maps into homology of section complexes,
with no cohomology-sheaf class map, base-change Beta, or flatness assumption.
They meet at the actual homology map of the same evaluated complex map, rather
than an existential intermediate object.

The item now uses two proof-only imports. Its public import remains identical.
The node records the two-step reduction and the real resolution-isomorphism
cancellation. No existing module besides the held item is adapted, and no
statement or definition change record is required.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.Scheme.Modules.flatBaseChangeResolutionBeta_sections`
(node `lem-weil-pbc-flat-base-change-resolution-sections`). No `sorry` remains
in the item. The private cancellation lemma and the public section factorization
are also proved.

Added exactly two holes, each in its own module with a source, a complete proof
in words, and a matching node:

- `AlgebraicGeometry.Scheme.Modules.flatPullbackHomologyAdjoint_sections`,
  node `lem-weil-pbc-flat-pullback-homology-adjoint-sections`;
- `AlgebraicGeometry.Scheme.Modules.flatBaseChangeRestrictedLift_homology`,
  node `lem-weil-pbc-flat-base-change-restricted-lift-homology`.

This is a decomposition, not a sorry-free proof of the mathematical theorem.
The delivery closes one upper hole and adds two lower holes (net -1 before any
pruning). Each is strictly a part of the previous argument: cocycle class
compatibility with exact pullback, and the resolution computation of an h-map.
Neither states the original conclusion under another name.

Edge cases checked before stating the intermediates: p=0 has zero incoming
boundaries, and both comparisons use the same augmentation/cocycle maps; a zero
complex or zero coefficient gives zero maps; empty opens have zero section
complexes and trivial homology. No exactness of pushforward is assumed. The
restricted-lift comparison uses an injective replacement of the pushed complex,
so it is valid without flatness. Arbitrary augmentation-preserving resolution
identifications give the same homology map by choice independence.

## No longer needed

Removed all six original proof-only imports from the held item:

- `Sheaf.Algebra.Homology.BoundedBelowInjectiveResolutionMono`;
- `Sheaf.AlgebraicGeometry.PushforwardInjectivesSectionsQuasiIso`;
- `Sheaf.AlgebraicGeometry.ModuleCohomologyFMapFunctorial`;
- `Sheaf.Paper.HigherDirectImagePresheaf`;
- `Sheaf.AlgebraicGeometry.FlatModulePullbackExact`;
- `Sheaf.AlgebraicGeometry.ModuleCohomologyFMap`.

The first three remain needed by the restricted-lift argument and are imported
in its new module; their nodes are not pruned. FlatModulePullbackExact and
ModuleCohomologyFMap remain necessary through the existing public definitions,
so deleting their duplicate direct imports is not pruning those modules.

`Sheaf.Paper.HigherDirectImagePresheaf`, node
`lem-weil-pbc-higher-direct-image-presheaf`, is no longer a proof dependency of
this calculation: the existing, explicitly constructed theta suffices, and no
universal property or stalk isomorphism of a higher direct image is used.
Its statement-dependency reference in the existing open-choice definition is
left intact. Global reachability can still retain it for another argument.
No node that realizes a unit statement or a unit proof step is bypassed.

The old node's six proof dependencies are accounted for explicitly:
`def-weil-pbc-module-cohomology-fmap`,
`lem-weil-pbc-complex-injective-resolution-mono`,
`lem-weil-pbc-module-pushforward-injectives-sections-quasi-iso`, and
`lem-weil-pbc-module-cohomology-fmap-functorial` remain in the restricted-lift
comparison; `lem-weil-pbc-flat-module-pullback-exact-pushforward-injective`
remains in the general adjunction comparison. Only
`lem-weil-pbc-higher-direct-image-presheaf` leaves this proof route. This is
local dependency pruning, not a claim that the module leaves every target's
import closure.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The original node bundled
several different compatibilities into one long proof step. Its existing
auxiliary declarations do not directly state either the restricted-lift homology
identity or the adjunction-on-homology section identity; the two new statements
make those missing portions explicit. The original plan's monic replacement,
sections quasi-isomorphism, and choice-independence results remain inputs to the
restricted-lift proof, not obstacles because they contain earlier holes.

Searches used Lean Finder, Loogle, local rg on both library roots and Mathlib,
and LeanSearch (which returned Internal Server Error). Finder's results were
unrelated group-cohomology cocycle formulas; Loogle found generic short-complex
homology comparisons. Local inspection found `moduleCohomologyFMap_independent`
and `ShortComplex.mapHomologyIso_hom_naturality`, but no duplicate of the
required comparisons. The search log is `searches.jsonl` in the sandbox.
The local literature payload is absent on this machine; the sources were read
at [02N7](https://stacks.math.columbia.edu/tag/02N7),
[01FB](https://stacks.math.columbia.edu/tag/01FB),
[01E4](https://stacks.math.columbia.edu/tag/01E4),
[01EZ](https://stacks.math.columbia.edu/tag/01EZ), and
[013K](https://stacks.math.columbia.edu/tag/013K) on the official Stacks website.

Local compiler iterations checked the map-of-complexes commutation equation,
both intermediate signatures, and the complete assembly. All four modules
compile without warnings. The final equalities are composed explicitly rather than rewritten through
the concrete section objects. The accepted proof was restored after timing
experiments that did not improve the compiler limit margin.
The dry run includes axiom probes for every delivered declaration. Its `OK`
result leaves only the independent second reading pending; nothing was pushed.

## New nodes

`def-weil-pbc-flat-base-change-section-complex` records the actual evaluation,
section class, and resolution section homology constructions, together with
their proved factorization. It introduces no new mathematical object chosen
from existence and uses the existing section class and resolution comparisons.

`lem-weil-pbc-flat-pullback-homology-adjoint-sections` isolates the general
cocycle calculation for a flat scheme morphism. It follows Tags 02N7 and 01E4
and the explicit tensor-pullback adjunction unit, independent of the base-change
square or injective resolutions.

`lem-weil-pbc-flat-base-change-restricted-lift-homology` isolates restriction,
augmentation compatibility, and cancellation of the injective replacement's
section homology map in Tag 01FB. It follows Tag 01EZ and the existing
choice-independence theorem. It ends in section-complex homology, before theta
or the higher-direct-image resolution comparisons.

All three nodes carry the parent's chapter, unit, and blueprint ancestry, the
three kinds of search, and the exact Lean signatures. No change records.

## Second reading by N3

1. Compared all four delivered modules against the repository. Only the held
   module exists there; its existing theorem signature, docstring, visibility,
   public import, and all definitions are unchanged byte for byte. The three
   other modules are new. No target or interface repair is involved. Verdict: pass.
2. Read the assembly, including adjunction naturality, the two class-map
   factorizations, the source inverse/hom cancellation, and evaluation at xi.
   All three new modules compiled cleanly. The original assembly timed out;
   explicit equality composition in its final step compiled in 53.6 seconds.
   Exactly the two reported public intermediate theorems contain sorry; none
   occurs in data or a private helper. No forbidden declarations or options
   occur. The delivery dry run passed compilation and the axiom probes for all
   declarations: only propext, Classical.choice, Quot.sound, and transitive
   sorryAx from the reported or existing open dependencies are permitted.
   Verdict: pass.
3. Read the two split statements against FlatBaseChangeOpenChoices, the explicit
   tensor adjunction, sectionCohomologyTheta, ModuleCohomologyFMapData.map,
   moduleCohomologyFMap_independent, and the pushed-injective sections theorem.
   D's augmentation and degreewise components pin both transports; unit_square
   pins psi. The restricted statement does not require exact pushforward or
   flatness: replacement of the pushed target complex and cancellation of its
   sections quasi-isomorphism suffice. The other statement uses flatness only
   for the homology comparison and concerns arbitrary complexes. Both are true,
   needed, and strictly separate parts of the target, with complete docstring
   arguments and matching nodes. Checked p = 0, zero complexes/coefficient,
   empty opens, and different augmentation-preserving comparisons. In degree
   zero use the kernel with zero incoming differential; all maps on zero
   section complexes are zero. Neither intermediate chooses unproved data.
   Read Stacks Tags [01FB](https://stacks.math.columbia.edu/tag/01FB),
   [01E4](https://stacks.math.columbia.edu/tag/01E4), and
   [02N7](https://stacks.math.columbia.edu/tag/02N7).
   Independent searches with alternative wording found general adjunction
   naturality and InjectiveResolution.desc; local rg found the concrete theta
   and choice independence, plus higherDirectImage_resolution_naturality
   (coefficient naturality, not this adjunction or restricted h-map identity).
   No existing theorem supplies either full comparison. Neither remaining hole
   has a few-minute direct closure from those results. Verdict: pass as a
   decomposition, not a sorry-free proof.
4. The route starts with the existing concrete maps and generic adjunction
   naturality; the only unresolved work is the two specific homology identities.
   Public imports serve signatures/definitions, and proof-only imports remain
   private to the item or the restricted-lift proof plan. Accounted for all six
   old proof dependencies under No longer needed. Inspected sk-thm-p1.realized:
   no realized statement or proof step is bypassed by this local reduction.
   Verdict: pass.
5. Checked node statements and dependencies against the Lean assembly and the
   intermediate docstring arguments. The new nodes carry source, chapter,
   unit, blueprint ancestry, creation data, searches, and Lean records.
   Fixed their primary Lean signatures to preserve source whitespace verbatim.
   The existing node changes only the allowed proof fields. Verdict: pass.

Second reading changed the final equality assembly to explicit congrArg₂/trans
composition to avoid rewriting through concrete section objects, repaired the
three new node signature records, and made the old proof-dependency accounting
explicit. No statement, definition, import, or hole count changed. Closed one
upper hole and added two lower holes: net minus one before any global pruning.

Earlier dry run: OK at 92fdbc763c; compilation, every declaration axiom probe,
and stage-3 preflight passed. Review class CODEX because the delivery adds
three modules and their nodes. This second reading approves the decomposition.

The subsequent delivery attempt stopped before pushing because recompilation
exceeded 60 seconds. Second reading additionally set
backward.isDefEq.respectTransparency to true scoped only to the held theorem, retaining
respectTransparency.types false for the scheme/module type identifications,
and added explicit rfl after the sectionwise rewrite in hb'. This avoids
unnecessary unfolding of the concrete maps while preserving all constructions.
The revised theorem compiled cleanly in 48.5 seconds. The final dry run and
push command recheck this exact repaired source and its axiom dependencies.

The elaboration option is scoped to the theorem rather than changed at module
level; this preserves every existing module-level command for the interface
guard. The revised dry run compiled and passed its axiom probes before that
guard requested the narrower scope.
