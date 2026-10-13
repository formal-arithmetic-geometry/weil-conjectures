## What changed

Proved the assembly in `Sheaf.CategoryTheory.NaturalTruncationCouple` with its existing
statement and universes unchanged. Constructed the raw exact couple explicitly from
`truncation_raw_exact`; obtained its vanishing from `truncation_quadrant_vanishing` and
invertibility of its canonical D comparison from `truncation_abutment_cocone`. Mathlib's
standard t-structure supplies strictly bounded-below representatives, so no further
injective replacement is needed. Built both comparison isomorphisms explicitly and
proved their transport equations by cancellation and functoriality. The zero-bidegree
g square uses a proved equality-transport helper.

Added `Sheaf.CategoryTheory.TruncationCoupleNaturality`, with real definitions
`CategoryTheory.TruncationCouple.abutmentMap`, `singleIso` and `homologyMap`, and one
remaining theorem for raw naturality at two fixed complexes and one derived morphism.
The main theorem genuinely combines this with independent exactness, vanishing,
invertibility and representative comparisons; the new theorem is not its restatement.
Updated the existing node's proof route and added the new node. All public imports of
the original module are retained, preserving its exported interface. New proof imports
are private imports. Both modules compile cleanly in import order with lcompile.py.

## Proved and sorry left

Closed the original hole:
`CategoryTheory.exists_natural_boundedBelow_truncation_couples`
(node `lem-pc-natural-bounded-below-truncation-couples`). No sorry remains in the item.

Added one strictly smaller hole:
`CategoryTheory.TruncationCouple.raw_naturality`
(node `lem-pc-raw-truncation-couple-naturality`). Its proof is exactly `by sorry`.
It asserts only raw map squares for two already fixed complexes, without any exact
couple, vanishing, representative selection, or invertible abutment comparison.
Thus this is a decomposition: one upper hole closed, one lower hole added; net zero.
No private helper or definition contains sorry. Representative choices occur only
inside the existential proof, and are obtained from proved Mathlib results.

## No longer needed

Removed proof imports:
- `Sheaf.CategoryTheory.TruncationHypercohomology`
- `Sheaf.CategoryTheory.TruncationTriangle`
- `Sheaf.CategoryTheory.RightDerivedFunctorTruncationIso`
- `Sheaf.CategoryTheory.DerivedCategory.ShiftIdentification`
- `Sheaf.CategoryTheory.KInjectiveBridge`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`

The revised item does not call `exists_truncationHypercohomology` and does not need
`thm-sp-truncation-e2`, its convergence assertions, stationary cycles/boundaries,
finite page comparisons, filtrations, or alpha colimits. It calls the raw exactness
and quadrant-vanishing results directly instead. The item does not need
`lem-sc-bounded-below-injective-resolution-existence` or choose an injective replacement.
It uses `DerivedCategory.exists_iso_Q_obj_of_isGE` instead. It does not call any theorem
of `lem-sp-shift-identification`, constructing the unbounded shift comparison directly.

The raw naturality node still needs `lem-weil-pbc-truncation-triangle`, and the abutment
cocone still needs `lem-weil-pbc-derived-functor-truncation-iso`. The bridge and unbounded RF
triangulated/shift machinery are still used transitively. Those nodes are not globally
prunable merely because their direct proof imports were removed. No assertion is made
that a removed module is unreachable from every other target. The raw construction
and the new naturality statement have no convergence/filtration imports of their own.
The old dependency `lem-weil-pbc-derived-direct-image-triangulated` (the Plus
functor) is replaced by `lem-pc-right-derived-functor-triangulated` (the unbounded
functor actually used); this is a citation correction, not global pruning.

## Where the brief, the DAG or earlier work was wrong

The old plan bundled the full hypercohomology theorem into a construction needing
only initial exactness and two vanishing clauses. It also unnecessarily requested
injective representatives even though the proved canonical truncation triangle
supports every derived morphism through localization. The simpler route preserves
the unit: `sk-thm-picard-duality` has no realized statement or step tied to this local
construction, and no unit-level node is bypassed.

Mathlib search ran through leanfinder, loogle and grep; leansearch returned HTTP 500
and is recorded as unavailable. Local searches found no existing raw-couple
naturality statement. Blueprint search for truncation found no duplicate: the
existing truncation triangle gives triangle squares, not the bridge-conjugated
bigraded and comparison squares. The new statement is true also for zero objects,
zero/identity morphisms, negative p, and complexes with no fixed common lower bound:
all its maps are induced by the descended truncation and cohomology functors. For
negative p the shift comparison remains an isomorphism (no ordinary natural-indexed
derived functor is used). Arbitrary roofs are covered by localization; no assumption
that c lifts to a complex map was inserted.

Read the actual source pages: Stacks Remark 08J5 (canonical truncation triangles),
Lemma 05TC (vanishing and truncation comparison), and Lemma 015J (hypercohomology
identifications). The raw naturality proof is an agent-written expansion of the
canonical-triangle argument, using the existing project's triangle naturality
interface, rather than an assertion that 015J directly states the new interface.

## New nodes

`lem-pc-raw-truncation-couple-naturality`, at
`dag/nodes/sec-picard-framework/lem-pc-raw-truncation-couple-naturality.json`, states
only step 4's raw naturality subargument, with the canonical inclusion and shift
comparisons specified by real definitions. Its module is
`lean/Sheaf/CategoryTheory/TruncationCoupleNaturality.lean`. Proof steps identify
localization lift/fac, the three canonical triangle squares, homology connecting-map
naturality, and cancellation of the bridge and shift comparisons. The existing node
is updated only in proof, proof_deps and proof_origin. No interface changes,
change records or forced adaptations are required.


## Second reading by E1

1. **Interfaces: pass.** Read the full diff of NaturalTruncationCouple against the
repository. Its existing theorem signature, including universes, instances, the
fixed bound, both vanishing clauses, and both comparison equations, is byte for
byte unchanged (checked by extracting the text before `:= by`). No existing
public definition is changed. The old public imports remain; all added imports
in the item are private. The new module has the required module header and public
section, and its sole public import supplies its definitions and statement.
There are no change records or forced adaptations.

2. **Proof and data: pass as a decomposition.** Both delivered modules compiled
in import order. Read the assembly: exactness comes from truncation_raw_exact;
the chosen existential witnesses there are only zero-composite proofs. The
rawCouple objects and maps are explicitly constructed. Representatives and their
isomorphisms are chosen inside the existential theorem from Mathlib's proved
exists_iso_Q_obj_of_isGE. abutmentMap_isIso identifies the cocone's c with the
explicit abutmentMap using its normalization equations. The D and E equations
are actual functoriality and cancellation calculations. zero_projection_square
handles the non-definitionally-identical zero-bidegree transport. No forbidden
construct or data sorry occurs. Explicit #print axioms checks give only propext,
Classical.choice and Quot.sound for abutmentMap, singleIso and homologyMap; the
main theorem and raw_naturality additionally have sorryAx, as allowed for this
unfinished reduction. The only delivered sorry is raw_naturality.

3. **New statement: pass.** Read the raw_naturality signature, its four-step
natural-language proof, TruncationCouple's actual definitions and the full
naturality clause of DerivedCategory.truncation_triangle. Descended truncation
maps give the alpha square at q+1 and the projection/boundary squares at q;
applying RF.mapTriangle and homologySequenceδ_naturality gives the f square.
The inclusion descends as a natural transformation to the identity functor.
The composite shift isomorphism is natural in H^q, identified by
homologyFunctorFactors. Adjacent bridge isomorphisms cancel in each equation.
This proves the claimed existence for arbitrary derived roofs without assuming
a complex-level lift. It asserts no exactness, vanishing, family of couples or
invertibility of the abutment map, so it is strictly one part of the original
argument, rather than a renamed target. Its all-integer E square is the natural
shift identity; negative p adds no ordinary-derived-functor assumption.
Scratch Lean checks proved its full displayed conjunction independently for
identity and zero morphisms (using identity and zero tD/tE); zero objects follow
from the same formulas. Different lower bounds are harmless: no common bound
is used in this statement. Read Stacks Remark 08J5 and Lemmas 05TC and 015J;
they supply the canonical triangles, inclusion comparison and cohomological
context, while the expanded naturality argument is correctly marked agent-written.
Repeated searches with new queries through leanfinder, loogle and grep found
homologySequenceδ_naturality, localization lifts and shift comparisons, but no
existing theorem with this interface. Also searched the upstream Lean tree and
project Lean/DAG: the exchange-couple theorem varies functors on one sheaf
complex, not arbitrary derived morphisms between two complexes, and is no match.
The scratch special cases do not close the general raw_naturality hole.

4. **Route and pruning: pass.** The assembly uses the shorter raw-exactness route
and does not require hypercohomology convergence, ordinary derived-functor shift
identification or an additional injective replacement. All six removed direct
proof imports and all removed old proof-dependency ids are covered above.
The Plus triangulatedness citation is now also explicitly listed as removed,
replaced by the unbounded result. The new raw naturality hole retains the
canonical triangle subargument; its private TruncationTriangle import makes
that intended proof dependency available. No globally unreachable-module claim
is made. Inspected sk-thm-picard-duality.realized (empty statement realization
and an empty step realization); this local assembly bypasses no realized unit
statement or step and leaves the unit record unchanged.

5. **DAG: pass after repair.** Checked the two node statements against Lean and
their proof_deps against the union of step uses. The old node changes only proof,
proof_deps and proof_origin. The new node has its source, searches, creation,
blueprint ancestry, unit/chapter and verbatim Lean statement. Both nodes formerly
cited lem-weil-pbc-derived-direct-image-triangulated, whose declarations concern
rightDerivedFunctorPlus. The code actually uses the unbounded functor. Replaced
that citation with the existing, upstream-proved
lem-pc-right-derived-functor-triangulated in both nodes; read its two instances
in RightDerivedFunctor/Triangulated.lean. No new node is needed for this fact.

**Changes in this reading:** corrected the Plus/unbounded triangulatedness
citations in both DAG nodes, added the private TruncationTriangle proof import
in the new module, completed the pruning explanation, and recorded this review.
The assembled Lean proof and all theorem signatures were retained. One old hole
is closed and one lower hole is added: decomposition, net zero, no claim of a
fully axiom-free proof of the item.
