## What changed

Completed and repaired the earlier sandbox attempt. The existing signature and docstring of
`AlgebraicGeometry.affineAlternatingCech_resolution_core` are unchanged. Its proof now combines
an augmented natural-degree complex with a proved base-change acyclicity lemma. It extends
by zero, passes to the homotopy category, localizes the two augmentations, proves both derived
units using the bounded-below acyclic-unit criterion and its compatibility with the unbounded
right derived functor, and supplies the integer-degree product presentations.

New modules:
- `Sheaf.AlgebraicGeometry.AffineAlternatingCechAugmentedConstruction`: the remaining
  construction, local contraction, and affine section comparison, stated as one theorem.
- `Sheaf.AlgebraicGeometry.AffineOpenPushforwardPullbackAcyclic`: proved using affine
  pushforward base change, the explicit restriction/pullback comparison, and the existing
  affine-open direct-image acyclicity theorem. No cover or derived complex enters this lemma.

The private helper `AlgebraicGeometry.unit_isIso_of_acyclic` proves the passage from the
bounded-below acyclic-unit criterion to the precise unbounded unit in the item. No additional
hole is used for this passage. Updated the parent node to match the actual proof and added
nodes for both new modules. No existing definition, public signature, visibility or instance
was changed. No other holder's module was adapted.

## Proved and sorry left

Closed the sole direct hole in `AlgebraicGeometry.affineAlternatingCech_resolution_core`
(node `lem-pc-s3-affine-alternating-cech-resolution-core`). The module has no direct `sorry`.
This is a decomposition, not a claim of a final axiom-free resolution: one direct hole is
closed and one strictly smaller construction hole is added, so the net direct hole count is
zero. The combining Lean proof is complete.

Also proved `AlgebraicGeometry.affine_open_pushforward_pullback_rightAcyclic`
(node `lem-pc-s3-affine-open-pushforward-pullback-acyclic`) and the private
`AlgebraicGeometry.unit_isIso_of_acyclic`, with no new holes.

The only `sorry` left anywhere in the delivery is
`AlgebraicGeometry.exists_affineAlternatingCech_augmented_construction`
(node `lem-pc-s3-affine-alternating-cech-augmented-construction`). Its entire proof is
`:= by sorry`. It asserts the sheaf complex, the two ordinary quasi-isomorphisms,
its affine section-model comparison and finite affine-open term presentations. It contains
neither of the derived-unit assertions; those are proved in the parent from termwise
acyclicity. The construction is used as an existential witness within a theorem, never to
choose data in a definition. Its docstring and node give the signed face cancellation,
local insertion homotopy, behavior under additive pullback, and tilde comparison.

Edge cases checked in the mathematical argument: an empty cover implies X is empty;
empty increasing-tuple types use n=0; the zero module, repeated or empty opens, and
non-flat g are allowed. The parent handles negative integer degrees explicitly with the
zero-object/empty-product isomorphism. Finite products are preserved by additive pullback
because they are finite biproducts; no general exactness of tensor pullback is assumed.

The three delivered modules compile together through lcompile.py, without non-sorry warnings.

## No longer needed

Removed the parent's direct proof import
`Sheaf.AlgebraicGeometry.ModulePullbackAffineSections` and its planned proof dependency
`lem-weil-pbc-module-pullback-affine-sections`. The remaining affine section comparison uses
the tilde-Gamma counit and naturality rather than the tensor-sections formula. This is pruning
of this node's direct route, not a claim that the module disappears from all targets' imports.

Removed the parent's direct proof import `Sheaf.AlgebraicGeometry.AffinePushforwardBaseChange`
and its direct dependency `lem-weil-pbc-affine-pushforward-base-change`; both remain needed
inside the proved `AffineOpenPushforwardPullbackAcyclic` helper, so they are relocated,
not globally pruned. All other original imports are retained. The old dependency
`def-pc-affine-alternating-cech-model` is no longer a direct proof dependency: it remains
a statement dependency and is used by the new construction node. Its public import stays. The new modules use
`TensorPullback` and `RingedSpaceDerivedDirectImage` directly instead of importing
`DerivedBaseChangeUnitCompatibility` for their statements. The original public imports
of the item are preserved. No unit statement or realized unit step is bypassed.

Second reading additionally removed the proof-only import
`Sheaf.AlgebraicGeometry.TensorPullbackAdjunction` from the new acyclicity module and
`Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives` from the parent.
Both were redundant; their required declarations and instances are already supplied
by the retained imports. Neither removal prunes a module globally.

## Where the brief, the DAG or earlier work was wrong

The previous sandbox attempt had no node files or report and did not compile. Its pulled-back
acyclicity proof needed an explicit `MorphismProperty.pullback_fst` proof of affineness;
`morphismRestrict_ι` and `isPullback_morphismRestrict` are in `AlgebraicGeometry`, not
`AlgebraicGeometry.Scheme`; the two `pullbackComp` comparisons were oriented backwards.
These are repaired. Replacing unnecessarily large imports also exposed the need for public
quasi-coherence and enough-injectives imports in the new acyclicity module, now supplied.

The node's original one-step plan hid the natural-to-integer extension, single-complex
identification, finite-product acyclicity, and bounded/unbounded unit transports. These
steps are now actual Lean proofs. Existing `CechSheafConstruction` and `CechSheafResolution`
use all tuples, including repeats, whereas `affineAlternatingCechModel` uses strictly
increasing tuples. Their signatures give no alternating sheaf representative or preservation
of its augmentation after arbitrary additive pullback. They therefore cannot simply be
substituted for the remaining construction theorem. Mathlib search found general
Mayer-Vietoris results, but no theorem closing this construction. LeanSearch was unavailable
and is recorded as unavailable in the search log and new nodes.

Stacks Tag 02KH is flat base change: its comparison of Cech complexes precedes the use of
flatness on cohomology. The new construction docstring specifies that portion of the proof;
the arbitrary-pullback quasi-isomorphism instead follows from the locally split contraction.
The affine-open base-change helper uses Tag 02KG, which permits arbitrary base change.
The parent node's inherited blueprint.from points at the intermediate exchange-resolution
node rather than the imported blueprint ancestor; the new nodes use the ancestor
`lem-pc-rf-base-change-flat-module` recorded by that exchange-resolution node. The ancestor
lookup script cannot follow module names in created.item. The inherited parent blueprint
field is outside this delivery's owned fields and is reported for bookkeeping repair.
An additional read-only DAG closure check found the inherited two-node cycle
`lem-weil-pbc-sheaf-algebraic-structures-objects` ->
`lem-weil-pbc-sheaf-algebraic-structures-abelian-component` -> the first node.
Both edges are present in the unchanged repository nodes; neither endpoint is modified
by this delivery. Reported here for the maintainer rather than changed outside this item.
The Lean import graph and delivery preflight pass.
No mathematical dispute or change to a target statement is proposed.

## New nodes

`lem-pc-s3-affine-alternating-cech-augmented-construction`, in
`dag/nodes/sec-picard-framework/`, states the remaining strictly smaller augmented sheaf
construction. Its module contains the single named construction hole. The natural-language
proof expands the parent construction and the pre-cohomology comparison of Tag 02KH,
with the increasing-tuple signs of Tag 01FM and the affine comparison of Tag 02KG.

`lem-pc-s3-affine-open-pushforward-pullback-acyclic`, in the same directory, states a
single affine-open termwise acyclicity fact after arbitrary base change. Its module proves
it from the existing affine base-change and affine-open acyclicity declarations. Three
kinds of actual Mathlib searches are recorded for each node; blueprint search found no
exact statement. The two general imported blueprint Cech nodes were read and do not supply
the increasing-tuple/pullback interface needed here. No change record is required: no
existing interface changes, and there are no forced adaptations.


## Second reading by Q2

1. Compared every delivered module against the repository. The parent is the only
   existing module; its existing theorem signature and docstring are byte-for-byte
   unchanged. The new modules add the two reported declarations. The existing node
   changes only proof, proof_deps and proof_origin. There are no definition changes,
   changed public imports, forced adaptations, or change records. Verdict: pass.
2. Independently compiled all three modules with lcompile.py and inspected their full
   proofs. Exactly one named theorem contains sorry: the reported augmented construction.
   No forbidden declaration form or data hole occurs. Scratch-copy #print axioms checks
   cover both public proved theorems, the construction, and the private unit helper;
   the private unit helper and affine-open pullback acyclicity theorem use only
   propext, Classical.choice and Quot.sound. The parent and the remaining construction
   also use sorryAx, exactly as expected from the reported construction hole. The chosen
   zero object in the parent comes from the genuine HasZeroObject instance, and the
   construction witness is eliminated inside a theorem, never installed as a definition.
   Verdict: pass, a decomposition rather than an axiom-free finished resolution.
3. Read the construction statement, docstring and node. Checked r=0 (empty scheme),
   r=1 (the sole open is top), degrees above the number of cover members, repeated
   and empty opens, the zero module, and non-flat base change. On a cover member,
   signed insertion contracts the augmented increasing-tuple complex; applying additive
   pullback preserves that homotopy identity. Finite affine intersections and the
   tilde-Gamma comparison give its precise affine section model. The construction
   omits both derived units, which the parent actually proves, so it is a strictly
   smaller part of the argument rather than a renamed copy of the item. Independent
   leanfinder, loogle and grep searches used different queries; read the existing
   CechSheafConstruction, CechSheafResolution, AlternatingCechRestrictionHomotopy and
   FiniteAffineCechModelComparison interfaces. They provide all-tuple constructions,
   additive-group comparisons or homology comparisons, not the required increasing-tuple
   module-sheaf construction with its two augmentations and complex isomorphism.
   Closing this remaining construction is substantial work, not a short application.
   Verified Stacks Tags 01FM, 02KG and the pre-cohomology comparison in 02KH. Verdict: pass.
4. Followed the proof from the parent: explicit zero-extension and localization,
   finite-product acyclicity on both schemes, then bounded/unbounded unit compatibility.
   The affine-open helper is a real proved reduction using the canonical base-change
   isomorphism and restriction/pullback comparisons. No shorter complete route was found.
   Reviewed all old proof_deps; the pruning section now accounts also for the model
   dependency relocated to the construction. The unit record has realized statement=[]
   and steps=[[]]; this delivery changes no realized unit node or route. Verdict: pass.
5. Compared every node's Lean statement with its source signature after whitespace
   normalization, checked every dependency exists, and read each proof step against
   the actual Lean argument. New nodes have source, searches, creation, blueprint,
   chapter/unit and Lean records. Parent changes stay within owned proof fields.
   The existing unrelated DAG cycle and inherited blueprint bookkeeping issue remain
   reported above. Verdict: pass.

Second-reading repairs: removed the unused proof import TensorPullbackAdjunction from
AffineOpenPushforwardPullbackAcyclic (the proof uses nonempty_tensorPullbackAdjunction
from TensorPullback), and the redundant EnoughInjectives import from the parent
(the new acyclicity module already publicly supplies those instances). Completed
No longer needed with the old model proof-dependency relocation. No theorem body,
signature, definition, docstring, node statement or unit route was rewritten.
