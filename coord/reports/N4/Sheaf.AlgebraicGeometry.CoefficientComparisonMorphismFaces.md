## What changed

Replaced the renamed copy of the target with the actual restriction and adjunction
naturality argument. The item's existing public signature and public import are
unchanged. Private helpers construct the restriction between supported direct images,
compute its action on sections, and prove naturality of the explicit coefficient
section linear maps. Mathlib's `Adjunction.homEquiv_naturality_right_square` then
transfers the section equality to the composed-adjunction mates. Functoriality and
uniqueness of arrows between opens identify the final support restrictions.

Removed the sandbox's obsolete copy of `CoefficientComparisonConstruction.lean`;
it would have replaced the repository's proved `coefficientSectionAddMap_linear`
with `sorry`. Removed `CoefficientComparisonMorphismFacesAux.lean`, whose remaining
hole merely repeated the target. Updated the item's node proof and dependencies.

## Proved and sorry left

The delivery replaces the original hole in
`AlgebraicGeometry.Scheme.Modules.coefficientComparisonMorphism_faces` with a proof.
No holes are added and no statements are split off. The three private helpers also
contain no holes. The complete module compiles without warnings. `#print axioms` on the target and
all three private helpers shows exactly `propext`, `Classical.choice`, and `Quot.sound`.
Thus one original hole is closed, zero holes are added, and zero statements are split off.

## No longer needed

The old proof dependency `def-pc-module-pullback` is not used: its declaration is the
separate `tensorPullback` construction, whereas this argument uses Mathlib's module
pullback/pushforward adjunction directly. Removed that dependency from the node.
The other original dependencies are used. No original import is removed, and no
module is claimed pruned from the targets' import closure.

The first worker's added import of `CoefficientComparisonMorphismFacesAux` and that
undelivered module are removed; this removes a proposed restatement, not a library
module or a genuine decomposition.

## Where the brief, the DAG or earlier work was wrong

The proposed `coefficientComparisonMorphism_face_naturality` had the same parameters,
let-bound objects, hypotheses and conclusion as `coefficientComparisonMorphism_faces`.
Introducing its final binders did not make it a strictly smaller statement. Its
claimed new node was also absent from the sandbox. The claimed decomposition was
therefore rejected, and the actual section restriction square was proved instead.

The sandbox construction module was stale relative to the repository. It has been
removed from the delivery rather than replacing the upstream linearity proof.

## Second reading by N4

1. Compared every proposed module with its repository version. The target signature
   is byte-identical, including all hypotheses, let bindings and conclusion. Its
   original public import is unchanged. No existing definition or statement is
   altered; the stale construction copy and the proposed auxiliary module are removed.
   Verdict: pass.
2. Read the construction of the support restriction and the three proof calculations.
   The support morphism is constructed explicitly from the restriction unit and
   composition/congruence isomorphisms, with no arbitrary existence witness. Static
   inspection finds no forbidden declaration and no remaining `sorry`. The helper
   calculations and the complete module compile without warnings. A scratch copy
   with `#print axioms` for the target and all three helpers shows only `propext`,
   `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Verdict: pass.
3. Rejected the first worker's split-off statement because it was the entire target
   under another name. No split-off statements remain. Checked empty supports and
   empty or singleton index families: the categorical identities remain valid,
   and in the latter cases no face tuple exists. No extra geometric hypotheses are
   used. Searched Mathlib through Loogle, Lean Finder and grep with new queries,
   and searched the upstream and project sources; used the existing adjunction
   naturality theorem rather than restating it. Verdict: pass.
4. The proof follows the original plan: section restriction naturality, composed
   adjunction mates, then the support identification. The generic calculations are
   below the unit level. Read `sk-thm-picard-coherence.json`; its route and `realized`
   fields are unchanged. The original import is needed by the target signature.
   The unused tensor-pullback DAG dependency is listed above. Verdict: pass.
5. The node has separate steps for the support restriction, the section square and
   adjunction naturality. Its `proof_deps` is exactly the union of the step `uses`,
   and `proof_origin` describes this calculation. All other node fields, including
   its statement and Lean signature, are unchanged. No new node or interface change
   is proposed. Verdict: pass.

Second reading changed the proof from a renamed hole to the actual naturality
calculation, removed the obsolete construction copy and the undelivered restatement,
and corrected the node's proof route and unused dependency.
