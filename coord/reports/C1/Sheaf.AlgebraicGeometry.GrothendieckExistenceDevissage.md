## What changed

Replaced the sole sorry in
`Sheaf.AlgebraicGeometry.GrothendieckExistenceDevissage` by a compiling Lean reduction.
Its declaration, binders, universe, conclusion, visibility and public imports are unchanged.
The proof converts formal torsion to componentwise torsion using
`coherentFormalModule_annihilated_iff`, constructs the second adic system, obtains a
K-torsion-controlled algebraization triple, recovers compatible I-level isomorphisms,
and assembles them with `NatIso.ofComponents` and `ObjectProperty.isoMk`.

Three new modules isolate strictly separate arguments from Stacks 088A/0889: the
second-adic-system construction (steps 1--3), torsion-controlled easy algebraization
(step 4), and compatible recovery of the original levels (step 5). The construction
retains an isomorphism of double diagrams, the canonical quotient-interchange
projection equation, and the comparison square, so the recovery theorem has explicit
inputs for the uniqueness argument. No definitions or arbitrary chosen witnesses were
added. No target statement or existing intermediate statement was changed.

All four modules compile together in dependency order with lcompile.py. The item
also compiles separately against the sandbox overlay. The updated parent DAG follows
the actual Lean reduction, and each remaining theorem has its own node and sourced
proof in words. New helper imports retain the dependencies of their source arguments.

## Proved and sorry left

Closed: `AlgebraicGeometry.grothendieck_existence_devissage`
(node `lem-weil-pbc-grothendieck-existence-devissage`). No sorry remains in the item.
This is a decomposition, not an axiom-free proof: one upper hole is closed and three
strictly smaller holes are added, so the textual net is -2 before closure accounting.

Added and still sorry:

- `AlgebraicGeometry.grothendieckDevissage_secondAdicSystem`
  (`lem-weil-pbc-devissage-second-adic-system`), in
  `Sheaf.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystem`.
- `AlgebraicGeometry.grothendieckExistenceEasy_torsionTriple`
  (`lem-weil-pbc-easy-algebraization-torsion-triple`), in
  `Sheaf.AlgebraicGeometry.GrothendieckExistenceEasyTorsionTriple`.
- `AlgebraicGeometry.grothendieckDevissage_recoverLevels`
  (`lem-weil-pbc-devissage-recover-levels`), in
  `Sheaf.AlgebraicGeometry.GrothendieckDevissageRecoverLevels`.

Each has exactly `:= by sorry` as its full proof. The third theorem assumes a concrete
second system and a concrete algebraized triple and identifies the levels of that
fixed coherent source; it has neither a thickening-equivalence hypothesis nor an
existential algebraization conclusion. The first theorem constructs only the second
system and comparisons, not the final coherent source. The second involves one ideal
only and has no thickening hypothesis. None is the original statement renamed.

Edge cases checked mathematically before finalizing the signatures: on the empty
scheme all objects are zero; for K=0 the K-system is constant and completion along K
is the identity; for K=1 the component torsion assumptions force alpha to be an
isomorphism and the actual torsion condition forces a to be an isomorphism. For I=0,
recovery identifies the constant original system; for I=1 every original level is zero.
No positive-index construction requires an exponent-zero level. The canonical theta
projection equation prevents choosing a quotient interchange inconsistent with alpha.

## No longer needed

Removed direct proof import `Sheaf.AlgebraicGeometry.ClosedImmersionCoherentEquivalence`:
its direct parent proof dependency
`lem-weil-pbc-closed-immersion-coherent-equivalence` is also removed. Its work remains
needed through `GrothendieckDevissageSecondAdicSystem`; its node is not globally pruned. Removed direct proof import
`Sheaf.AlgebraicGeometry.GrothendieckExistenceEasy` and its direct proof dependency
`lem-weil-pbc-grothendieck-existence-easy`: the delivered route instead uses the
properly torsion-restricted direction-(1) triple theorem. Direction (2) of the old
easy theorem is unnecessary for this item. The underlying affine, formal-gluing and
gluing modules remain needed and are imported by the new triple module.

No further module is claimed globally unreachable. The two original public imports
remain because changing public visibility is outside this proof reduction. The
annihilation-equivalence import is used directly in the Lean proof.

## Where the brief, the DAG or earlier work was wrong

The plan is mathematically the Stacks 088A argument, but the existing dependency
interfaces do not state its second-system construction or final level recovery.
Those are now explicit intermediate statements instead of unexplained glue.

STATEMENT-DISPUTED: `AlgebraicGeometry.grothendieckExistenceEasy` in the existing
`Sheaf.AlgebraicGeometry.GrothendieckExistenceEasy` has an unrestricted uniqueness
clause and omits the condition on the actual coherent map's kernel and cokernel.
Stacks https://stacks.math.columbia.edu/tag/0889 explicitly includes condition (1)(b)
and (2)(b), and uniqueness is among triples satisfying that condition. For the unit
ideal on a nonempty affine scheme, all completions are zero, and the old uniqueness
clause would identify an arbitrary nonzero coherent source mapping to the zero target
with the zero source. This is false. The new direction-(1) theorem includes the
actual torsion condition both on its output and on competing triples. It does not
use the disputed theorem or derive anything from its unrestricted uniqueness.

The existing easy module is not held by this delivery and was not edited. Therefore
its declaration could not be annotated in-place without a non-forced adaptation;
the dispute is recorded here for its holder and in the new theorem's documentation.
The original parent's docstring remains as received; its step 4 implicitly expects
the actual torsion condition that the old dependency fails to provide.

The referenced local `literature/stacks-project/coherent.tex` is absent on this
machine. Read the primary sources directly at
https://stacks.math.columbia.edu/tag/088A and
https://stacks.math.columbia.edu/tag/0889. Semantic searches found no applicable
Mathlib theorem. LeanSearch returned Internal Server Error for all three new queries;
this is recorded as unavailable, not as a no-match result. LeanFinder and grep ran
successfully. Blueprint searches for second adic, torsion triple, and recover levels
found no matching blueprint nodes. No unit-level statement or route was changed.

## New nodes

`lem-weil-pbc-devissage-second-adic-system` records the K-adic reconstruction,
its natural double-diagram isomorphism, canonical quotient interchange, comparison
square, and uniform torsion bound, from the first four paragraphs of Stacks 088A.

`lem-weil-pbc-easy-algebraization-torsion-triple` records precisely the direction
needed from Stacks 0889(1), with the actual-map torsion and properly restricted
uniqueness that the existing Lean statement omits. Its proof uses the original
affine/formal-gluing route, without the unused reverse direction.

`lem-weil-pbc-devissage-recover-levels` records the final paragraph of Stacks 088A,
including naturality of the recovered levels. Naturality is checked using agreement
on completion and away from V(K), then injectivity of the formal-gluing complex.

No change record is needed: existing signatures, definitions and public imports
are untouched, and no existing module was adapted.

## Second reading by C1

1. PASS: independently diffed the delivered item against the repository. Only private
proof imports and the theorem body differ; the existing signature, binders, conclusion,
universe, visibility, docstring and public imports are byte-for-byte unchanged. All
three additional modules are new. There are no definitions or interface adaptations.

2. PASS as a decomposition: compiled all four files in dependency order using
lcompile.py, and independently compiled scratch copies with #print axioms for each
of the four declarations. Every list contains only propext, Classical.choice,
Quot.sound and sorryAx. The latter is expected from the three reported split lemmas
and the still-open upstream annihilation equivalence. Scanned the delivered sources:
exactly the three named theorem holes, no forbidden declarations, and no holed data.
No arbitrary witness is installed as a definition.

3. PASS: independently read Stacks Tags 088A, 0889 and 0888 at their primary URLs.
The three statements separate construction of a second formal system, one-ideal
algebraization with actual-map torsion and restricted uniqueness, and recovery for a
fixed coherent triple. Each is strictly a part of the argument, not a renamed parent.
The quotient-projection equation fixes theta, and the double-diagram naturality and
comparison square provide the needed recovery inputs. Checked empty X, zero and unit
ideals, and positive-level indexing. In particular, unit-ideal uniqueness requires
both actual-map torsion assumptions: they force a and a' to be isomorphisms.
The zero-ideal comparisons reduce to identity completion. Each hole has a sourced
proof docstring and matching node. Independent msearch LeanFinder queries used
"finite module reconstruction", "compatible family of quotients", and "algebraization
of an isogeny", rather than the first reader's phrasing; results were general adic
extensionality or sheaf/scheme isomorphism lemmas, not any of these statements.
Additional Mathlib grep and rg across both Lean roots found no replacement theorem.
ClosedSupportedFormalAlgebraization supplies only individual supported algebraizations,
not the double diagram and torsion bound; the existing easy theorem has the documented
false unrestricted uniqueness clause. None of the remaining geometric holes can be
closed by a short existing-library application.

4. PASS after import repair: the item first applies the upstream annihilation
criterion, then combines the three strict subarguments and assembles a natural
isomorphism via NatIso.ofComponents and ObjectProperty.isoMk. No shorter sound route
was found. Checked all old parent proof dependencies: the closed-immersion and old
easy dependencies are the two removed direct dependencies, both now explicitly listed
above. Closed-immersion work remains below the second-system lemma. No module is
claimed globally pruned. Read dag/units/sk-thm-p1.json realized: this item is below the
unit's realized nodes, and the delivery changes neither the unit nor its route.
The private helper imports retain the sourced plans for their still-open proofs.

5. PASS: opened all four node records alongside their Lean modules. The parent changes
only proof, proof_deps and proof_origin. Its steps match the actual applications and
final diagram assembly. Every node's proof_deps equals the union of its steps' uses.
The new nodes have the required source, proof, searches, split status, created,
blueprint, chapter, unit and Lean records; their statements match their declarations.

Changed by this reading: made the new second-system module's import of
WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian private. Its signature needs
IsNoetherian, already publicly supplied by CoherentFormalModule; the extra module
provides closed-immersion Noetherian results for the planned proof only. Recompiled
the complete set after the change. Clarified that the closed-immersion node is removed
from the parent's direct proof_deps but is still needed transitively. No theorem body,
statement, definition or node required repair. Holes closed remain one; holes added
remain three, a decomposition with textual net -2 and no axiom-free proof claim.
