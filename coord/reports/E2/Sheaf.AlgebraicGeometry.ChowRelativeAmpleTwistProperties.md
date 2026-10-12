## What changed

Proved `AlgebraicGeometry.chow_relative_ample_twist_properties` in
`Sheaf.AlgebraicGeometry.ChowRelativeAmpleTwistProperties`, with its original signature,
visibility and docstring unchanged. Added four proved private helpers: preservation of
invertibility under tensor pullback; comparison of successive pullbacks along equal
composites; the projective ampleness theorem over an arbitrary affine scheme; and its
application on an affine open of the base. These helpers contain no holes.

Added proof-only imports `Sheaf.AlgebraicGeometry.ProjectiveAmpleInvertible`,
`Sheaf.AlgebraicGeometry.AmpleIso` and
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`. The latter supplies the proved
integral polynomial twist invertibility instance: removing it was tested and failed
with `failed to synthesize instance ... t.IsInvertible`. All original public imports remain.

Global invertibility follows from the proved source pullback instance, using uniqueness
of left adjoints to compare tensor pullback with Mathlib pullback. Closedness of both
immersions follows directly from properness and the closed-image criterion. Restriction
to an affine open is identified with base change by a cartesian square. The existing
`projective_closedImmersion_ample_invertible` theorem then supplies ampleness over the
section ring of that affine open. Pullback composition and the equality of maps to the
integral model transport both conclusions to the exact modules in the statement.
The Z clause uses an explicitly constructed twist isomorphism, not the holed isomorphism
component. No arbitrary module data is chosen from a mere existence theorem.

The existential global witness `hL` in the unchanged original signature does not occur
in the quantified conclusions. A command-local `linter.unusedVariables.funArgs false`
prevents its unavoidable unused-binder warning without changing the signature; all
private helpers are compiled with the normal linter settings.

Updated the existing node's `proof`, `proof_deps` and `proof_origin` to this route.
No unit realization is bypassed: `sk-thm-picard-coherence` has empty realization lists,
and the original Chow argument (both closed immersions and both relative ampleness
clauses) is retained. Sources checked: [Stacks Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
and [Stacks Tag 01PU](https://stacks.math.columbia.edu/tag/01PU).

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.chow_relative_ample_twist_properties`
(node `lem-pc-chow-relative-ample-twist-properties`).
There are no remaining sorries in the delivered module and no added holes, modules,
axioms or definitions. This is a proof from existing stated dependencies, not a
new decomposition. In particular, the existing dependency
`AlgebraicGeometry.projective_closedImmersion_ample_invertible`
(node `lem-weil-pbc-projective-ample-invertible`) is still sorry in its own module;
this delivery uses it as intended by stage 3 and does not claim the transitive theorem
is axiom-free yet.

Local single-file compilation passed without errors or warnings. The generic helpers
require no Noetherian or nonempty hypotheses: m=0, the empty scheme and empty affine
opens all remain covered by the original affine-base theorem and base-change argument.

## No longer needed

Removed the circular planned proof dependency `lem-pc-chow-relative-ample-twist`
(module `Sheaf.AlgebraicGeometry.ChowRelativeAmpleTwist`): its already completed proof
uses this component, so invoking it would have made an import cycle. This removes a DAG
proof edge; no original Lean import was removed and no global module retirement is
claimed.

The proof also does not need `lem-pc-chow-relative-ample-twist-iso`
(module `Sheaf.AlgebraicGeometry.ChowRelativeAmpleTwistIso`): its isomorphism is constructed
by pullback composition in this delivery. Nor does it import
`Sheaf.AlgebraicGeometry.ChowRelativeAmpleGeometric`
(node `lem-pc-chow-relative-ample-geometric`): the needed closedness conclusions are
proved directly in a few lines, without the unused projectivity conclusions. These
modules may still be needed by other consumers and are not claimed globally pruned.
No other planned proof dependency existed in the original item node.

## Where the brief, the DAG or earlier work was wrong

The item's sole old `proof_deps` edge pointed to its parent
`lem-pc-chow-relative-ample-twist`, whose Lean module imports and applies this item.
That edge was a circular plan, not a usable proof dependency. The parent's own prose
correctly described the geometric and affine-local proof, and the delivery implements
that argument using the existing affine-base theorem. The child docstring's generic
reference to the parent did not spell out the affine-spectrum transport; the updated
DAG and proved helpers now do so. No statement or definition was changed.

The cited literature files are absent on this remote clone; the existing source tags
were read directly on the Stacks website. No new sourced statements were introduced.

## Second reading by E2

1. Interface: PASS. Read the entire delivered module and its diff against the repository.
   Extracted the existing public theorem signature from `theorem` through `:=` and
   checked byte-for-byte equality. Its visibility, docstring, universes, hypotheses,
   existential witnesses and both conclusions are unchanged. The four new helpers
   are private proved theorems; there are no new definitions or interface changes.
   The only node fields changed are `proof`, `proof_deps` and `proof_origin`.
2. Proof and axioms: PASS. Independent local compilation through `lcompile.py` passed
   without errors or warnings (2.8 seconds). A scratch copy printed axioms for all
   four private helpers and the public theorem. Both pullback helpers use only
   `propext`, `Classical.choice` and `Quot.sound`. Both ampleness helpers and the public
   theorem additionally use `sorryAx` through the existing, explicitly reported
   `projective_closedImmersion_ample_invertible` dependency. No direct `sorry` remains,
   no forbidden declaration or attribute occurs, and no data is constructed from
   an arbitrary witness of an unproved existence theorem. The adjunction comparisons
   determine the pullback up to the isomorphism used for transport.
3. Split statements and edge cases: PASS. No statements were split off and no holes
   were added. Checked the affine-spectrum helper, the cartesian restriction square,
   and the direction of every invertibility/ampleness transport. Closed immersion
   of the lift over Z uses separatedness of g, supplied by its properness; it does
   not presume that the unrestricted lift is a base change of j. The affine-open
   lift is a base change, by the displayed morphism-restriction square. For m=0,
   empty schemes, empty affine opens and zero section rings, no nonemptiness or
   nonzero-ring premise is introduced; the affine-base theorem covers those cases.
4. Shorter routes and pruning: PASS. Searched local Lean sources for invertible
   tensor pullback, affine ampleness and relative ampleness, and independently used
   leanfinder with the query "invertible sheaf O(1) on projective space over an affine
   scheme is ample after restriction to a closed subscheme". Results give basic
   affine Proj charts, not a shorter theorem proving this item. The existing bundled
   `invertible_pullback_tensor` includes the same adjunction comparison but would
   bring additional fibre/tensor infrastructure; the private direct comparison is
   appropriate. The three added imports supply the affine-base theorem, ampleness
   transport and integral-twist invertibility, respectively, and are proof-only.
   Original public imports provide the statement's projective space, twist, pullback
   and ampleness definitions. `No longer needed` includes the sole original DAG
   proof dependency (the circular parent). No removed Lean import or globally pruned
   module is claimed. The unit's realization lists are empty; its route is preserved.
   Read the Chow paragraph of [Stacks Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
   and the closed-restriction argument of [Tag 01PU](https://stacks.math.columbia.edu/tag/01PU).
5. DAG agreement: PASS. Read the original and revised nodes, the existing affine-base
   theorem and the unit record. Each revised proof step describes the corresponding
   Lean construction, and `proof_deps` is exactly the union of step `uses`. The original
   statement and Lean record are unchanged. No new node needs validation.

Second reading changed only this report: appended the independent checks, axiom
results and verdicts. No repair to the Lean proof or DAG was needed. Net holes closed
in this delivery: one; holes added: zero. Transitive axiom-freedom remains pending the
existing affine-base dependency, as recorded above.
