## What changed

Proved `AlgebraicGeometry.Scheme.affine_torsor_component_image_orbit` directly in
`Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorComponentImageOrbit`, keeping its
signature, public imports, definitions and visibility unchanged. Added the proof-only
import `Mathlib.AlgebraicGeometry.PullbackCarrier` and three proved private helpers:
`orbit_split_ι_clopen`, `orbit_section_reconstruction`, and `orbit_deck_cover`.
The first two reuse the connected-summand argument from AffineTorsorSplitAction,
where its reconstruction lemma is private; no shared interface was changed.

The proof shows that the restricted inclusion of the invariant subalgebra is
surjective, using finiteness over an intermediate subalgebra and lying over.
Its projection equations identify q followed by f with the explicit section over H.
For each point of the self-pullback of the puncture, the two maps from its residue
field and the rotation hypothesis put the point on a deck graph. Base-changing the
section's image and applying the splitting identifies these graph images with the
orbit-labelled summands. Their disjointness proves both implications.
The DAG copy now describes this actual proof route. No other module was adapted. The first dry run fetched a newer baseline containing
two directional declarations in this same module. Both declarations and their exact
signatures/docstrings are retained; their proofs now apply the corresponding direction
of the direct equivalence. Their node copies are updated to this acyclic route.

The unchanged signature includes hypotheses `hj`, `hEt`, and `hK` that this shorter
proof does not need. The unused-variable linter is disabled locally for this one
theorem, preserving every original binder; all other compiler checks remain enabled.

## Proved and sorry left

The dispatched version had one hole, in
`AlgebraicGeometry.Scheme.affine_torsor_component_image_orbit`
(node `lem-sbc-affine-torsor-component-image-orbit`), now proved directly.
The newer fetched delivery baseline had already reduced it to these two holes,
both now closed, with signatures unchanged:

- `AlgebraicGeometry.Scheme.affine_torsor_component_image_orbit_forward`
  (node `lem-sbc-affine-torsor-component-image-orbit-forward`).
- `AlgebraicGeometry.Scheme.affine_torsor_component_image_orbit_backward`
  (node `lem-sbc-affine-torsor-component-image-orbit-backward`).
No holes remain in the item's module. No holes were added or split off.
Every private helper is proved. This is a proof, not a decomposition.

The complete module compiles cleanly through lcompile.py in 12.6 seconds.
The dry run printed OK, passing preflight except for the separate second reading;
nothing was pushed. The delivery dry run checks the file,
its unchanged interface, node fields and declaration axioms. The proof handles
ordinary points directly in universe u; it makes no algebraic-closure universe
assumption. For d=0 the label x cannot exist. For G trivial the deck family has
one graph and the disjointness argument selects precisely x. F need only be an
intermediate subalgebra: no argument depends on an unproved stabilizer quotient.

## No longer needed

The direct equivalence proof no longer depends on the forward/backward decomposition
nodes. Those declarations are retained and proved for API compatibility, rather than
removed. No existing module or import is removed: the existing public imports provide the
statement and explicit section/action definitions. Both recorded dependency
modules remain needed for those proved interfaces. The theorem
`affine_torsor_split_point_lifting` itself is not invoked; its module still supplies
`fixedSplitSectionOver` and its compatibility theorem, so it is not claimed pruned.

The planned finite étale deck-graph isomorphism, subgroup orbit polynomial,
universal-surjectivity theorem, extension to algebraic closures and invariance
of open membership under field extension are unnecessary for this proof. None
was a separate dependency node of this item. Exploratory additional imports of
IntegralClosure.Algebra.Basic, Properties and Connected.Clopen were removed after
checking that their needed APIs are already available through the existing imports.
No new work is left for those planned steps.

## Where the brief, the DAG or earlier work was wrong

The old plan cited the label-laws and point-lifting statements for conclusions
they do not state: a deck-graph isomorphism and integrality/surjectivity of an
invariant quotient. These are not obstacles; the delivery proves the needed
weaker geometric fact and the quotient's surjectivity directly. Only existence
in hrot is used for graph coverage. Tag 03SF was read at
https://stacks.math.columbia.edu/tag/03SF; it describes the Galois-cover and
permutation-set framework, while the explicit scheme-point argument above is
written and checked here. The unit record sk-prop-input-spreading has no realized
nodes, and this argument retains the unit's component/orbit route.

No statement, definition, target, or public interface was changed. No tool failure
or disputed statement was found.

## Second reading by F2

1. Compared the delivered module with the repository version. Existing declaration signatures, definitions, visibility, and hypotheses are unchanged; the added import is proof-only. Verdict: pass.

2. Compiled the module with `lcompile.py`; it succeeds without errors or warnings. The three theorem proofs contain no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The direct equivalence proof uses only permitted constructions; the directional declarations apply it without circularity. Verdict: pass.

3. Checked the split-off directional statements and the main node against their Lean declarations and DAG records. Both directional statements are strict implications of the main equivalence, true, and needed for compatibility; no hollow definition or duplicate upstream theorem was introduced. Verdict: pass.

4. Reviewed the proof route and imports. The route uses the explicit residue-field deck coverage, integrality/lying-over, pullback range, and coproduct disjointness arguments. The unit route through the component/orbit construction is retained. No removable import or proof dependency was found beyond the planned proof-only import. Verdict: pass.

5. Checked DAG `proof`, `proof_deps`, `proof_origin`, declaration records, and report consistency. The main node records the direct Mathlib proof and the directional nodes depend only on it; no stale dependency is used by the Lean proof. Verdict: pass.

Changed only the report by adding this second-reading record. No Lean statement, definition, or proof was changed during review.
