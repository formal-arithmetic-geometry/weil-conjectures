## What changed

Replaced the proof hole in `Sheaf.RingTheory.H1CotangentFiniteSubfields` by a complete
finite-support argument, preserving the theorem signature and both public imports.
The theorem has a local `backward.isDefEq.respectTransparency false` elaboration option;
it changes neither the signature nor kernel checking.
For a representative polynomial, adjoin its finite set of variables, descend evaluation
and evaluated derivatives using injectivity of the field inclusion, and apply the
hypothesis to its conormal class. Map the square of the smaller evaluation kernel into
the square of the original kernel to show the original class vanishes.

The proof follows all three steps of the existing node
`lem-weil-pbc-h1-cotangent-finite-subfields`, using Mathlib's polynomial renaming,
`cotangentSpaceBasis_repr_one_tmul`, `Cotangent.mk_eq_zero_iff`, and ideal map/power
lemmas. The existing node's proof and proof dependencies already describe this route,
so no DAG change is necessary. The fixed unit route is preserved.

The source was checked at https://stacks.math.columbia.edu/tag/07BQ (Lemma 10.134.9).
The constant-polynomial case uses the adjoin of the empty variable set, with no
nonemptiness assumption. The same argument includes the zero class and the trivial
extension. No data are chosen from an unproved theorem.

## Proved and sorry left

Closed the sole hole:
`Algebra.subsingleton_h1Cotangent_of_finite_subfields`
(node `lem-weil-pbc-h1-cotangent-finite-subfields`).

Proved 1 of 1 original sorries; added 0 holes; split off 0 statements.
No sorry remains in the module, and no other modules are changed.
The completed module compiles cleanly through `lcompile.py` in approximately 5 seconds.

## No longer needed

None of the original imports, nodes, or modules are pruned. A provisional explicit
import of `Mathlib.Algebra.MvPolynomial.Variables` was removed after confirming that
all needed declarations are already available through the existing public imports.
The delivery adds no imports.

## Where the brief, the DAG or earlier work was wrong

No statement or proof-plan error found. No interface changes or forced adaptations.

## Second reading by B3

1. Compared the delivered module with the repository using `diff -u`. The only
   changes are replacement of the sole `sorry` and a theorem-local elaboration
   option. The existing declaration signature is byte-for-byte unchanged; no
   definition, visibility, or import changed. No change record is required. PASS.
2. Independently compiled the module through `lcompile.py` without errors or
   warnings (5.8 seconds). Compiled a scratch copy with `#print axioms
   Algebra.subsingleton_h1Cotangent_of_finite_subfields`: exactly `propext`,
   `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Read every proof step;
   there are no forbidden declarations, remaining holes, or data definitions.
   Polynomial representatives are obtained from proved Mathlib surjectivity;
   the intermediate field is explicitly constructed by finite adjoin. PASS.
3. No new statements or split-off statements exist, so there are no new holes or
   nodes to validate. Checked the empty-support/constant-polynomial case, zero
   class, and trivial extension: finite adjoin needs no nonempty support, both
   evaluation and derivative descent use the injective field inclusion, and
   square-ideal transport remains valid in these cases. PASS.
4. Read the Mathlib conormal and first-homology definitions and searched Mathlib,
   upstream, and `lean/Sheaf` for a shorter existing reduction. An independent
   LeanFinder search using “Vanishing kernel of the conormal differential descends
   to a finitely generated intermediate field by finite polynomial support”
   found related finite-generation lemmas, not this reduction; local searches
   found no union/colimit theorem replacing the argument. Both public imports
   provide notions in the signature (`IntermediateField`/`FG`, `H1Cotangent`).
   Both old proof dependencies are used through their Mathlib realizations;
   none is pruned. Read `dag/units/sk-thm-p1.json`: this node is below its realized
   steps, and the proof preserves its existing route. PASS.
5. Read the item's node and both dependency nodes. Its three planned steps agree
   with the Lean proof: finite support, descent of evaluation and derivatives,
   and transport of the squared evaluation kernel. The existing `proof`,
   `proof_deps`, and document `proof_origin` need no edits. Independently checked
   [Stacks Tag 07BQ](https://stacks.math.columbia.edu/tag/07BQ): its canonical
   presentation/filtered-colimit argument supports this finite-support
   specialization. PASS.

Second-reading changes: clarified the existing local elaboration option in
`What changed` and added this review record. No Lean or DAG repair was needed.
Closed 1 original hole, added 0 holes, split off 0 statements; pruned none.
