## What changed

Proved `Algebra.relativeGlobalCompleteIntersection_baseChange` in
`lean/Sheaf/Paper/RelativeGlobalCompleteIntersectionBaseChange.lean`, preserving its complete
signature and existing docstring. Added the proof-only import
`Mathlib.RingTheory.Extension.Presentation.Basic` and a fully proved private helper
`Algebra.polynomialQuotient_baseChange` for part (a). The second reader added its
source-and-proof docstring.

The proof implements the existing node's five-step plan. Mathlib's naive presentation and
`Presentation.baseChange` identify the quotient by the mapped equations with the tensor
product; the variable formula follows from the presentation's algebra map and `aeval_X`.
For a prime q of the new base, contract to p, install the canonical residue-field map,
and tensor the quotient equivalence. Two `TensorProduct.cancelBaseChange` equivalences
identify the new fibre with the field extension of the old fibre. Nontriviality descends
because tensoring a subsingleton module is subsingleton. The old hypothesis supplies
both c ≤ n and its fibre dimension. The finite base-changed presentation supplies finite
type, and the existing dimension-preservation theorem finishes the dimension equality.

Local compilation succeeded without warnings. The proof works for arbitrary universes,
zero variables or equations, trivial quotient rings and an empty prime spectrum: the
fibre condition is only invoked for nontrivial fibres, and no nonemptiness of a prime
spectrum is assumed.

## Proved and sorry left

Closed the only direct hole: `Algebra.relativeGlobalCompleteIntersection_baseChange`
(node `lem-weil-pbc-relative-global-complete-intersection-base-change`).
No holes remain in this module, and no holes or unfinished statements were added.
The private helper `Algebra.polynomialQuotient_baseChange` is also completely proved.
This is a proof from existing declarations, not a decomposition. It retains the existing
`AlgebraicGeometry.topologicalKrullDim_spec_tensorProduct_of_field_extension` dependency;
this delivery does not claim to close holes reachable through its dependencies.

## No longer needed

None. Both the existing proof import
`Sheaf.AlgebraicGeometry.DimensionPreservedFieldExtension` and the added Mathlib
presentation import are used. All public imports remain required for the unchanged
statement. No nodes, modules or unit steps from the stated proof plan are pruned.
The existing DAG proof, proof dependencies and proof origin continue to describe this
proof, so no node-file changes are needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The presentation-base-change, residue-field and
tensor-cancellation dependencies are Mathlib matches rather than separate Sheaf modules;
their Mathlib implementations suffice. Mathlib already uses the desired tensor-factor
order, so the swaps in the natural-language plan are unnecessary. The finite-type step
is obtained from the finite base-changed presentation, with no additional assumption.


## Second reading by N1

1. **Interface and meaning: pass.** Read the entire repository/sandbox diff and compared the
   existing theorem header through `:= by` byte for byte: identical. No existing declaration,
   definition, visibility, public import or docstring changed. The only added import is plain
   `import Mathlib.RingTheory.Extension.Presentation.Basic`, needed only for the proof.
   Read [00SS (1)](https://stacks.math.columbia.edu/tag/00SS),
   [00SP](https://stacks.math.columbia.edu/tag/00SP), and
   [00P3](https://stacks.math.columbia.edu/tag/00P3), since the local Stacks TeX is absent.
   The arbitrary coefficient map, specified variables/equations, quotient equivalence and its
   variable formula, and preservation of the specified-presentation predicate match the node.
   The original `c ≤ n` requirement on nontrivial fibres is transported unchanged.

2. **Proof and axioms: pass, relative to the existing open dependency.** Independently compiled
   the delivered module cleanly with `lcompile.py` (about five seconds). A scratch copy with
   `#print axioms` gives only `propext`, `Classical.choice`, `Quot.sound` for the private
   quotient helper. The main theorem also has `sorryAx`; an independent print of
   `AlgebraicGeometry.topologicalKrullDim_spec_tensorProduct_of_field_extension` confirms
   that the retained dimension dependency already has it. No direct `sorry`, forbidden axiom
   or implementation command, definition body, or arbitrary witness from an unproved
   existence theorem was added. The presentation quotient equivalence comes from Mathlib's
   proved construction. All lines meet the 100-character convention.

3. **Split statements and small cases: pass.** There are no split-off statements or new holes
   to review or close. The private helper is proved, rather than a restatement left open.
   Its kernel/quotient construction works when `n = 0` or `c = 0`, or when the ideal is the
   unit ideal; the generator condition is vacuous for `Fin 0`. For part (b), an empty prime
   spectrum and a zero new fibre impose no condition. For a nonzero new fibre, the tensor
   equivalence and the subsingleton tensor instance force the old fibre to be nonzero.
   Thus invoking the original presentation condition is justified even when `c > n`:
   that case can only survive vacuously. No injectivity or flatness of `R → R'` is assumed.

4. **Shortest route, imports and unit: pass.** Searched the library for quotient/base-change
   and complete-intersection declarations and independently queried Loogle for
   `Algebra.Presentation.baseChange`. Read Mathlib's `naive`, `baseChange`, kernel equality,
   `quotientEquiv` and `finitePresentation_of_isFinite`. The existing presentation machinery
   already is the short route; `tensorMap_polynomialPresentation` is more specialized and
   would add unnecessary tensor-map infrastructure. Read the unchanged presentation predicate
   and dimension theorem, and checked the two scalar towers using `ResidueField.map_algebraMap`.
   Tensor congruence and two cancellations give exactly `κ(q) ⊗[κ(p)] p.Fiber S`.
   The finite presentation supplies the finite-type hypothesis required by 00P3.
   Both proof imports are used; public imports supply the unchanged signature.
   `## No longer needed` is complete: none of the old proof dependencies is bypassed.
   Read `dag/units/sk-thm-p1.json`, including `realized`: the item is below its realized
   steps, and no unit statement, step or route is replaced.

5. **DAG/Lean agreement: pass.** Read the item's full node and the Lean/Mathlib records of
   all eleven `proof_deps`. Step 1 is the private presentation equivalence; step 2 is
   prime contraction and `ResidueField.map`; step 3 is tensor cancellation, spectrum
   homeomorphism and nontriviality descent; step 4 is the finite base-changed presentation;
   step 5 applies the existing field-extension dimension theorem. The recorded Mathlib
   matches cover these uses. Mathlib's fibre/presentation conventions already put the
   factors in the desired order, so the explanatory swaps require no extra Lean call.
   The existing `proof`, `proof_deps` and document `proof_origin` remain accurate.
   No node or change record is needed; no relevant interface change record was found.

**Changed on second reading:** added the private helper's source-and-proof docstring and
this review. No proof repair, signature change, new hole, new node or pruning was needed.
Closed holes: `Algebra.relativeGlobalCompleteIntersection_baseChange` (one of one).
Added holes: none. Its transitive dimension dependency remains open as noted above.
