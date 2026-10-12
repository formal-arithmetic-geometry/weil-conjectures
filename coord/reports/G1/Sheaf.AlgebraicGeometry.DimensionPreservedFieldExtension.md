## What changed

Proved `AlgebraicGeometry.topologicalKrullDim_spec_tensorProduct_of_field_extension`
in `Sheaf.AlgebraicGeometry.DimensionPreservedFieldExtension`, preserving its signature.
Added the proof-only import `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`.
The tensor-swap homeomorphism reduces to the existing local-dimension theorem in its native
factor order. The supremum formula, pointwise equality and surjectivity then finish the proof.
Updated the theorem docstring to describe the global tensor-swap used by the code.
Updated the existing node's proof and proof_origin to match this implementation; all four
proof dependencies remain. No definition, statement or public import changed.

Search: LeanFinder for dimension preservation under field extension returned algebraic
rank lemmas, with no match. Loogle for `topologicalKrullDim` supplied the homeomorphism
invariance lemma. Grep of Mathlib found no tensor dimension theorem. The source library's
Noether-normalization tensor theorem concerns a fraction field of the base domain, so it
does not apply to an arbitrary field extension. The planned local-dimension route fits.

Validation: local single-file compilation passed without warnings. The proof includes the
zero algebra and allows separate universes for k, K and S. Surjectivity and the empty
supremum formula require no nonempty-spectrum hypothesis.

## Proved and sorry left

Proved the sole original sorry:
`AlgebraicGeometry.topologicalKrullDim_spec_tensorProduct_of_field_extension`
(node `lem-weil-pbc-dimension-preserved-field-extension`).
No sorry remains in the delivered module, and no new sorry or declaration was added.
The existing imported theorems
`AlgebraicGeometry.topologicalKrullDimAt_spec_tensorProduct_field_extension` and
`topologicalKrullDim_eq_iSup_topologicalKrullDimAt` still contain sorry in the library;
they remain the next proof obligations on this route.

## No longer needed

None. Both original proof imports and all four planned dependency nodes remain needed.
A trial explicit import of `Mathlib.LinearAlgebra.Basis.VectorSpace` was removed because
its instances are already available through the retained imports; it was never an original
module import. No original public imports were changed.

## Where the brief, the DAG or earlier work was wrong

No mathematical or statement error found. The DAG planned to transport faithful flatness,
contraction and each local dimension across tensor symmetry. Those transports are unnecessary:
first transport only the global dimension, then use the local theorem and faithfully flat
map directly in their existing factor order. The updated node records this simplification.

## Second reading by G1

1. Compared the delivered Lean module and node with the repository using `diff`.
   Verdict: the existing theorem signature is byte for byte unchanged; no definition,
   public import, or statement changed. The only added import is proof-only.
2. Compiled the module locally successfully without warnings. Inspected its entire proof:
   no sorry remains, no new declaration is present, and none of the forbidden constructs
   occurs. A scratch copy with `#print axioms` reports exactly `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. The last is expected from the two
   existing open imported theorems listed above. Verdict: the original hole is closed
   relative to existing obligations, not yet an axiom-free proof of the result.
3. No statements were split off, no holes added, and no new nodes exist.
   Read the two imported open theorem signatures and their docstring proofs. Their
   hypotheses and conclusions fit the application. Checked the zero algebra (empty
   spectra), identity field extension, and polynomial-algebra cases of the reduction.
   Verdict: no restatement or hidden new obligation.
4. Searched Mathlib again via launcher grep for tensor dimension and supremum-local
   dimension formulas, and searched both library roots with `rg`. Read the upstream
   Noether-normalization tensor theorem: its fraction-field assumption prevents its
   direct use for arbitrary field extensions. The existing local-dimension/supremum
   route is the short available reduction. Both original proof imports are used; the
   added faithfully-flat import supplies surjectivity. All four old dependency nodes
   are used, two through their recorded Mathlib matches. Read the unit `sk-thm-p1`
   and its `realized` record: this below-unit simplification bypasses no unit step.
   Verdict: `No longer needed: None` is complete and the unit route is kept.
5. Compared the updated node's proof steps, proof_deps, and proof_origin with the
   Lean proof and read the two Mathlib dependency matches. Verdict: the metadata
   agrees with the global tensor swap, faithful-flat surjectivity, pointwise equality,
   and supremum reindexing actually used. Other node fields are unchanged.

Second-reading repair: updated only the theorem's proof docstring, which still described
transporting faithful flatness and local dimensions across tensor symmetry. It now
matches the simpler implemented global-dimension transport. No proof code needed repair.
