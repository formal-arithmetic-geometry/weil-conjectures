## What changed

Proved `Module.basis_iff_basisQuotient_of_nilpotent` in
`Sheaf.RingTheory.BasisIffBasisQuotientOfNilpotent` without changing its signature or visibility.
Added proof-only imports `Mathlib.LinearAlgebra.TensorProduct.Quotient` and
`Mathlib.LinearAlgebra.TensorProduct.Basis`. Retained the existing proved nilpotent Nakayama
lemma for spanning. Updated the theorem docstring and its node's proof, proof dependencies,
and proof origin to the compiled route.

Transport the quotient basis through the tensor/quotient equivalence. Mathlib's
`Module.IsLocalRing.linearIndependent_of_flat` proves independence directly. The span's
inclusion is surjective modulo the maximal ideal, hence surjective by nilpotent Nakayama.
`Basis.mk` combines the two assertions. The reverse direction is scalar extension of a basis.
The index type and all three original universes are unchanged; no finiteness is assumed.

## Proved and sorry left

Closed one hole: `Module.basis_iff_basisQuotient_of_nilpotent`
(node `lem-weil-pbc-local-artinian-basis-when-flat`). Added zero holes. No sorry remains in
any delivered declaration. This is a proof, not a decomposition. The existing dependency
`RingTheory.surjective_of_surjective_mod_nilpotent` is already proved.

## No longer needed

No existing import was removed: the sole proof-only Sheaf import, NakayamaNilpotent, is used.
Pruned proof dependencies `lem-weil-pbc-flat-quotient-tensor-injective` and
`def-weil-pbc-exact-sequence`. Their recorded Mathlib modules
`Mathlib.RingTheory.Flat.Equalizer` and `Mathlib.Algebra.Homology.ExactSequence` need no direct
proof import for this theorem. Mathlib may still import some infrastructure transitively;
this delivery makes no claim that those Mathlib modules leave the global import closure.
The planned free-module kernel, its reduced exact sequence, and the second Nakayama application
are unnecessary. Retained `lem-weil-pbc-tensor-over-quotient-ring`,
`def-weil-pbc-flat-ring-map`, and `lem-weil-pbc-nakayama-nilpotent`.

## Where the brief, the DAG or earlier work was wrong

No statement error. The stage-1 search had already identified the arbitrary-module independence
lemma as a partial shortcut; combining it with the now-proved nilpotent Nakayama lemma closes
the whole theorem. Searches used the prescribed LeanFinder, Loogle, and grep services, plus
rg in both project roots and Mathlib. The local literature checkout contains only metadata,
so the statement and proof of Stacks Tag 051F were read at
https://stacks.math.columbia.edu/tag/051F. The original lemma matches the unchanged signature.
The item is not in `dag/units/sk-thm-p1.json`'s realized statements or proof steps; no unit-level
route is bypassed. Edge cases remain covered: an empty index type forces the span to be zero,
and Nakayama forces M to be zero; when the maximal ideal is zero the quotient is M itself.
No new statement or definition, forced adaptation, or new node was needed.

## Second reading by J1

1. Compared the delivered module with the repository version. The theorem signature and all
   existing declarations are byte-for-byte unchanged; only proof text, proof-only imports, and
   the corresponding DAG proof metadata differ. Verdict: pass.
2. Compiled the module with `lcompile.py` and checked `#print axioms`; it has no `sorry`, `axiom`,
   `unsafe`, or forbidden implementation features, and depends only on `propext`,
   `Classical.choice`, and `Quot.sound`. Verdict: pass.
3. Checked the closed theorem and its edge cases (including empty index type and zero maximal
   ideal). No new statement was introduced, and the theorem is not duplicated in Mathlib or the
   library. Verdict: pass.
4. Verified the proof follows the shortest available route: tensor quotient equivalence,
   `linearIndependent_of_flat`, span mapping, and nilpotent Nakayama; the obsolete kernel and
   exact-sequence dependencies were removed from the node metadata. Verdict: pass.
5. Checked the node's `proof`, `proof_deps`, and `proof_origin` against the Lean proof and
   confirmed the unit route remains represented by its existing realized nodes. Verdict: pass.

Changed only the theorem proof, two proof-only Mathlib imports, and matching DAG metadata; no
new nodes, statements, definitions, or change records were needed.
