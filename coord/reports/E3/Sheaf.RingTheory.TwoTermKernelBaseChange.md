## What changed

Proved both existing declarations in `Sheaf.RingTheory.TwoTermKernelBaseChange`
without changing their signatures or definitions. The module now proves the
canonical kernel map is bijective by applying the existing Tor long exact
sequence to the two image-factorization short exact sequences and the existing
free dimension-shifting theorem. It constructs the map explicitly with
`LinearMap.codRestrict` and the equivalence with `LinearEquiv.ofBijective`.
The algebra clause follows from the first theorem by tensor symmetry and
`LinearMap.tensorKer_coe`. Added the proof-only import
`Mathlib.Algebra.Homology.ShortComplex.ModuleCat`.

Removed the first worker's unlanded `TwoTermKernelBaseChangeCore` module and
its auxiliary node: bijectivity of the canonical map under exactly the original
hypotheses was a restatement of the original problem, not a smaller proof step.

## Proved and sorry left

Closed the original holes in:
- `LinearMap.exists_twoTermKernelBaseChange_equiv`;
- `LinearMap.bijective_twoTermKernelBaseChange_algebra`.

Both belong to `lem-weil-pbc-two-term-complex-kernel-base-change`.
No local holes remain and no holes are added. This is two local holes closed,
zero split off; it is not a decomposition into new holes. The proofs still
transitively depend on existing open declarations, including
`CategoryTheory.tor_dimension_shift_free`, through the existing proof imports.
`#print axioms` for both declarations returns only `propext`, `Classical.choice`,
`Quot.sound`, and the permitted upstream `sorryAx`.

## No longer needed

No repository proof dependency or imported module is pruned. Both original
Sheaf proof imports are used. Removed only the unlanded core-module import,
module, and node `aux-weil-pbc-two-term-kernel-map-bijective` from the sandbox.
All five original public Mathlib imports support the existing signatures:
ModuleCat's abelian and projective-resolution instances, its tensor structure,
Tor', and the canonical algebra-linear `tensorKer` map.

## Where the brief, the DAG or earlier work was wrong

The first worker's core bijectivity claim carried the same mathematical
content as the original equivalence with its coercion formula. Its proof
merely postponed the entire exact-sequence argument. The second reading
replaced this with the actual reduction through the two existing Tor lemmas.
The original DAG proof plan was correct and is restored; the final step now
also records the concrete tensor-symmetry argument for the algebra clause.

## New nodes

None. No interface changes and no change records.

## Second reading by E3

1. Compared the delivered module with the repository using `diff` and the
   declaration parser. Both existing signatures are byte for byte unchanged;
   no existing declaration or definition was removed or altered. No changes
   outside this sandbox were made by the reader.
2. Compiled the first worker's two-file set and the repaired single module
   using `lcompile.py`. The repaired module compiles without errors or warnings
   and contains no `sorry`, axiom, unsafe, opaque, implemented_by, extern, or
   hollow definition. A scratch copy with `#print axioms` verifies both results
   have only the three standard axioms and upstream `sorryAx`. The canonical
   map is constructed explicitly; no object is chosen from an open existence
   theorem. The Tor connecting maps are used only inside a proposition proof.
3. Rejected and removed the proposed split-off theorem as a restatement. No
   new statement remains to audit. Checked the exact-sequence argument also
   for zero modules, the zero map, and a surjective map: the image sequences
   and Tor hypotheses give exactly the required kernel comparison. Searched
   the library and Mathlib with different terms; the existing Tor lemmas and
   tensor-commutation identities suffice. Recorded launcher searches include
   grep for rTensor_comm/tensorKer_coe/exact_subtype_ker_map and Loogle for
   LinearMap.tensorKer_coe. Flatness-based tensorKerEquiv cannot be applied
   under these hypotheses because C need not be flat.
4. Read the proof from the target downward. The repaired argument uses the
   original planned Tor dependencies rather than a new equivalent hole.
   The added ModuleCat short-complex import is proof-only; original public
   imports support signatures. No old proof dependency is unused.
   Read `dag/units/sk-thm-p1.json`: none of its statement or step realizers is
   bypassed, and the original unit route is retained.
5. Restored the original node's proof and proof_deps; expanded only its final
   proof step to describe the algebra-clause transport. Its dependencies are
   precisely Tor', the low-degree Tor sequence, and free dimension shifting.
   The unchanged document proof_origin still matches the five-step argument.

Changes by the second reader: removed the tautological core split and its node;
proved both original holes directly from the existing proof dependencies;
added one proof-only Mathlib import; repaired the DAG and this report.
