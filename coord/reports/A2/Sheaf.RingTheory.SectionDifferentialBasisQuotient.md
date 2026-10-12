## What changed

Proved `Algebra.localized_cotangent_vanishes_of_section_differential_basis` in
`Sheaf.RingTheory.SectionDifferentialBasisQuotient`, with its statement unchanged.
Added a proved private span-induction helper for the conormal generators.

The proof uses `Algebra.jacobiZariski_quotient_smooth`, constructs the unique residue-field
map through the surjective section, and transports the given basis through explicit
tensor-product equivalences. Mathlib's `Module.exists_basis_of_basis_baseChange` lifts
that residue basis over the local ring, using flatness to discharge its tensor-injectivity
hypothesis. The localized conormal map is bijective because its composite with the
surjective generator map is the linear-combination map of this basis. Localized exactness
then proves both subsingleton conclusions.

Added proof imports `Mathlib.RingTheory.Localization.BaseChange`,
`Mathlib.RingTheory.Flat.Stability`, `Mathlib.LinearAlgebra.TensorProduct.Basis`, and
`Mathlib.Algebra.Module.LocalizedModule.Exact`. Updated the existing node's proof,
proof dependencies and proof origin to this route. No public signatures or definitions changed.

The source read was [Stacks Tag 07M7](https://stacks.math.columbia.edu/tag/07M7),
the second paragraph through the two cotangent vanishings. The case n = 0 uses the same
basis-lifting theorem and gives zero modules. If Q is the zero ring, no prime contains
ker τ, so the assertion is vacuous. No nontriviality or nonemptiness hypothesis was added.

## Proved and sorry left

Closed one original hole:
`Algebra.localized_cotangent_vanishes_of_section_differential_basis`
(node `lem-weil-pbc-section-differential-basis-quotient`).

The private helper `Algebra.span_conormal_generators` is also fully proved.
No `sorry` remains in the delivered module; no holes were added or split off.
The proof retains the existing Jacobi–Zariski dependency; its downstream holes, if any,
are existing items, not additions of this delivery.

## No longer needed

Removed proof imports `Mathlib.RingTheory.Spectrum.Prime.FreeLocus` and
`Mathlib.RingTheory.OrzechProperty`.

The route no longer needs `lem-weil-pbc-finite-projective-rank-locally-constant`
(Mathlib's `Module.isLocallyConstant_rankAtStalk` / FreeLocus), or
`lem-weil-pbc-finite-module-surjective-endomorphism-bijective`
(Mathlib's OrzechProperty endomorphism result).
Their proof-dependency edges were removed. Neither was a separate Sheaf module import
in the original item. No claim is made that these nodes are globally unreachable: other
items may still use them. All existing statement imports were retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The DAG's rank and surjective-endomorphism
steps can be replaced by the local residue-basis criterion already in Mathlib. The target's
`hf` is redundant given the supplied factorization τ∘mk = σ, and its binder was retained
unchanged. No new nodes, statement corrections or change records are needed.

## Second reading by A2

1. **Statements unchanged.** Compared the delivered module with the repository version. The public theorem signature and all existing declarations are byte-for-byte unchanged; only proof-only imports, a private helper, and the theorem proof differ. The DAG node statement is unchanged.

2. **Proof validity.** Compiled `Sheaf.RingTheory.SectionDifferentialBasisQuotient` with `lcompile.py`; it compiles cleanly and contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. Axiom inspection reports only the permitted axioms plus `sorryAx` inherited from still-open imported declarations.

3. **Split statements.** No public split-off statements were added. The private span-induction helper is fully proved and has no DAG node requirement. The existing theorem is mathematically unchanged and the proof follows the stated Stacks 07M7 route.

4. **Pruning and route.** The proof uses the local residue-basis lifting route and removes the previously unnecessary FreeLocus and OrzechProperty imports and dependency edges. The unit route remains represented by the Jacobi–Zariski and localization exactness steps; the node's `proof`, `proof_deps`, and `proof_origin` match the implementation.

5. **Dependency and source checks.** Searched the library and Mathlib-oriented search results for an existing theorem with this conclusion; only component lemmas were found. The theorem's hypotheses, including the retained `hf`, are unchanged, and the edge cases `n = 0` and the zero-ring/vacuous prime case are covered by the same argument.

Changes made in this second reading: none to the Lean proof or DAG beyond the already delivered route; this report section records the verification.
