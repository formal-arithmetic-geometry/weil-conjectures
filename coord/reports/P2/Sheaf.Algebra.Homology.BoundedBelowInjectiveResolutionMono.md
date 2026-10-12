## What changed

Replaced the proof of `CochainComplex.exists_mono_quasiIso_injective_boundedBelow`
with the planned specialization of `CochainComplex.exists_mono_quasiIso_in_subcategory`
to the subset of injective objects. Mathlib's zero-injective instance supplies zero
membership. `Injective.under X` and `Injective.ι X`, with their injective and mono
instances, supply the embedding hypothesis. The returned four properties are reordered
into the required conclusion. No signatures, definitions, imports, or DAG route changed. The second reading corrected
a directional typo in the existing node's proof explanation (maps into zero).

## Proved and sorry left

Proved the sole original sorry:
`CochainComplex.exists_mono_quasiIso_injective_boundedBelow`
(node `lem-weil-pbc-complex-injective-resolution-mono`). Local single-file compilation
passes without warnings. No sorry remains in the delivered module and none is added.
The proof uses the existing named theorem
`CochainComplex.exists_mono_quasiIso_in_subcategory`, whose proof remains sorry in
`Sheaf.Algebra.Homology.SubcategoryRightResolution`
(node `lem-weil-pbc-subcategory-right-resolution-05T6`); that module is not changed.

## No longer needed

None. The proof uses the existing proof import
`Sheaf.Algebra.Homology.SubcategoryRightResolution`; no planned node is bypassed.
The existing public Mathlib import is retained to preserve the module's public interface.

## Where the brief, the DAG or earlier work was wrong

The existing node described zero injectivity using a map out of zero; the extension
is the unique map into zero. This explanatory typo is corrected without changing the route.
The cited subcategory theorem has precisely the required hypotheses and conclusion.
The Mathlib search confirmed that its standard mono resolution theorem lowers the bound
by one, so it is not substituted for the same-bound statement here. The specialization
follows the existing node's proof and does not bypass any realized unit step.


## Second reading by P2

1. PASS: Compared the sole delivered Lean module with the repository using `diff`.
   Only the original theorem's proof body changed; the signature, definitions,
   docstring and imports are byte for byte unchanged. No change record is needed.
2. PASS: Local compilation is clean. The file has no `sorry` and none of the forbidden
   declarations or options. A scratch copy with `#print axioms` reports exactly
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The latter comes from
   the existing imported `exists_mono_quasiIso_in_subcategory`, explicitly reported
   above; this delivery closes the local sorry, not that upstream obligation.
3. PASS: No new theorem, definition, node or split-off statement is introduced.
   Checked the imported theorem's zero-membership and embedding hypotheses and all
   four conclusion clauses. Zero complexes and arbitrary integer lower bounds need
   no extra hypothesis: zero is injective and the returned bound is the same `a`.
4. PASS: Repeated the Mathlib search with the launcher grep service and read CM5a's
   two resolution lemmas. The mono lemma lowers the bound; the same-bound lemma
   lacks mono, so neither is a direct shorter proof. Repository search finds the
   used subcategory theorem. Both existing imports are needed: removing CM5a in a
   scratch copy makes the public signature's `Category` unavailable, while the
   private Sheaf import supplies the proof theorem. No proof-only public import
   was added. No old proof dependency is bypassed, so pruning is none. Read
   `dag/units/sk-thm-p1.json` including `realized`; the unit route is retained.
5. PASS after correction: The node's proof, proof dependencies and source origin
   match the specialization to injectives and Mathlib's enough-injectives witnesses.
   Corrected the node's explanatory phrase "map out of zero" to "map into zero":
   injectivity of zero extends a map along a mono by the unique map into zero.
   The statement and dependency set are unchanged; no new-node fields are needed.

Second reading changed only the node's directional typo and this report. The Lean
proof was correct and is retained as written.
