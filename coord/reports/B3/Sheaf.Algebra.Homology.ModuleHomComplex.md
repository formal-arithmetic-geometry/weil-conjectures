## What changed

In `Sheaf.Algebra.Homology.ModuleHomComplex`, proved
`CochainComplex.moduleHom_shape` and `CochainComplex.moduleHom_square`.
Both proofs apply `ModuleCat.hom_ext` and `LinearMap.ext`, then use the existing
Mathlib lemmas `CochainComplex.HomComplex.δ_shape` and
`CochainComplex.HomComplex.δ_δ`, respectively. The complex construction,
declaration signatures, visibility, docstrings, and imports are unchanged.

The existing docstrings give precisely this Mathlib route; no route change or
new dependency node is needed. The second reader recorded these proof steps
and their Mathlib origin in the existing definition node. Read the definition node
`def-sc-module-total-hom-complex` and the unit `sk-thm-picard-duality`:
this construction does not replace any realized unit statement or proof step.
Loogle found the exact square-zero lemma; local Mathlib and library searches
confirmed the existing differential API. Both public imports are needed for
the statements and construction.

## Proved and sorry left

Closed two of two original holes:
- `CochainComplex.moduleHom_shape` (node `def-sc-module-total-hom-complex`).
- `CochainComplex.moduleHom_square` (node `def-sc-module-total-hom-complex`).

No sorry remains in the module; no holes or new declarations were added.
The module compiles cleanly through `lcompile.py`.

## No longer needed

None. No imports removed, no planned proof dependency nodes pruned, and no
additional Sheaf modules needed. The existing node has empty `proof_deps`.

## Where the brief, the DAG or earlier work was wrong

None. The two existing docstrings identify the exact reusable Mathlib lemmas.
The proofs work for arbitrary integer degrees, including nonadjacent degrees,
without restrictions on the complexes or the commutative ring.

## Second reading by B3

1. PASS: inspected the complete diff against the repository version. Only
   the two original `sorry` proof bodies changed; every existing signature,
   definition body, visibility, docstring, and import is byte-for-byte unchanged.
   No change record or forced adaptation is needed.
2. PASS: independently compiled the delivered file with `lcompile.py`, with no
   errors or warnings. A scratch copy with `#print axioms` for
   `CochainComplex.moduleHom_shape`, `CochainComplex.moduleHom_square`, and
   `CochainComplex.moduleHomComplex` reports only `propext`, `Classical.choice`,
   and `Quot.sound`. No sorry, forbidden declaration, or hollow definition occurs.
3. PASS: no statements were split off and no declarations were added. Read the
   Mathlib implementations of `δ_shape`, `δ_hom`, and `δ_δ`; the first handles
   every nonadjacent pair and the second handles both nonadjacent and adjacent
   triples. Negative degrees, zero complexes, and the zero ring require no extra
   hypotheses. Repository search confirms no duplicate helper was introduced.
4. PASS: both proofs directly use the shortest Mathlib route, already described
   by the original docstrings. Both public imports provide types, instances, or
   construction data used by the public declarations. No imports or old
   proof-dependency nodes can be pruned. The unit `sk-thm-picard-duality` has
   empty realized statement and step lists; this auxiliary construction neither
   bypasses nor changes a realized unit step.
5. PASS after metadata repair: the definition node names all three declarations.
   Recorded the two extensionality/Mathlib proof steps and concrete construction
   in `proof`, and their Mathlib source in `proof_origin`; `proof_deps` stays
   empty because no other DAG statement is invoked. Other node fields stay
   unchanged.

Second reading changed only DAG proof metadata and this report. No Lean repair
was necessary. Closed holes remain two; added holes remain zero.
