## What changed

Proved `Algebra.fibre_finrank_eq_cotangent_finrank_add_fin_fun` in
`Sheaf.RingTheory.RegularLocalFibreFinrankComparison`, with all existing signatures and
visibility unchanged. The proof implements the existing node's conormal-sequence plan:
separable residue injectivity, exactness and surjectivity, localization of differentials,
tensor cancellation, rank-nullity, and the separating transcendence basis dimension theorem.
The final theorem `Algebra.fibre_finrank_eq_cotangent_finrank_add` keeps its original proof.

Added four proof-only Mathlib imports: `RingTheory.Localization.Submodule` for Noetherian
localization, `FieldTheory.IntermediateField.Adjoin.Algebra` for finite field generation,
`LinearAlgebra.FiniteDimensional.Lemmas` for rank-nullity, and
`RingTheory.AlgebraicIndependent.TranscendenceBasis` for the basis cardinality formula.
All original imports remain used. The proof follows the four existing proof dependencies;
there is no route change, new node, definition, interface change, or forced adaptation.

The local compiler accepted the complete module. All lines have at most 100 characters.
The proof handles r = 0 with the empty transcendence basis, without a positivity assumption;
localization, cotangent identification, and rank-nullity also cover a zero cotangent space.

## Proved and sorry left

Closed the sole original hole:
`Algebra.fibre_finrank_eq_cotangent_finrank_add_fin_fun`
(node `lem-weil-pbc-regular-local-fibre-finrank-add-fin-fun`).
The existing `Algebra.fibre_finrank_eq_cotangent_finrank_add`
(node `lem-weil-pbc-regular-local-fibre-finrank-comparison`) remains proved.

No `sorry` remains in the delivered module, and no hole was added or split off.
This is a proof from existing declarations, as requested for stage 3, rather than a
claim that its entire dependency closure is axiom-free: the existing differential
basis dimension theorem ultimately uses
`KaehlerDifferential.exists_basis_differentials_of_separating_transcendenceBasis_basis`
(node `new-separably-generated-differentials-basis`), which remains a separate library item.

## No longer needed

None. No imports, nodes, or modules were pruned. All four planned proof dependencies are used:
`lem-weil-pbc-jacobi-zariski-differential-maps`,
`lem-weil-pbc-separable-residue-cotangent-injective`,
`lem-weil-pbc-separably-generated-differentials-dimension`, and
`lem-weil-pbc-kahler-differentials-localization`.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error was found. The residue field is definitionally the
residue field of the prime localization, so no separate residue-field comparison lemma
is needed. Mathlib already supplies the conormal sequence and localization equivalence.
The inherited DAG plan is realized unchanged.

## Second reading by J3

1. Compared the delivered module with the repository version. Existing declaration
signatures and visibility are byte-for-byte unchanged; only the first proof, its
docstring, and proof-only imports changed.

2. Compiled the complete delivered module with `lcompile.py`; it succeeds with no
errors or warnings. There are no `sorry`s, axioms, unsafe declarations, or hollow
definitions in the delivered file. The proof depends only on the permitted existing
open theorem in the differential basis dependency.

3. Checked the proof against the node statement and tested the finite function-space
dimension reduction used by the final theorem. The theorem is exactly the stated
conormal decomposition, with no added hypotheses or weakened conclusion; no new
statement or split-off node was introduced.

4. Reviewed the route and imports. The proof uses the four declared proof
dependencies, Mathlib conormal/localization/rank-nullity results, and the existing
separating-transcendence-basis theorem. The four added imports are proof-only and
the old imports remain needed. No shorter route or pruning opportunity was found.

5. Checked the DAG node's Lean declaration, `proof`, `proof_deps`, and
`proof_origin` against the proof. The unit `sk-thm-p1` route and its realized nodes
are preserved.

Changed only the completed proof and its explanatory docstring/imports; no statements,
definitions, nodes, or change records required repair.
