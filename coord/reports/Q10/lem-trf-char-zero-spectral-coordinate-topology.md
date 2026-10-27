# Q10 stage-1 delivery: lem-trf-char-zero-spectral-coordinate-topology

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-char-zero-spectral-coordinate-topology.json`: item split; statement unchanged; four explicit proof steps.
- `dag/nodes/sec-trace-formula/lem-trf-field-trace-minpoly-coefficient.json`: statement; Mathlib leaf, `trace_eq_finrank_mul_minpoly_nextCoeff`, `Mathlib/RingTheory/Trace/Basic.lean:140`.
- `dag/nodes/sec-trace-formula/lem-trf-char-zero-trace-dual-basis.json`: statement; Mathlib leaf, `Module.Basis.traceDual` at `Mathlib/RingTheory/Trace/Basic.lean:553` and `Module.Basis.trace_mul_traceDual` at line 571, with the characteristic-zero separability instances in `Mathlib/FieldTheory/Perfect.lean:306,338`.

The sandbox also contains citations.json and the actual msearch.py searches.jsonl log. Two new nodes, both Mathlib leaves. No Lean files were written or compiled.

## Attachments

None. The blueprint tag and relevant spectral norm, weak stability, weak cartesianness and trace-dual terminology were searched in `lean/WeilConjectures/`. No project declaration proves the whole item without a completeness assumption. The project has unrelated trace-duality declarations and a specific p-adic trace-dual basis in TwistedLatticeBasis.lean; neither states this item. The two new nodes match Mathlib itself, and so are delivered as leaves.

## Wanted literature

WANTED: Bosch–Güntzer–Remmert, Non-Archimedean Analysis, Proposition 3.5.1/4 and Definition 3.5.2/1, printed pp.152–153 (PDF pp.160–161), for lem-trf-char-zero-spectral-coordinate-topology. The file named in the live item's source does not exist in this machine's read-only literature directory. The public URL could not be read by the web tool (document too large). I did not download or write literature or alter its inventory. The original citation is retained, but I do not claim to have read that PDF. The replacement proof is explicitly marked agent-written and uses the Stacks and Mathlib texts described below.

## Findings and changes

The live item was unsplit, and no earlier sandbox node, proof or report existed. There is no released repair note for this item. Its statement is mathematically correct and has been retained verbatim, including the nontrivial absolute value and the absence of completeness. The general finite-dimensional norm-equivalence theorem over complete fields would not justify it. Instead, the first coefficient of the minimal polynomial bounds the field trace, and traces against a dual basis recover the coordinates.

I read the chapter and unit records, and the current `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md`. This is an inherited historical analytic dependency, as the item's existing blueprint.from already explains. The split works below that node level; it makes no change to the current contracting-correspondence unit proof, chapter or unit records.

There are no unfinished proof steps. The only missing source is the original BGR PDF, recorded WANTED above. Sources actually read: Stacks `fields.tex`, Tag 0BIH (`lemma-trace-and-norm-from-minimal-polynomial`), including its proof and preceding characteristic-polynomial argument; Tag 0BIL (`lemma-separable-trace-pairing`), including its hypotheses and the nondegeneracy argument; pinned Mathlib `RingTheory/Trace/Basic.lean:127–142,500–573`; `FieldTheory/Perfect.lean:306,338–341`; and the spectral norm coefficient definitions and incomplete norm interface. The actual proof origin is agent, not a claim to reproduce BGR.

## Searches and duplicate review

Before creating the nodes I searched the whole DAG for trace forms, trace-dual bases, minimal-polynomial trace coefficients, the declaration names, and Tags 0BIH/0BIL. Blueprint searches included `trace pairing`, `spectral norm`, `trace dual`, `minimal polynomial`, `nextCoeff`, `characteristic zero`, `trace`, `weakly cartesian`, `0BIH`, `0BIL`, and `coordinate topology`. The blueprint ancestor tool gives lem-trf-local-term-locality; both new nodes use that ancestor and prepend the item to the inherited via list. No blueprint node states either new fact or the item. The few general `trace pairing` hits are curve duality, rather than finite field-extension duality.

All new-node Mathlib records are copied from searches actually run by the required msearch.py command. For the trace formula, semantic searches returned the exact declaration and Loogle confirmed its type; the grep supplied line 140, which I read. For trace duality, LeanFinder, LeanSearch and Loogle returned traceDual and its pairing formulas; grep supplied lines 553 and 571, which I read together with the characteristic-zero instances. The searches also returned the usual complete-base topology results for the whole item, which do not apply to an incomplete field. The incomplete norm axioms already have a Mathlib leaf, and are reused. No new elementary estimate, topology-equivalence clause or restatement of the item was made a node.

## Not duplicates

lem-trf-field-trace-minpoly-coefficient vs lem-sfb-finite-field-norm-minpoly: both cite 0BIH, but the existing node gives the determinant norm and the constant-coefficient formula; it gives no trace or next-coefficient formula.

lem-trf-field-trace-minpoly-coefficient vs lem-sfb-finite-normal-domain-norm-prime: the existing node concerns restrictions of the determinant norm to a normal coefficient domain and contraction of prime ideals; it gives no field trace coefficient formula.

lem-trf-field-trace-minpoly-coefficient vs lem-a1-finite-field-trace-frobenius-sum: the existing node assumes the top field finite as a set and sums Frobenius powers; the new formula works for every finite-dimensional field extension and computes the trace from the minimal polynomial's next coefficient.

lem-trf-char-zero-trace-dual-basis vs lem-per-integral-trace-dual-lattice: the existing node chooses an integral basis with a nonzero trace determinant and proves sheaf bounds over finite normal domains; it does not supply a trace-dual basis for every prescribed field basis. It is not a generalization of the new leaf.

Additional comparison: lem-sbc-trace-form-nondegenerate-iff-etale-field detects etaleness by nondegeneracy; it does not state the prescribed-basis dual construction. lem-a1-trace-pairing-nondegenerate is restricted to finite fields over their prime fields. Neither supplies this new leaf verbatim or as a direct specialization.

## Review by Q10

I checked the split against delivery-errors B–E with the statements and the sources open. Both new nodes introduce their fields, finiteness, scalar map through an inclusion, the K-linear trace functional and its multiplication-endomorphism convention, and all additional objects. The coefficient-formula leaf introduces the minimal polynomial and K(z), and makes no separability claim. The dual-basis leaf has precisely the characteristic-zero hypothesis needed to infer separability, and asserts a basis and the Kronecker identity, rather than silently using nondegeneracy as if it already stated a chosen dual basis. Its two Mathlib declarations supply exactly those two clauses. The sources have labels/tags and the pinned file lines, and every recorded search was actually run.

Step 1 uses only the existing incomplete-spectral-algebra-norm statement: definiteness, homogeneity and the strong triangle inequality. Iterating that inequality gives the finite-sum estimate, and C is positive because a basis of a field extension has at least one nonzero vector. This is an elementary consequence, not a new norm-equivalence node.

Step 2 uses the same norm node for its explicit coefficient-maximum formula, and the new coefficient-formula leaf for Tr(u)=-(e*1)a_1 and the field-trace convention. The i=1 term of the maximum is |a_1|. I wrote out the induction |n*1|<=1 rather than citing a continuity or boundedness fact not present in a node. Hence |Tr(u)|<=s(u), with no completion, choice of extension of the absolute value, normality, or separability used in this step. The zero element has polynomial T, so that its a_1=0 is included without an empty maximum. The coefficient formula in the cited node is exactly the equality used, with e the degree over K(u), not the potentially different total extension degree.

Step 3 invokes the new dual-basis statement with exactly its hypotheses: the given K has characteristic zero, L/K is finite, and (v_i) is the given basis. The quoted statement supplies Tr(v_i w_j)=delta_ij and explicitly says the trace is K-linear, so expanding the finite sum really gives Tr(z w_j)=a_j. The previous step bounds that trace, and the existing norm node supplies submultiplicativity. This proves every coordinate bound for the very basis in the item. No result about all finite-dimensional vector-space norms over an incomplete field is assumed.

Step 4 just takes a finite maximum and divides by the positive real B=max_j s(w_j). Nonemptiness and nonzero basis vectors prove positivity from the same norm node; the displayed lower bound follows directly. Thus c=1/B and C from step 1 are fixed positive constants independent of the coefficients. In degree one, a basis v and its trace-dual v^(-1) give the expected reciprocal constants. At z=0 all coordinates and both bounds vanish. For an incomplete valued characteristic-zero field (for example Q with the p-adic absolute value), none of the four steps asks for completeness. A purely inseparable positive-characteristic extension would lack the trace-dual basis; it is excluded by the actual characteristic-zero hypothesis, not silently handled.

Every node in every step's uses list was opened and its verbatim statement is copied in citations.json. The proof-dependency list is exactly the union of those lists. Both new nodes are Mathlib leaves with empty proofs and proof dependencies; the substantive upper/lower-bound argument remains in the item. None of the four steps exceeds 2000 characters, and none hides an auxiliary comparison theorem. The statement, chapter route, maintainer metadata, and original import/provenance fields are preserved. I also checked the source-tag overlaps individually above; no claimed duplicate result was borrowed from another node's proof.

## Validation

The required remote `deliver.py Q10 lem-trf-char-zero-spectral-coordinate-topology --no-push` exited successfully and printed `OK (not pushed)` with preflight passed (initial validation commit 82acf8f8cf7). After recording that result in this report, the final dry run is repeated on the final report content, then the direct push is run only after that process exits. The delivery command runs the DAG/split checks on the server; none was run locally.
