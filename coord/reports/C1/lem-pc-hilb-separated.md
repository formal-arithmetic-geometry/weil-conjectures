1. files written

- `dag/nodes/sec-picard-framework/lem-pc-hilb-separated.json`: split item; the project theorem is recorded as a Lean candidate but rests on a sorry-backed dependency.
- `dag/nodes/sec-picard-framework/lem-pc-hilb-containment-locus.json`: statement-only `sorry_here` node for `AlgebraicGeometry.exists_idealSheafData_le_ker_iff_comap_le`; Mathlib searches found no match.

2. attachments

- `AlgebraicGeometry.isSeparated_of_representableBy_hilbertPresheaf` belongs to `lem-pc-hilb-separated` as a sorry-free declaration whose own proof rests on `lem-pc-hilb-containment-locus`.

3. WANTED:

None.

4. what was wrong in the node, the blueprint, or the brief

The imported item had no proof and its Lean theorem was not a valid final attachment because the theorem `exists_idealSheafData_le_ker_iff_comap_le` is marked `sorry` in the slopmaster2 map. No duplicate containment-locus node exists in the DAG or blueprint. I added that theorem as the one missing statement-only dependency and made the item proof use it for the two containment loci and their intersection, the diagonal.

5. what I could not finish, and why

The containment-locus node remains `unsplit` because its project declaration is itself `sorry_here`; it is the next stage-1 item to prove.

## Review by C1

I read the item source at the Stacks Project Picard Schemes of Curves, Lemma 44.2.8 (Tag 0B98), and checked the project declaration and body at `WeilConjectures/AlgebraicGeometry/Hilbert/Curve.lean:996-1032`. The declaration has the item hypotheses (`f` separated and a representing `H`) and conclusion (`IsSeparated H.hom`) exactly, but the sorry map shows its containment-locus dependency is sorry-backed. I read that dependency at lines 830-844 and used its full existence-and-base-change statement verbatim in `citations.json`. The proof step uses the two applications to the universal subschemes, the Hilbert-functor representability identification, and the definition of separatedness; the cited DAG statements contain those clauses. I searched the whole DAG and blueprint for the dependency and found no duplicate. I ran LeanFinder, Loogle, grep, and LeanSearch searches for the new node; the first three found no Hilbert containment theorem in Mathlib and LeanSearch was unavailable. The item is marked split, while the missing dependency is explicitly statement-only and `sorry_here`.

## Not duplicates

`lem-pc-hilb-containment-locus` vs `lem-pc-hilb-separated`: the new node is a general existence theorem for a closed subscheme cutting out one containment condition after arbitrary base change; the item concludes that a representing Hilbert scheme is separated by applying that theorem twice and identifying the intersection with the diagonal.

## Second reading by C1

- Item statement: checked against Picard Schemes of Curves, Lemma 44.2.8, label `lemma-hilb-d-separated`, Tag 0B98; verdict: hypotheses and conclusion match.
- Item step 1: checked against the source construction of `Z_1,Z_2` over `H\\times_S H` and the Tag 0B97 containment claim; verdict: valid after making both applications explicit.
- Item step 2: checked against the source diagonal universal property and the closed-diagonal definition of separatedness; verdict: valid with the explicit `def-weil-proper-morphism` citation.
- New node `lem-pc-hilb-containment-locus`: checked against Lemma 44.2.7, label `lemma-hilb-d-of-closed`, Tag 0B97; verdict: closed-immersion, finite-locally-free, and arbitrary-base-change hypotheses and conclusion agree.
- New node form: statement-only and self-contained through scheme, base-change, closed-immersion, and finite-locally-free definition nodes; TeX is escaped once; no proof text or proof dependencies.
- Searches and edge cases: the recorded semantic, Loogle, grep, and LeanSearch searches were checked; no existing Hilbert containment or separatedness theorem was found, and LeanSearch is recorded unavailable. For `d=0`, the empty finite locally free subscheme gives the whole containment locus; over a field, the locus is the expected finite-dimensional vanishing condition.

Changes made: corrected the dependency source from Tag 0B98 to Tag 0B97; replaced the ideal-sheaf paraphrase by the source closed-immersion containment-locus statement; corrected the item source to `literature/stacks-project/pic.tex`; expanded both proof steps and cited the diagonal characterization; updated citation quotes.
