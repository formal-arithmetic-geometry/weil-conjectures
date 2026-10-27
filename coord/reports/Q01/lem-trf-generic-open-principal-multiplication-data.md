# Stage-1 report: lem-trf-generic-open-principal-multiplication-data

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-generic-open-principal-multiplication-data.json`: statement, four-step proof; not a Mathlib leaf. The statement and statement dependencies are unchanged. The split uses existing nodes exclusively: **0 new nodes, 0 new Mathlib leaves**.
- `citations.json`: one entry for each step/node citation, copying the entire cited statement verbatim so its hypotheses and the implication used are visible.
- `report.md`: this report. `searches.jsonl` was produced by the required search command; `write_split.py` is a sandbox-only writing helper.

## Attachments

None. Searched `lean/WeilConjectures/` for the item's blueprint tag and for generic/principal/multiplication and schematic-density terminology. No declaration states the complete finite-family selection and injective-multiplication conclusion. Hits for multiplication in principal quotients and a smooth trait's generic affine chart concern different statements. The existing affine-density criterion is used as a DAG statement, without claiming that its Lean proof is finished.

## WANTED

None. All sources needed for this split are available locally.

## Findings and source provenance

The item is true as stated. No STATEMENT-DISPUTED correction is needed. Its source is Stacks **0573**, `more-morphisms.tex`, `lemma-scheme-theoretically-dense-generic-fibre`, third proof paragraph. I read that paragraph and its cited algebra lemma **0565**, `algebra.tex`, `lemma-when-injective-covering`, and the sheaf formulation in **056C**, `morphisms.tex`, `example-scheme-theoretic-closure`, and **01RE**, `lemma-characterize-scheme-theoretically-dense`.

Read `dag/chapters/sec-trace-formula.json`, `dag/units/sk-i-curve-zero.json`, the three blueprint levels in SETUP, and the current `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.proof.md`. The inherited ancestor/via provenance points to the generic-density auxiliary branch introduced in an earlier expansion; the latest ancestor text discusses contracting correspondences and no longer contains the generic-density paragraph itself. This split proves the unchanged auxiliary item directly from its explicit Stacks source, preserving its ancestor/via chain and the unit route. It does not assert that Tag 0573 occurs in the latest ancestor text. Whole-blueprint searches for `principal`, `schematically dense`, and `0573` found no blueprint statement equal to this item; `same_as` remains empty. `blueprint_refs.py ancestor` confirmed the inherited ancestor.

The imported proof was empty. I filled it rather than moving its clauses into new nodes. In particular, the proof explains why generators remain generators after tensoring, why the generic open is quasi-compact, and why functions chosen from B (not merely from B_K) suffice. No quasi-compactness of U is used. No SGA source is used.

## Searches and reuse

Retained all inherited Mathlib searches without representing them as this worker's calls. Six additional actual `msearch.py` calls are recorded in `searches.jsonl` and appended verbatim by tool/query in the item: LeanSearch, Loogle, two different LeanFinder phrasings, and two Mathlib greps. The services answered. Returned coverage/dominance/fraction statements do not state the combined item; the grep for schematic-density/generic-principal terminology found no hit. I read the returned signatures and the local `Cover/Open.lean:206` and `AffineScheme.lean:956` candidates: these describe a principal covering of the entire spectrum assuming the unit-ideal condition, rather than the selection inside U with schematic density. No new leaf is claimed.

Searched the whole DAG for 0565, 0573, the principal-basis and Noetherian facts, and the Lean source before deciding on reuse. The existing `lem-trf-affine-schematic-density-criterion` gives precisely the final equivalence, with n=0 allowed. The existing `lem-weil-pbc-spec-localization-away-basic-open` states exactly the principal-open basis needed for the selection. Reused the existing Noetherian algebra, affine quasi-compactness, locally Noetherian definition, and Noetherian open-subscheme statements. There is no new node to search or to split further.

## Not duplicates

No new nodes. All requisite facts are cited through existing nodes, including the previously split affine schematic-density criterion; no copy of that criterion or of the finite-cover conclusion was introduced.

## Review by Q01

I checked B through E against the open node statements and the Stacks text. The item introduces A, B, K, B_K, X, X_K, U, U_K and j_K, and explicitly allows the empty tuple. Its existing notion dependencies supply finite-type algebras, tensor products, affine spectra and open immersions. No new statement-only node, disguised clause, duplicate, or auxiliary Lean definition is being introduced.

**Step 1.** `def-weil-pbc-finite-type-algebra` supplies finite algebra generators, and `def-weil-pbc-module-tensor-product` explicitly states generation by pure tensors. Substituting each b=P(t) into b tensor k gives k P_K(t tensor 1); finite sums show finite generation over K. This is a calculation from the definitions, not an unquoted base-change theorem. K is a field since A is a domain; the two possible ideals of a field are explicitly checked. `lem-weil-pbc-finite-type-algebra-noetherian` assumes only a Noetherian base and a finite-type algebra, both now established, and concludes precisely that B_K is Noetherian. I read its statement and Stacks **00FN**, `algebra.tex`, `lemma-Noetherian-permanence`, not just its title. No Noetherian hypothesis on A or B was introduced.

**Step 2.** `pqf-def-locnoeth` defines local Noetherianity by an affine cover with Noetherian section rings, so the single affine chart X_K qualifies using Step 1. `lem-weil-pbc-affine-scheme-qcqs` states quasi-compactness for every affine scheme, with no nonempty or Noetherian assumption. `lem-weil-pbc-noetherian-open-subscheme-noetherian` requires the ambient scheme to be locally Noetherian and quasi-compact; both have just been verified. Its conclusion explicitly includes quasi-compactness of the open. Thus it can be applied to U_K, even though U need not be quasi-compact. Read the defining **01OV** and **01OW**, `properties.tex`, `definition-noetherian` and `lemma-locally-Noetherian`, and **01OZ**, `lemma-Noetherian-topology`, underlying that existing open-subscheme node; also the affine quasi-compactness source **00E8**, `algebra.tex`, `lemma-quasi-compact`. The cited definition is used only to recognize local Noetherianity, not as a substitute for the open-subscheme theorem.

**Step 3.** `lem-weil-pbc-spec-localization-away-basic-open` clause (i) explicitly states openness and the basis refinement for any point of any open in Spec B. Taking all g with D(g) inside U therefore covers U. For a prime q of B_K, contraction under b -> b tensor 1 gives the equivalence g not in p(q) iff g tensor 1 not in q. The inverse-image identity is proved in the step rather than attributed to a node that only states a basis theorem. Taking inverse images gives the cover of U_K; apply the same openness clause to B_K, then the finite-subcover property obtained in Step 2. Enumerating the finite selected subset is elementary. This step is marked elementary because it is the basis refinement plus the displayed prime-membership calculation and the definition of quasi-compactness, not an additional geometric theorem.

**Step 4.** Read the entire statement of `lem-trf-affine-schematic-density-criterion`. It identifies sheaf injectivity with injectivity of the tuple multiplying by the very same functions, for every commutative ring and every n>=0. Substitute B_K and g_i tensor 1. Step 3 identifies the union with U_K, so the open immersion and its sheaf map are the actual j_K and the map in the hypothesis, not a different dense open or merely topological density. This yields exactly mu_K. Nothing is taken from the cited node's proof. Read **0565**, **056C**, **01RE** as well as the use of them in **0573**; no additional density lemma is silently invoked.

All cited statement quotations are in `citations.json`; proof_deps is exactly the union of uses. The sole non-Mathlib theorem used is in the item's own unit. The other reused theorem nodes are Mathlib leaves; pqf-def-locnoeth is used as a definition. There is no off-route replacement or undeclared theorem tool. Every non-elementary step is below 2000 characters (the entire assembly is 2234 characters), and contains no hidden independent comparison or standard lemma.

**Small cases.** If B_K=0, X_K and U_K are empty and the empty family works: the map 0 -> 0 is injective. This case occurs for A=Z, B=Z/2, K=Q, and U empty. If U_K is empty and B_K is nonzero, the sheaf hypothesis fails on global sections, so no false empty-family conclusion follows. For U=X, choosing 1 alone gives the identity multiplication. For a non-quasi-compact total open, take A=k[x_1,x_2,...], B=A and U=union_i D(x_i); its generic open is Spec K and one nonzero x_i suffices, as our proof allows. For the dual numbers k[e]/(e^2), D(e) is empty and cannot be schematically dense; D(1) works. For k[x,y]/(xy), D(x) alone has a nonzero kernel y, whereas the family (x,y) has zero common annihilator and its principal union satisfies the expected criterion. Hence no reducedness, domain condition on B, or topological-density shortcut has crept in.

The four steps follow the third paragraph of Tag 0573. The new work is the explicit assembly and verification of hypotheses, using the existing DAG instead of adding nodes for elementary steps. I corrected no source statement and left no mathematical subtask of this item's split unfinished.

## Unfinished work

None for stage 1 of this item. Proofs of the existing dependencies retain their own separate DAG tasks.
