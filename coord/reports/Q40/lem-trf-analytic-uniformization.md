# Q40 stage-1 delivery: lem-trf-analytic-uniformization

## Files written

- dag/nodes/sec-trace-formula/lem-trf-analytic-uniformization.json: existing statement, now split in five steps; statement unchanged.
- dag/nodes/sec-trace-formula/lem-trf-analytic-type-alternatives.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-analytic-type23-stability.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-analytic-immediate-rationality.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-analytic-parameter-finiteness.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-analytic-close-embedding-degree.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-analytic-etale-residue-degree.json: statement, unsplit; no Mathlib match.

## Attachments

None. Searched the project WeilConjectures source by the exact blueprint tag, analytic uniformization, unramified generators, Temkin, and perturbation. The power-series perturbation declarations concern a different problem. No exact sorry-free declaration was found. No Lean was written or compiled.

## Literature wanted

WANTED: Temkin, Stable modification of relative curves, arXiv:0707.3953v3, archival PDF literature/temkin-stable-modification-arXiv-0707.3953v3.pdf, for the item and all six new nodes.

The read clone does not contain that PDF. I read the primary author PDF at https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf and checked the arXiv v3 online. Extracted text is retained in the sandbox as temkin.txt. No literature or launcher file was changed. Because the archival document is absent, proof_origin.by is agent, as the brief requires. This is not a claim that the paper was locally archived. There is no Stacks tag for these analytic uniformization and stability theorems; sources give the exact theorem/lemma and printed page. No SGA source was used.

## Corrections and limitations

The imported item had no proof. Its statement is valid also for E=k, whereas the terminology of a one-dimensional analytic field in section 6 excludes this case. I supplied the degree-one case separately, without changing its hypotheses. In the nontrivial case the given y cannot belong to k, since E would then be a finite extension of algebraically closed k.

The latest blueprint ancestor lem-trf-local-term-locality now uses Varshavsky's contracting-correspondence proof. This item belongs to the already-created historical Temkin branch named by blueprint.from.place. I retained that provenance and do not claim that the current blueprint invokes Temkin. Neither chapter nor unit route was changed.

The immediate-field node has stronger conclusion E=k(z)^wedge and strictly narrower hypotheses than the item. The stability node concerns every finite extension and a degree formula, not existence of a parameter. The other nodes are independently meaningful classification, finiteness, degree-invariance and ramification results. They do not reproduce the item's three clauses. All six are statement-only and deliberately not recursively split.

Nothing needed for this one-level split remains unfinished. The six new statements remain future stage-1 items.

## Searches and Not duplicates

Before creating the nodes I searched the whole DAG for analytic fields, topologically generated fields, immediate extensions, unramified generators, Cartesian extensions, stability, close embeddings and residue-degree criteria. The whole imported blueprint was searched using blueprint_refs.py for analytic uniformization, unramified, stable analytic, orthogonal, immediate, residue degree and valuation. No blueprint node states any new input. All new ids were checked for absence before writing.

Existing lem-trf-abhyankar-inequality is only the finitely generated algebraic inequality; it does not state the analytic type classification, equality of value groups, cyclic coordinate or separating residue coordinate. Existing lem-trf-valued-decompletion-etale compares finite extensions before and after completion; it does not give a degree criterion or finiteness after changing the topological parameter. Existing lem-trf-sepclosed-rank-one-completion concerns the base field's completion and residue field, not the one-dimensional analytic extension. Existing lem-trf-composed-valuation-etale handles composition of valuations of finite height, not analytic stability or parameter perturbation. None replaces these new inputs.

## Not duplicates

- lem-trf-analytic-type-alternatives vs lem-trf-abhyankar-inequality: the existing node is an inequality for finitely generated field extensions; the new node gives the analytic alternatives, residue finite generation and separating parameter, and the cyclic value coordinate after finite analytic extension.
- lem-trf-analytic-parameter-finiteness vs lem-trf-valued-decompletion-etale: changing the nonconstant analytic parameter is not completion of an already finite rational-field extension.
- lem-trf-analytic-etale-residue-degree vs lem-trf-valued-decompletion-etale: the new node detects etaleness using residue separability and equality of field degrees, rather than a comparison to completion.
- lem-trf-analytic-immediate-rationality vs lem-trf-analytic-uniformization: this is the type-4 case with the stronger conclusion of topological generation; it is combined with classification and the separate residue/value cases, rather than carrying the whole item.

For each new node I ran msearch.py with its own statement in mind: LeanFinder, Loogle, Mathlib grep and LeanSearch, then a second semantic phrasing. All services returned successfully. Exact queries and full returned hits are preserved in the node records, searches.jsonl and per-query text files. Hits on local fields require local compactness or discrete valuation; neither is assumed here. Laurent-series completions concern their fixed adic valuation. Number-field ramification results require Dedekind domains, not arbitrary nondiscrete rank-one valuation rings. WithAbs and spectral norms do not supply any analytic uniformization conclusion.

Two close candidates were opened in the Mathlib source. FunctionField.finiteDimensional_of_adjoin_transcendental, Mathlib/NumberTheory/FunctionField.lean:230, assumes an algebraic function field finite over the uncompleted rational function field; the present extension is finite only after completion, so it does not specialize. IsLocalRing.finrank_eq_finrank_residueField, Mathlib/RingTheory/LocalRing/Etale.lean:104, assumes finite etale local algebras and gives only one direction. Algebra.FormallyUnramified.iff_map_maximalIdeal_eq, Mathlib/RingTheory/Unramified/LocalRing.lean:117, assumes EssFiniteType; the main missing theorem here must establish finite etale valuation rings from the degree equality. Neither is a leaf for the analytic iff. The logged targeted greps exposed these declarations and I read their surrounding hypotheses.

## Review by Q40

I read Temkin Theorem 2.1.10 on printed page 10 and its actual proof on page 51, not just its statement. For type alternatives I read section 6.2 on pages 41–42, Remark 6.2.2, and the coordinate choices at the beginning of the proof of 6.3.1 on page 49. For stability I read 6.3.1(iii) and its proof, and the definition of Cartesian/stable in sections 2.1 and 6.1. For immediate rationality I read the type-4 proof on page 50: over algebraically closed k the finite extensions in that case are immediate, and the proof actually constructs a generator, which explains the stronger conclusion of the new node. For parameter finiteness I read Corollary 6.3.4 on pages 48–49, including its warning that topological transcendence cannot be treated as ordinary transcendence in towers. For close embeddings I read Lemma 6.3.3 and its almost-orthogonal-basis proof. For the etale criterion I read Lemma 2.1.5(ii), the henselian discussion on pages 7 and 9, and 2.1.6 on page 10; complete rank-one real valuations are exactly within those hypotheses.

Step 1 uses exactly the three alternatives and algebraic-closed/divisible assertions of the type-alternatives node. It uses only clause (1) of lem-weil-pbc-etale-composition-cancellation to make the identity valuation-ring map etale: an identity is an open immersion. This off-unit node is declared as a generic tool in split_report.tool_uses. The E=k edge case cannot be fed into the nontrivial type classification.

Step 2 uses the separating residue coordinate or cyclic value coordinate explicitly supplied by type-alternatives, and parameter-finiteness only after checking x is outside k. I wrote the polynomial and rational-function Gauss-norm calculations instead of creating elementary extra nodes. Completion preserves the norm and residue of a nonzero element because one can approximate it with relative error less than one. These give the exact value-group index one needed to use type23-stability. The base of this use is L=k(x)^wedge, not E; L itself is a one-dimensional field topologically generated by x. The criterion then gives the actual etale valuation-ring map from the degree equality and separability. No criterion for discrete valuations is substituted for the rank-one assertion.

Step 3 uses immediate-rationality only in case (4), so both required equalities of residue field and value group hold. Its topological generator makes the extension the identity; the etale residue-degree criterion explicitly includes degree one. This is not a new node for a clause of the item: the proof of the other two cases is Step 2 and the perturbation/residue conclusions have independent arguments.

Step 4 proves the substitution isomorphism directly. Algebraic closedness factors all polynomials into linear factors and ensures x and x' outside k are transcendental. Completeness makes k closed, giving positive distance to x, so epsilon=r/4 is positive. The relative-error product and inverse formulas preserve the uniform bound; extending by Cauchy limits yields a weak bound <=1/4 even if the original strict bound is lost at the limit. The close-embedding node is deliberately stated with this weak bound and nonzero c<1, avoiding the literal strict inequality at zero in the source's shorthand. Its conclusion is exactly the equality of finite extension degrees used here. Both residue subfields agree as actual subfields of the fixed residue field of E, since phi(a)-a has norm <1 for every integral a, and phi is onto. Only then do I apply the etale residue-degree node. I did not cite an unrelated continuity assertion as a substitute for the degree theorem.

Step 5 applies parameter-finiteness to every residue-transcendental x, not merely a convenient chosen lift. The same explicit Gauss computation shows L has the required type-2 hypothesis. Type-alternatives identifies the ambient E as type 2 from its nontrivial residue extension, giving equality of value groups. The stability formula is now applied to this L and E/L, and the residue separability is precisely the hypothesis of the item's last clause. The criterion supplies every remaining conclusion.

For B–E of delivery-errors I checked self-contained objects, all notion citations against their actual statements, single TeX escaping, precise source places, real search records, absence of duplicate nodes, and no unsupported Mathlib-leaf claim. citations.json contains a verbatim statement quote for every uses entry of every step; I opened each cited node and matched its claimed output as described above. New nodes have no proof or proof dependencies. Every mathematical dependency in the assembly is one of those quoted statements; the polynomial/substitution and degree-one arguments are written explicitly. No step exceeds 2000 characters (largest 1379 when written), and no elementary Gauss calculation was extracted as a new node.

Small-case checks: E=k; a standard Gauss field with transcendental residue; an irrational-radius field with cyclic relative value group; an immediate type-4 field; residue characteristic zero and positive characteristic (including inseparable finite extensions in the stability node); identity embeddings and c approaching 1 in the close-embedding node; identity extension and an extension with inseparable residue in the etale criterion. The classification and rationality nodes require E!=k, whereas the degree criterion allows identity extensions. The stability statement includes inseparable extensions as in the source. The etale criterion explicitly excludes inseparable residue extensions. None of these checks required changing the imported item.
