# Stage-1 report: lem-trf-integral-component-henselian-permanence

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-integral-component-henselian-permanence.json`: existing statement, now split into seven proof steps. Statement and statement dependencies unchanged. Five actual Q57 Mathlib searches run, with three new query records appended and two queries already present in the retained Q05 records; all earlier searches and provenance retained.
- `citations.json`: eleven citations, one for every use in the seven steps, with verbatim quotations from the cited node statements.
- `report.md`: this report. `write_split.py` is a sandbox-only writing helper; `searches.jsonl` is the search command's unmodified log.

No new DAG nodes; no new Mathlib leaves; no unit files modified.

## Attachments

None. I searched the slopmaster2 project by the exact item id, the blueprint tag, and integral/henselian/connected terminology, and checked the upstream name index. `IsLocalRing.of_henselianLocalRing_of_isIntegral_of_isDomain` in `WeilConjectures/RingTheory/ProEtale/IntegralLocal.lean:207` requires a domain and concludes only locality. Its use at `HenselianLocalRing.lean:61` is the integral-closure domain case. Neither states this item. The finite-product theorem already belongs to `lem-weil-pbc-finite-over-henselian-local-product`; it is used through that node, not attached to this more general item. Upstream master was reference only.

## Literature wanted

WANTED: Huebner--Schmidt, *The tame site of a scheme*, printed p. 12, permanence paragraph citing Artin Proposition 3.3, for historical provenance of this item. No local copy was found among the named literature paths. The item's existing online citation is retained as provenance; I do not claim to have read that online paper in this run.

WANTED: Artin, the original Proposition 3.3 on integral algebras over quasi-acyclic rings cited in that paragraph, for historical provenance. Neither missing document is needed by the proof delivered here.

## What required work

The item had a correct statement but no proof or Lean audit attachment. Its cited Stacks 092X explicitly assumes the target algebra is a domain, so that theorem cannot simply be applied to this item. The finite-subalgebra argument does extend: every finite subalgebra inherits the idempotent restriction, so 04GH's finite product has exactly one nonzero factor. One must also prove that inclusions of stages are local; arbitrary maps of local rings need not be local. This is supplied by the existing integral-maximal-contraction node, with integrality over each intermediate algebra verified directly by the original monic equations.

The omitted directed-limit locality and residue-field details in Stacks 04GI are written explicitly in Steps 4 and 6. The strict clause is proved by taking all coefficients of a separable polynomial AND its Bezout witnesses to one finite residue field, rather than assuming that a separable polynomial descends as separable without proof. No domain, reducedness, noetherianity or module-finiteness hypothesis on S was added. No statement dispute was found.

## Unfinished work

None for the one-level split. It uses existing statement nodes as intended by stage 1 and writes no Lean. The preserved missing historical references do not leave a mathematical gap.

## Not duplicates

No new nodes. Whole-DAG statement/source searches for 04GH, 092X, 09XK, filtered henselian colimits, finite integral generators, integral maximal contraction and separably closed finite extensions found the existing nodes reused below. Whole-blueprint searches `henselian` and `separably closed` found no statement equivalent to the whole item. The finite-extension node is deliberately used only for the finite fields k_A, not for the generally infinite extension K/k.

## Review by Q57

I read the local Stacks source for More on Algebra 092X (`lemma-integral-over-henselian`), including its domain hypothesis and reduction to finite subalgebras; Algebra 04GH (`lemma-finite-over-henselian`), especially (1) and (2); Algebra 04GI (`lemma-colimit-henselian`), whose omitted locality/residue details are relevant here; and More on Algebra 0FWT (`lemma-filtered-colimits-henselian`). I also read 09XK (`lemma-integral-over-henselian-pair`) to compare the initially suggested pair route. The chosen pair-colimit route reuses the DAG and does not need an auxiliary zero-dimensional algebra or a new henselian-pair lemma. I checked tag-to-label mappings in `stacks-project/tags/tags`, correcting a draft mislabel for maximal contraction to 00OI with 00GU as its going-up input.

For Step 1 I opened `lem-weil-pbc-finite-of-integral-generators`: its statement is exactly the finite-generation plus monic-equations implication used. The generators' equations hold in the subalgebra because its map to S is injective. The index is a genuine set of subalgebras, not a proper class, is nonempty even if the structure map R to S has kernel, and common upper bounds come from the union of generating sets.

For Step 2 I opened `lem-weil-pbc-finite-over-henselian-local-product`: its statement supplies the finite product, henselianity of factors, local base maps AND finite residue extensions. Thus the proof takes no property from that node's proof or its Lean implementation. The exclusion of the empty product uses S nonzero; the exclusion of multiple nonzero factors is the explicit coordinate idempotent. The resulting single factor identifies A with a henselian local R-algebra.

For Step 3 I opened `lem-weil-pbc-integral-maximal-contracts-maximal` and read the corresponding pinned Mathlib declarations at `Ideal/GoingUp.lean:204` and `:211`. The statement contracts a maximal ideal for any integral homomorphism, with no injection or domain hypothesis. I verified its input separately for A to B using the original R equations. Locality and injectivity on residue fields then follow by the maximal ideals already constructed, not by a tacit assumption that local-ring maps are local.

Step 4 uses only the local stage results just proved. For addition and multiplication in the union ideal, pass to a stage containing all representatives. Properness follows because no stage maximal ideal contains 1. A unit cannot enter N, since its inverse and its purported ideal membership occur together at some stage and all transitions preserve the maximal ideals. Conversely an element outside N is already a unit in any stage containing it. This proves the local-ring assertion, the exact contraction to every A, and locality of R to S without an uncited limit theorem.

For Step 5 I opened `def-weil-pbc-category-colimit`, `def-weil-pbc-henselian-terminology` and `lem-weil-pbc-filtered-colimit-henselian-pair`. The last statement requires a nonempty directed set, compatible ideals, henselian pairs, an actual ring colimit, and the UNION of stage ideals. Steps 1, 3 and 4 verify each requirement, and the elementwise universal property in Step 5 proves the needed colimit directly. The conclusion is exactly the henselian pair (S,N), and the definition identifies it with henselianity at the already established maximal ideal. This does not confuse Mathlib's root-lifting formulation with the DAG's idempotent formulation.

For Step 6 I opened `def-weil-algebraic-element`: the needed condition is a nonzero annihilating polynomial for each residue. The reduced monic equation has leading coefficient 1 in the nonzero field k, so is indeed nonzero. The residue embeddings use the contraction proved in Step 4; representation of every residue comes from the union, requiring no separate residue-field/colimit theorem.

For Step 7 I opened all four cited statements. The henselian terminology gives precisely separable closedness of k and the final strict conclusion. `lem-kun-sep-closed-finite-extension-sep-closed` gives separable closedness of k_A because Step 2 gives a FINITE extension; it is not applied to K. I read its recorded Mathlib source `PurelyInseparable/Basic.lean:567`, which is even more general, but do not take that unrecorded generality from the node's finite statement. `def-pc-separable-polynomial` supplies the Bezout identity, and `def-pc-separably-closed` supplies the root criterion. Carrying the finitely many coefficients of all three polynomials to one k_A proves separability there by injectivity, including nonconstancy, and mapping its root proves the criterion for K. No separability-descent theorem is hidden.

The two off-unit non-leaf tools (finite henselian product decomposition and filtered colimits of henselian pairs) are declared in `split_report.tool_uses`. They are generic commutative-algebra tools for this already assigned permanence subproblem, and do not replace the trace unit's route. The item is not its unit's key node, so its unrelated unit realization record is untouched. Blueprint ancestry and the existing created/source metadata remain intact.

I checked B--E of delivery-errors against the delivered JSON. There are no new nodes to conceal clauses or duplicate definitions. Every non-elementary input is a statement citation and every citation has a verbatim quote. Steps 4 and 6 are elementary explicit ideal/quotient arguments from previous steps; the other steps are marked non-elementary because they apply cited theorems. All seven steps are below 900 characters, hence none exceeds the 2000-character inspection threshold. The proof is agent-written because it generalizes the domain-source proof and supplies the omitted union details.

Small cases checked: S=R; R a field and S an infinite algebraic field extension; nonreduced S=k[epsilon]/(epsilon^2); noninjective R to S such as Z_p to F_p; and products such as k times k, which are excluded by the idempotent assumption. S=0 is explicitly excluded and would invalidate the locality conclusion. Over an imperfect separably closed field the residue extension may be nontrivial purely inseparable; the proof demands only algebraic and separably closed, never an isomorphism or separability. No finiteness or reducedness of S is used.

Five searches were actually run through msearch and read: LeanFinder twice with distinct phrasings, Loogle, LeanSearch and grep. The returned henselian definitions, simple-root criteria, completeness instances and Jacobson preservation theorem do not state the item; the query/results records are copied from the actual search log without inventing unavailable or absent results. Existing Q05 searches are retained. No new node search logs are required because there are no new nodes.

Server `srvcheck ... check_dag` completed successfully before report writing: no finding introduced by the sandbox or on its nodes. The required full dry run also completed with OK (not pushed), preflight passed. After this report-count correction, the final dry run and push are performed sequentially.
