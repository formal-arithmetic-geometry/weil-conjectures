# Worker report: lem-sfb-flat-scalar-cyclic-resolution

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-flat-scalar-cyclic-resolution.json: statement split into six steps; Mathlib verdict no exact match.
- citations.json: all thirteen step/node citations, with literal statement excerpts.
- report.md: this report. searches.jsonl contains the five actual searches made in this attempt.

No new nodes and no new Mathlib leaves. Only marker files were present in the sandbox at arrival; there was no previous split, report, or search log to resume. The item was read from the current repository and its original statement, statement dependencies, provenance, blueprint fields, and inherited Q19 searches were retained.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and for scalar/cyclic resolution terminology. The project has the general bounded-flat K-flat theorem, but no declaration giving all the assertions of this item. No Lean was written and no compiler, Lake, or build was run.

## WANTED

None. All needed source material is in literature/stacks-project/.

## Problems found and repaired

The imported item had no proof. The split now distinguishes flatness over the constant domain, used only for scalar injectivity, from flatness over the sheaf algebra itself, used for K-flatness. No assertion was changed or weakened. The quotient is the sheaf cokernel, not an assertion that all quotient maps on sections are surjective. No point or enough-points hypothesis was introduced.

The cited existing lem-pc-bounded-above-flat-kflat-site has stale source metadata saying 06YS. The local tag table and its reviewed_lean note both identify lemma-bounded-flat-K-flat as 06YQ; the present steps cite 06YQ and the correct label. The existing node's statement is exactly the ringed-site theorem needed. I did not edit that other worker's node.

## Unfinished work

None in the one-level mathematical split. The mandatory server checks and direct push are performed after this report is written.

## Mathlib and duplicate searches

Read all five current search results before concluding no match. The first LeanFinder query returned ordinary flat-module criteria; the second returned sheaf finite-presentation predicates, the sheaf abelian instance, and ordinary flatness results. LeanSearch returned flat tensor exactness for ordinary modules, HomologicalComplex.tensorObj, and a bounded-representative theorem. Loogle's quoted KFlat query returned the unrelated Lean structure utility. The grep found seventeen uses or declarations of scalar short complexes and ordinary torsion-free flatness. Read Mathlib/RingTheory/Regular/Category.lean:20-53 and RingTheory/Flat/TorsionFree.lean:71-89. They concern modules over a ring, and do not supply the ringed-site statement in one specialization. The item retains its inherited searches and appends only the five searches actually logged by msearch.py here.

Searched the whole DAG for 06YQ/06YU and bounded-flat, scalar quotient, cyclic resolution, and exact constant sheafification concepts. Searched the imported blueprint using blueprint_refs.py (bounded-flat, K-flat, constant sheaf exact, scalar cyclic, cyclic resolution, scalar quotient, and 06YQ). The ancestor command confirms det-lem-integral-models-operations. The general ringed-site K-flat criterion and exact module sheafification already exist and are reused. The nearby lem-pur-constant-two-term-resolution only covers constant Z_l and Z/l^N, whereas this item allows every domain and an arbitrary flat sheaf algebra. The nearby lem-sfb-scalar-model-finite-flat-resolution assumes a DVR or a field and asserts existence of some free resolution, not the specified scalar differential over every domain.

## Not duplicates

No new nodes: no new/existing same-tag pairs arise. The elementary tensor-unit identifications and two-term cohomology calculation are proof steps, not extra nodes.

## Review by NK

I read the chapter and sk-lem-integral-models unit record, and the current blueprint's sk-lem-integral-models-operations.proof.md. This item supplies the cyclic scalar calculation for the unit's tensor-product local models; it changes no route or unit realization. Its source is an explicit agent expansion using the actual Stacks texts, rather than attributing the whole composite lemma verbatim to Stacks. I read Modules on Sites 03EI (exact sheafification), 03ER (the sheaf flatness definition), 03EK (the sectionwise tensor and its sheafification), 03DA's module-category content through the cited statement, Homology 0115 and the immediately preceding cohomology formula, and Sites Cohomology 06YQ and 06YU with the preceding construction. There are no new child-node sources to review.

Step 1 cites lem-weil-pbc-site-r-module-presheaf-sheafification-exact, whose statement explicitly provides sectionwise presheaf kernels and exact module sheafification, and def-weil-pbc-constant-sheaf, which identifies the sheafified constant presheaf. The input coefficient multiplication is injective by cancellation in the given integral domain. Module sheafification over the constant ring presheaf has coefficient sheaf A_C, exactly the coefficient in the item. This is the one non-elementary passage from coefficient modules to sheaves, and it is cited rather than replaced by a stalk argument.

Step 2 uses def-pc-flat-sheaf-modules, whose statement defines flatness as exactness of the actual sheaf tensor functor, not merely as an undeveloped word. Preservation of the kernel sequence is a direct application of that definition. The tensor identification is written with mutually inverse formulas on every object, using the sectionwise tensor formula in def-pur-sheaf-tensor-product. I checked that a tensor 1 is multiplication by the given constant scalar, even if the algebra map is not faithful. def-weil-sheaf-of-modules-category explicitly states that kernels are sectionwise, justifying the injectivity wording. This is a few-line definitional step, with no unstated flat-base-change theorem.

Step 3 uses the same module-category statement for the quotient cokernel, the exact cohomology formula from def-pc-acyclic-complex-modules, and the cohomology-isomorphism definition from def-pc-quasi-iso-modules. I checked both relevant degrees (-1 and 0), all remaining degrees, and that the cohomology map is induced by the actual quotient augmentation q, not merely that the objects have isomorphic cohomology.

Step 4 uses only the actual tensor construction and flatness definition. The written unit formulas and the zero tensor show exactness over R itself. This distinction prevents the incorrect inference that R-flatness must be deduced from A_C-flatness. It is elementary and creates no separate tensor-unit or free-flatness node.

Step 5 cites lem-pc-bounded-above-flat-kflat-site. I opened its statement: it applies to an arbitrary site with an arbitrary commutative ring sheaf, not just an etale site, a constant coefficient sheaf, or a ringed space. The bounds are b=0 for both displayed complexes, and Step 4 supplies every flat term, including zero terms. def-pc-kflat-complex explicitly defines a K-flat resolution as a quasi-isomorphism with K-flat source. Step 3 supplies that quasi-isomorphism. The cited theorem's precise statement therefore covers everything taken from it.

Step 6 takes only the explicit sentence of lem-weil-pbc-ringed-projection-mate-exact saying that one K-flat resolution computes derived tensor. Its ringed-topos setup is supplied by the identity of the given small ringed site; there is no properness or projection-formula hypothesis. The formula uses total tensor with an arbitrary complex M, so the conclusion covers derived tensor on the entire unbounded category, not merely modules in degree zero. The two general black-box tools are declared in split_report.tool_uses; the module sheafification node is already a Mathlib leaf.

I checked every step against C1/C4: the only non-elementary inputs are exact sheafification, the bounded-flat K-flat criterion, and the one-factor derived tensor computation, all existing cited statements. Every other fact is cancellation, applying an exact functor by its definition, an explicit tensor-unit formula, or the two-term kernel/cokernel calculation. citations.json quotes actual substrings of all cited statements. No step exceeds 2000 characters. The proof contains no new node restating a clause of the item, and no generic result has been hidden in a long step.

Small cases checked: a invertible gives a contractible two-term resolution of zero; R=0 gives zero throughout and needs no faithful-flatness hypothesis; R=A on the point site gives the usual scalar quotient resolution; a nonzero nonunit over a domain gives H^0=R/aR and no H^-1. Empty or degenerate sites also require no nonzero global sections. Dropping flatness would fail, for example A=Z, R=(Z/2)_C, a=2 on the point site: the degree -1 cohomology is then nonzero. Taking a=0 likewise fails outside the allowed hypothesis. Thus the hypotheses used are exactly those given. The report and item were checked against delivery-errors B through E, including source labels, literal citations, edge cases, and the prohibition on unnecessary child nodes.
