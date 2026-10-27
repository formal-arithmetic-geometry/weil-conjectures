# Stage-1 report: lem-trf-generic-subcurve-nodal-chart-ideals

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-generic-subcurve-nodal-chart-ideals.json`: item, statement, split into nine proof steps; no Mathlib match for the full classification.
- `citations.json`: all 14 step/node citations, with verbatim statements as quotations.
- `report.md`: this report. `searches.jsonl` records the actual msearch calls; `write_split.py` is sandbox-only preparation.

No new DAG nodes; zero new Mathlib leaves. The mathematical statement and statement dependencies are unchanged. The inherited searches, source, blueprint ancestry and created record are retained; actual Q109 searches are appended.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint id, nodal-chart/subcurve-ideal phrases, nodal, generic-component and binomial-normality terminology. No declaration states this classification. A sorry declaration is not treated as a proof. No Lean was written and no compiler, Lake or build tool was run.

## WANTED

None. The argument is explicitly agent-written from locally available Stacks ingredients and already existing DAG tool statements; it is not attributed to a source that states this relative classification verbatim.

## Problems and corrections

The item was unsplit with no proof; there was no earlier sandbox split or report. No released repair note exists. There is no statement dispute. Tags 0CBY and 0E38 give respectively the etale nodal model and the field-fibre complementary-subcurve result, rather than the asserted relative normal-domain classification. In particular, one cannot invoke 0E38 to identify contracted ideals over an arbitrary normal base, or infer that a flat algebra is a domain. The proof supplies that missing algebra: the normal chart uses existing finite normal-domain factors; the split chart uses both axis quotients and an injection into their product.

A potentially new binomial-normality lemma was rejected during research because `lem-sfb-binomial-laurent-normal-form` already states its full generality, including arbitrary commutative coefficients for the basis and arbitrary normal-domain coefficients for nonzero a. Likewise `lem-trf-etale-normal-domain-finite-factors` already supplies the non-Noetherian factorization. No clause was moved into a new node.

The latest blueprint is `literature/blueprint/latest/` (main-20261024). I read the current `sk-i-curve-zero/_section.md` and the locality proof there. The current proof follows contracting correspondences; the item's assigned ancestry is a historical nearby-cycle/alteration auxiliary. I retained that ancestry, documented its historical role in split_report, and did not modify the unit or substitute a route. The chapter remains fixed.

## Not duplicates

No new nodes were created, so there are no new/existing pairs sharing a Stacks tag to justify. Whole-DAG statement/title/source searches covered normal etale factors, polynomial normality, normal localizations, uv-a/xy-a, normal binomial/Laurent algebras, flat tensor exactness and etale quotient base change. Whole-blueprint searches used `normal etale`, `nodal chart`, `uv`, `uv-a`, `normal domain`, and `generic subcurve`; they produced no node stating the assigned classification. The binomial algebra and factor-decomposition nodes were reused rather than duplicated.

## Review by Q109

I read the full B--E checklists in both copies of coord/delivery-errors.md and checked the proof against the statements actually cited. I read Stacks curves.tex Tag 0CBY (`lemma-etale-local-structure-nodal-family`, including its universal model) and Tag 0E38 (`lemma-closed-subscheme-nodal-curve`, statement and branch argument). For the algebra tools I read algebra.tex Tag 030A (`lemma-polynomial-domain-normal`), Tag 030C (`lemma-characterize-reduced-ring-normal`), Tag 033C (`lemma-normal-goes-up`), Tag 00U2 (`lemma-etale`, base change and flatness), and Tag 00HD (`lemma-flat`). I also read Tag 00CS (`proposition-localization-exact`) to compare the explicit fraction calculation, rather than treating localization of an arbitrary ideal equality as an unexplained transport. I opened every cited DAG node and read its statement. There are no new nodes needing separate sources.

1. Step 1 takes polynomial normality precisely from `lem-weil-pbc-polynomial-ring-normal-domain`, iterated n times with n=0 starting at A. It takes binomial normality from the final clause of `lem-sfb-binomial-laurent-normal-form`. That clause explicitly assumes a domain and a nonzero parameter; this step is restricted to a != 0 and A normal. It imposes no Noetherian assumption. The binomial node's actual basis and normality statements, and its coefficient proof, were read.
2. Step 2 takes the A-algebra product statement, now with base E, from `lem-trf-etale-normal-domain-finite-factors`. E is a normal domain by step 1 and Spec C -> Spec E is exactly the etale map in the hypothesis. The basis clause of the binomial node makes A -> E injective in that case. `lem-weil-pbc-etale-algebra-flat` supplies flatness over E, and `lem-weil-pbc-flat-tensor-exact` supplies preservation of the displayed multiplication injection. Thus nonzero scalars cannot disappear in a nonzero domain factor; normality alone was not used for this assertion.
3. Step 3 uses only the established product, elementary idempotent/prime algebra and explicit common denominators. Localization of each factor is a nonzero domain because the scalars are nonzero in it. This proves contraction of the factor kernels, identifies the chosen subset T and its complement with product ideals, and gives an explicit principal neighborhood. The case C=0 has no prime to check.
4. Step 4 invokes `lem-weil-pbc-etale-quotient-base-change` with the ideals (u) and (v) in E, and identifies the two quotients by evaluating the eliminated coordinate, using a=0. Polynomial normality and the same finite-factor theorem apply to A[v], A[u]. Flatness and exact tensoring are applied again over those polynomial domains, with multiplication by any nonzero b. This separately verifies A-torsion-freeness and the nonvanishing of the other coordinate in each factor, which are needed in step 6. All five cited statements say exactly these things; the proof does not take facts from their proof bodies.
5. Step 5 uses only the arbitrary-ring basis clause of the binomial node, so a=0 is permitted. The map E -> E/(u) direct-sum E/(v) is injective by inspecting the two lists of coefficients. The etale-flat node and the exact-tensor node then give C -> D direct-sum F injective. The tensor/quotient identification is explicitly the map e-bar tensor c -> ec-bar. Thus uC intersect vC=0 is proved rather than hidden as a presumed flat-intersection formula.
6. Step 6's elementary argument uses the products of step 4 and injection of step 5. A prime contains u or v, and then a factor kernel. Kernels within a product are incomparable by idempotents. Kernels from the two branches are incomparable because u and v have opposite vanishing/nonvanishing in their quotients. These facts prove minimality and completeness, not merely existence of some primes. Their quotients are A-torsion-free domains, so contraction after generic localization is checked by sc in P implies c in P. Applying the same argument to the localized two quotient products identifies every generic minimal prime and hence the original contracted intersections. This is a finite prime-and-fraction argument without a new existence theorem.
7. Step 7 constructs g and h by lifting single factor idempotents only in the quotient in which the prime exists; if that quotient has no induced prime it uses u or v to kill it. Each lift is outside q by its residue at q. The product f is outside q, and an induced prime proves that at least one retained factor remains nonzero. No arbitrary stalk equality is spread to a neighborhood, and no finite generation is assumed before this construction.
8. Step 8 checks localization of every finite intersection using one maximum denominator exponent and checks kernels the same way. The surviving branch quotients are domains, so the only possible surviving kernels are uC_f and vC_f. Intersecting whichever ones T selects gives all four displayed pairs; their intersection is zero by step 5. The empty intersection is explicitly the unit ideal.
9. Step 9 handles the case one branch quotient vanishes, using the localized injection and quotient surjectivity to identify the other quotient with C_f. It is then a domain with one minimal kernel, giving the two trivial pairs. Radicality follows directly from contraction of intersections of primes, including the empty intersection, and finite generation follows from the explicit local generators 0,1,u,v. It is not an extra assumed lemma.

All non-elementary steps cite their actual theorem statements. All uncited steps are explicit finite-product, prime, quotient or fraction computations from the preceding steps. No step exceeds 2000 characters (lengths 421, 608, 954, 796, 525, 1099, 694, 728, 781), and none hides a new standard lemma. proof_deps is the union of uses. The only off-unit non-leaf tool is the binomial basis/normality theorem, declared in split_report.tool_uses as a generic commutative-algebra tool; it replaces no unit step.

I tested n=0; arbitrary n by induction; a a unit (normal smooth Laurent chart); a nonzero nonunit over a DVR, where the special fibre splits but the generic component remains a whole normal-domain factor; a=0 over a field, with the identity algebra giving ideals (u),(v); a=0 after inverting u or v, when one branch vanishes; empty and full T; disconnected etale algebras; the zero algebra; and a non-Noetherian normal base. The proof never uses a height-one or Noetherian criterion, normality of A/(a), a valuation alternative, properness, or smoothness of a selected component. In the split chart the other coordinate is nonzero in each axis factor, even at points where it belongs to the prime: nonzero and invertible are not confused.

## Unfinished work

None within this stage-1 split. Existing unsplit/sorried tools remain their own DAG work; no finished Lean attachment is claimed. Server dry run and push results are recorded below when available.

## Delivery validation

The standalone server review_split passed. The first full dry run caught one textual citation typo in step 2 (`lem-weil-pbc-etale-normal-domain-finite-factors` instead of the existing `lem-trf-etale-normal-domain-finite-factors`); I corrected it. The uses list and verbatim citation already named the correct node. Statement equality, exact step/node quotation coverage and the absence of a dependency cycle through the item were checked independently.
