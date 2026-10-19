# Stage-1 worker report: lem-sfb-finite-classical-unbounded-comparison

1. Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-classical-unbounded-comparison.json`: item, split into five proof steps; not a Mathlib leaf.
- `citations.json`: verbatim statement evidence for every cited node use.

2. Attachments

None. A source grep for the item id, its blueprint tag, and the comparison notions found no sorry-free project declaration covering the unbounded classical counit. The existing declarations/nodes cover bounded-below comparison, full faithfulness, or direct-image comparison separately.

3. WANTED:

None. Bhatt–Scholze and the blueprint sources needed for the split are present locally.

4. Problems corrected

The imported item had an empty proof despite asserting the unbounded essential-image theorem. I supplied the missing finite cohomological-dimension and left-completion route. Full faithfulness and unbounded direct-image comparison are deliberately not restated: they are separate existing nodes named by the blueprint route. No statement change was needed.

## Not duplicates

- `lem-sfb-finite-classical-unbounded-comparison` vs `det-pe-classical-derived-equivalence`: the existing node is only a bounded-below equivalence; this item extends the counit to all unbounded classical complexes.
- `lem-sfb-finite-classical-unbounded-comparison` vs `det-pe-unbounded-classical-bounds`: the bounds node supplies cohomological-dimension estimates, not the counit or essential image.
- `lem-sfb-finite-classical-unbounded-comparison` vs `det-pe-unbounded-classical-truncation`: the truncation node supplies fixed-degree tail control, not the derived equivalence.
- `lem-sfb-finite-classical-unbounded-comparison` vs `sk-thm-pe-classical-sheaves`: the existing theorem is an underived sheaf equivalence; this item concerns unbounded derived complexes.
- `lem-sfb-finite-classical-unbounded-comparison` vs `lem-sfb-unbounded-site-comparison`: that node gives exact full faithfulness of inverse image, while this item proves the counit on the classical pro-étale essential image.

## Review by NR

I read the item source, the current `sk-prop-pe-unbounded-classical` section and proof, the chapter and unit records, Bhatt–Scholze Proposition 5.2.6(3), Remark 5.2.8, Definition 5.3.1 and Proposition 5.3.2, and each cited DAG statement. Step 1 uses the exact module equivalence in `sk-thm-pe-classical-sheaves` to identify the cohomology sheaves of an exact inverse-image complex as classical. Step 2 applies the finite-type torsion bounds with the identity morphism and then uses the same sheaf essential-image statement to transfer the bound to every classical coefficient sheaf; finiteness of `A` supplies torsion. Step 3 checks that the bounded-below unit hypothesis required by `det-pe-classical-derived-equivalence` is exactly `sk-prop-sf-comparison`, and takes its stated counit conclusion. Step 4 uses the fixed-degree truncation estimate and the finite bound to justify the lower-truncation tower and the single Milnor `R^1 lim` term; Bhatt–Scholze’s left-completion argument then identifies the unbounded classical category with the completed étale category, which equals the ordinary étale category under finite cohomological dimension. Step 5 is the immediate essential-surjectivity consequence of the counit, with `R K` as the étale preimage.

I checked that every cited node says the fact its step takes, that all hypotheses (finite or algebraically closed `k`, invertible `ell`, finite `ell`-power-torsion `A`, finite-type `X`) are in force, and that no boundedness or constructibility was silently added to the item. I tested the point case, the zero complex, zero coefficient ring, identity comparison, and an arbitrary unbounded lower-truncation tower. No SGA source is used. The Mathlib searches for the item were run with `msearch.py` (LeanFinder, Loogle, grep, LeanSearch); all returned only generic derived-category or site declarations, so there is no Mathlib leaf.


## Second reading by NR

Item statement — read Bhatt–Scholze Proposition 5.2.6(3), Remark 5.2.8, Definition 5.3.1 and Proposition 5.3.2 on printed pp. 37–38, the current main-20261015 affine-local opening comparison paragraph, and the finite-coefficient unbounded-comparison statement/bounds/truncation files. Verdict: correct; finite-type schemes over finite or algebraically closed fields with finite commutative coefficients killed by an invertible prime power satisfy the required uniform classical torsion bounds. No separatedness, constructibility, finite-module, or boundedness hypothesis is needed. The item statement and its definition dependencies are unchanged.

Step 1 — checked the exact module equivalence in `sk-thm-pe-classical-sheaves` and the natural unbounded cohomology formula in `lem-weil-pbc-exact-functor-bounded-below` against their actual statements; verdict: valid, including arbitrary unbounded complexes and zero cohomology sheaves. Added the latter citation instead of silently using its non-elementary derived-functor fact.

Step 2 — checked part (1) of `det-pe-unbounded-classical-bounds` against its main-20261015 source, with Y=X and g=id, and the module essential image of `sk-thm-pe-classical-sheaves`; verdict: valid with the same nonnegative e for every affine etale W. Every module, even one with infinitely many generators, is killed by ell^r. The empty scheme is handled before invoking its dimension. Replaced the unused etale-local-cohomological-dimension detour with the precise uniform input needed in step 5.

Step 3 — checked the entire conditional statement of `det-pe-classical-derived-equivalence`, especially its bounded-below unit hypothesis and counit part (2), against `sk-prop-sf-comparison`; verdict: valid. Read `lem-sc-bounded-below-injective-resolution`: its bounded-below injective complex is explicitly K-injective, so it computes the same R and counit used in the unbounded statement. Added this compatibility justification.

Step 4 — checked the sectionwise restriction formula of `def-weil-pbc-site-comparison-morphism`, the exact-sheafification and cohomology clause of `lem-weil-pbc-site-module-presheaf-sheafification-exact`, and the unbounded statements of `lem-weil-pbc-kinjective-total-derived` and `lem-weil-pbc-kinjective-hom-derived`; also opened Stacks sites-modules.tex Tag 03EI, label lemma-sheafification-exact, and derived.tex Tags 070I/070Y, labels lemma-K-injective/lemma-K-injective-defined. Verdict: the displayed presheaf calculation gives the natural cohomology sheaf of RK; it assumes no left completeness of the etale category and uses no bounded-below detection theorem on an unbounded input.

Step 5 — checked the precise inequality N<m-e-1 and coefficient hypotheses of `det-pe-unbounded-classical-truncation` part (2), the natural exact-functor cohomology formula, and the all-integer isomorphism criterion of `lem-weil-pbc-unbounded-derived-iso-cohomology` (Stacks 05RT, label lemma-acyclic); verdict: valid. N is independent of W. W has its constant affine-etale presentation. Sheafification is justified from its universal property: the kernel and cokernel presheaves vanish on affines, every map from either to a sheaf is zero by affine covers, and exact sheafification therefore makes the induced map invertible. The actual counit equation is written with both composites typed from FRK to T, and all three other cohomology maps in that equation are invertible.

Step 6 — checked against the item's counit conclusion and the definition of essential image; verdict: elementary, take the actual etale object M=RK and invert the counit.

New nodes — none; no elementary lemma, duplicate, item restatement, or new Mathlib leaf remains to audit under B1–B7. All 12 existing dependencies were opened and their statements, rather than their proofs, supply the cited inputs. `citations.json` now contains one complete verbatim statement per use, including all new citations and the renumbered final argument.

Small cases — the empty scheme is zero by the empty-cover sheaf condition; for A=0 all module sheaves and all maps in the argument are zero/isomorphisms; for a field and for a single classical sheaf in degrees 0 or 1 the argument reduces to the bounded-below counit; for an arbitrary unbounded K the choice N<m-e-1 ensures N<m, so the right truncation map is an isomorphism in degree m. No finite generation or lower bound is introduced. The zero complex gives zero at each section-cohomology and sheafification calculation.

Search and attachment audit — searched the entire DAG and current blueprint by classical/counit/essential-image/unbounded-comparison terms; the other comparison nodes supply full faithfulness, a bounded-below counit, bounds or truncation, and none duplicates this item's unbounded counit proof. Searched both named read-only source trees by item id and classical-counit/unbounded-comparison concepts; no project attachment was found. Ran independent msearch.py LeanFinder (both a general exact-functor formulation and a finite-cohomological-dimension comparison formulation), a valid quoted `"proetale"` Loogle query, and grep for `leftComplete|classical.*cohomology|cohomology.*classical`. Inspected actual returned signatures: generic exact-functor components are already covered by an existing node; site definitions and derived-localization declarations do not prove the item. Actual logs are retained in searches.jsonl and reflected in mathlib_searches. The first worker's invalid Loogle identifier query is explicitly recorded as invalid, not evidence of absence.

Changes and reasons — the old step 4 attributed a whole left-completion equivalence and the identification of its adjunction to a citation whose statement only gives a fixed-degree sections estimate (C1/C4/E5). Replaced that unsupported inference by the explicit sheafification computation, uniform truncation map, and counit naturality square of steps 4–5. This realizes the reduction to bounded-below complexes in Bhatt–Scholze Remark 5.2.8 and the blueprint's fixed-degree truncation route without outsourcing the item to a new theorem. Added citations for exact inverse-image cohomology and bounded-below/unbounded resolution compatibility; made the empty case and the uniform prime-power torsion hypothesis explicit; regenerated citation evidence and recorded the searches actually run. The first worker's review above is retained as requested; its approval of the old step 4 is superseded by this repair. No statement dispute, target change, new node, SGA source, Lean writing, compiler, or local preflight was involved.

Generic tool uses for the maintainer — `lem-weil-pbc-exact-functor-bounded-below`, `lem-sc-bounded-below-injective-resolution`, `lem-weil-pbc-kinjective-hom-derived`, and `lem-weil-pbc-kinjective-total-derived` are existing general tools for exact derived functors and K-injective computations; they supply no alternative geometric route. The sheafification and unbounded cohomology-isomorphism inputs are existing Mathlib leaves. The classical sheaf equivalence, bounded-below comparison, and bounds/truncation inputs are the existing comparison route named by the item's source. No tool_uses maintainer field was edited.
