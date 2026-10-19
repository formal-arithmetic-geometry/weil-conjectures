# Worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-invariant-localization-filtered-lift.json` — repaired split, statement unchanged; 7 proof steps, now with two extracted lemma citations.
- `dag/nodes/sec-trace-formula/lem-trf-localization-filtration-descent.json` — new statement node, Mathlib searches found no match.
- `dag/nodes/sec-trace-formula/lem-trf-invariant-closed-basechange-identification.json` — new statement node, Mathlib searches found no match.
- `citations.json` — verbatim statement quotes for every step citation.

## Attachments

None found. The source checkout has no declaration tagged `(blueprint: lem-trf-invariant-localization-filtered-lift)`.

## WANTED

None. The proof source is available in Varshavsky’s paper under `literature/varshavsky-lefschetz-verdier-trace-formula_arXiv-math0505564.pdf`.

## What was wrong and what changed

The returned version had two proof steps longer than the 2000-character review limit. Step 1 contained the complete construction and representative-independence argument for the open--closed filtered object; Step 5 contained the complete reduced closed-support factorization and compact-support base-change argument. I extracted these arguments into the two new statement-only nodes above, leaving the item statement and route unchanged. Step 1 now cites the filtration-descent node together with the pro-étale comparison and finite-stage preservation statements. Step 5 now cites the invariant closed-basechange node for the factorization and the assertions `i^*T(a)=0` and invertibility of `i^*T(b)`. Both nodes were searched against the whole DAG and blueprint before creation; neither duplicates an existing statement or restates the item.

## What could not be finished

Nothing.

## Review by Q12

I read the item statement and all seven proof steps against Varshavsky, §§1.5.6, 1.5.9, Example 5.2.3, §§5.1.4–5.1.5, 5.2.1–5.2.3, and 5.3.3, including equation (5.2), with the legs interchanged as required by this project’s correspondence convention. The statement still has the original hypotheses (finite coefficient stage, separated finite-type schemes, set-theoretic invariance, bounded constructible finite-Tor object, and the exact filtered localization category) and the original conclusion (bijective forgetful Hom map and the two exceptional-adjoint graded maps).

For Step 1 I checked the exact open–closed sequence against `lem-weil-pbc-open-closed-short-exact`, exact inverse image and extension by zero against `prop-weil-pbc-inverse-image-modules-exact` and `lem-weil-pbc-extension-by-zero-exact`, and the representative-independent filtered descent against the new `lem-trf-localization-filtration-descent` statement. I also checked the etale/pro-etale Hom identification against `lem-sf-proetale-constructible-origin`, `sk-prop-sf-comparison`, and `det-ctf-finite-comparison-localizing`, and the constructibility claim against `prop-functor-package`.

For Step 2 I checked the invariant inclusion `c_2^{-1}(U)\subseteq c_1^{-1}(U)`, extension-by-zero base change, compact-support composition, and the empty/self squares. For Step 3 I checked ordinary exceptional adjunction, enough injectives, and the filtered RHom global-Hom formula; the vanishing is asserted for every cochain shift, as required. For Step 4 I checked Nagata’s hypotheses (the finite-type separated targets are quasi-compact and quasi-separated), the supplied filtered operation lifts and their graded formulas, and the negative graded pieces: only `RHom(TK_U,K_Z)` can occur and it vanishes by Step 3, so the truncation gives the Hom bijection.

For Step 5 I checked functorial filtered truncation triangles and graded operation comparisons, the open uniqueness via `j_!\dashv j^*`, and the closed uniqueness via the new `lem-trf-invariant-closed-basechange-identification` plus `fix-prop-adjunctions`. For Step 6 I checked the explicit open exceptional-adjoint formula and its unit/counit comparison. For Step 7 I checked reduction invariance, the factorization through `Y=W_{\mathrm{red}}`, compact-support base change, and the proper coefficient pushforward formula against `prop-functor-package`, `i-topology`, `fix-prop-adjunctions`, `def-trf-coefficient-pushforward`, and `lem-weil-pbc-closed-immersion-proper`; the displayed mate identity is the ordinary triangle identity and gives the claimed closed graded map.

I checked the two new nodes are strict subclaims of the item, introduce all their objects and hypotheses, carry no proof text, and have no Mathlib match. Small edge cases checked include `Z=\varnothing` (the closed graded term is zero), `Z=X` (the open graded term is zero), and a representative concentrated in one degree; the filtered construction and the two base-change assertions reduce to the evident exact localization sequence in these cases. No SGA 4 or SGA 4½ source is cited.

## Repair continuation, 2026-10-17

I retained the previous proof route, both extracted statements, the source transcript, and the search log after the transport interruption. Comparing the sandbox item with the current shared node shows that the statement, Lean record, blueprint import fields and unit binding are unchanged; only the split fields change. The two retained child ids are still absent from the shared DAG. Steps 2, 3, 4, 6 and 7 remain verbatim from the returned proof. The initial required dry run was started before these continuation edits; a final dry run will validate the revised files before delivery.

I corrected the retained closed-support statement to introduce $k$, $A$, $X$, $C$, admissibility, the small etale realization, $K_U$, and both localization arrows. I made the filtration lemma explicitly assume all four exact functors used by descent, and described its generic etale filtered localization inline instead of citing a definition specialized to pro-etale finite-type schemes. Step 1 now cites the actual exactness statements to discharge those assumptions. Step 5 introduces $W$ and $Y$ explicitly, so the unchanged Step 7 can use them. Both children record the intermediate item in their blueprint ancestry.

The previous citations file often quoted a node's opening hypotheses instead of its conclusion. I replaced those entries with verbatim conclusions or formulas actually used by the steps, and checked them against the current shared node statements. In particular, Step 1 takes the constructible-origin equivalence, full faithfulness, and comparison with compactification-defined compact support from three separate statements; it does not infer compatibility of operations from equivalence alone. The finite-stage preservation clause of `prop-functor-package` supplies the bounded constructible finite-Tor domain. Step 5 uses the filtered Hom node's functorial truncation triangles and the operation-lift node's graded comparisons for its equations, recollement's specified adjunctions for the open equation, and the new closed-support statement plus ordinary adjunction for the closed equation. Step 7 retains the explicit mate and triangle-identity calculation; it does not simply claim that the closed graded map transports correctly.

I read the current main-20261015 blueprint proof of `lem-trf-local-term-locality` at the paragraph explaining open--closed additivity and proper pushforward in the contracting-correspondence proof. The two children refine exactly that part of the historical blueprint ancestor. Whole-DAG searches for localization filtrations, invariant closed support, and canonical sections of the forgetful functor, and whole-blueprint searches for `localization filtration`, `invariant closed`, `filtration`, and `invariant`, found no node stating either child. The Lean source searches for the item id and the new notions found no attachment. The general cone-localization, filtered Hom, and filtered-operation nodes supply different facts, so none replaces either child.

I read the saved semantic-search hits and the Mathlib source of `Functor.mapDerivedCategoryFactors` (DerivedCategory/ExactFunctor.lean, lines 32–45), `ShortComplex.ShortExact.singleTriangle` (DerivedCategory/SingleTriangle.lean, lines 51–58), and `IsClosedImmersion.isStableUnderBaseChange` (Morphisms/ClosedImmersion.lean, lines 382–388). They concern ordinary derived functors, ordinary triangles, and geometric base change of a closed immersion; they do not assert the filtered section or the invariant-support sheaf comparison. The previously logged second semantic phrasings are retained as search records. The retained closed-support search entries lacking their corresponding log were recovered using the required search command, and their actual results are now recorded. No new search result was invented.

For the closed-support statement I also tested a nonreduced fibre: take $X=\mathbf A^1_k$, $Z=\{0\}$, $C=\operatorname{Spec}(k[\epsilon]/(\epsilon^2))$, with $c_1^*t=\epsilon$ and $c_2^*t=\epsilon$. The fibre $W$ is already a point in this example; if instead $c_1^*t=0$, then $W=C$ and $c_2$ does not factor through $Z$ until one replaces $W$ by its reduction. This is why the new statement uses $Y=W_{\mathrm{red}}$, rather than claiming scheme-theoretic factorization on $W$. Over a finite-type field scheme the reduction immersion is finite and a universal homeomorphism, so `i-topology` applies. The empty and full closed subsets remain valid and give respectively a zero closed or open summand. The localization lemma is also valid for the zero complex, arbitrary bounded representatives, and the empty or full closed subset: the graded functors are the assumed exact subfunctor and quotient. Neither child gives the Hom bijection or either graded-map equality of the item, so neither is a relabelling of an item clause.

All seven non-elementary steps have at most 2000 characters (914, 891, 701, 1641, 1100, 948, 1835 after this continuation). The longer retained Step 4 is a single application of the cited graded Hom formula followed by finite-filtration vanishing; Step 7 is the explicit unit--counit calculation with the cited pushforward recipe, rather than an additional uncited comparison lemma.

The first dry run printed `OK (not pushed)` at `e672127680`. Because continuation edits were made while that invocation waited, I require a new dry run of the final sandbox before pushing; the earlier OK is not treated as validation of later edits. The invalid retained Loogle application pattern is explicitly labelled invalid, and the earlier successful logged query `"Filtered", "ShortComplex"` supplies the actual name-pattern search. The citation file has exact coverage of all 32 `(step, node)` citations and every quote is a verbatim part of the cited statement.

## Not duplicates

- `lem-trf-localization-filtration-descent` vs `lem-trf-filtered-cone-localization`: the latter establishes a triangulated localization of filtered complexes; it does not construct the canonical open--closed section on bounded derived objects or prove its representative independence.
- `lem-trf-localization-filtration-descent` vs `lem-trf-filtered-derived-operation-lifts`: operation lifts take a filtered object as input; this child constructs a particular filtered object functorially from an unfiltered one.
- `lem-trf-invariant-closed-basechange-identification` vs `i-topology`: reduction invariance is only one ingredient; the child states the reduced leg factorizations and the natural compact-support comparison for the closed restriction, including the localization arrows.
- `lem-trf-invariant-closed-basechange-identification` vs `prop-functor-package`: the package gives general base change and preservation; it does not assert the invariant-support factorization through the closed subscheme or its consequences for the two localization arrows.
