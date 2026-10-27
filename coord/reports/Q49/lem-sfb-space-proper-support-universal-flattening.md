# Stage-1 report: lem-sfb-space-proper-support-universal-flattening

Group Q49; direct-delivery worker; 2026-10-24.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-proper-support-universal-flattening.json: item, statement unchanged, five-step document proof, status split.
- dag/nodes/sec-six-functors-basics/def-sfb-space-universal-relative-purity.json: definition, unsplit; no Mathlib match. Defines the algebraic-space relative assassin through the existing scheme notion and defines universal purity by absence of impurities on every scheme base change.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-proper-support-universal-purity.json: statement, unsplit; no Mathlib match. Proper carrier implies universal purity for a finite type quasi-separated morphism and a finite type module, without finite presentation or an affine base.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-pure-dimension-flatness-representability.json: statement, unsplit; no Mathlib match. Dimension-filtered flatness for every n over any scheme base is represented by an algebraic space monomorphism of finite presentation, assuming universal purity and finite presentation.
- citations.json: verbatim supporting quotations for every proof-step citation.
- searches.jsonl and search-results.json: actual msearch runs and their full output. The old item searches are retained; new searches are appended to the item. Each new node records its own five searches (LeanFinder, LeanSearch, Loogle, Mathlib grep, and a second LeanFinder phrasing). run_searches.py and write_split.py are sandbox-only helper scripts.

There are three new nodes and zero Mathlib leaves. New nodes have no proof, no proof dependencies and no proof origin. No Lean was written or compiled, no repository file was written and no git command was run by the worker.

## Attachments

None. Searches of lean/WeilConjectures for the exact item tag and universal-flattening, impurity, relative-purity and dimension-flatness concepts found no declaration stating this result or either new theorem. Weight purity and Cartesian-chart helpers called flatten are different notions. Existing sorry declarations are not completion evidence.

## WANTED

None. All mathematical sources needed are present under literature/stacks-project.

## Problems found and changes

The imported node was statement-only. Its statement and its statement dependencies remain unchanged. The proof now follows 0CVI, 0CX1 at n=0, and the schemehood argument in 0CXB, using existing DAG nodes for 0463 and 03XX. The general representability input deliberately retains every n and an arbitrary scheme base, and concludes algebraic-space representability; it does not restate the item's proper-support scheme-valued conclusion. Properness is used in a separate purity theorem. Schemehood is supplied by already existing nodes, not made into a new clause node.

The nearest blueprint ancestor printed by tools/blueprint_refs.py is None, exactly as recorded on the live item. I retained that inherited null ancestry and its full via chain, prepending the item for each new node and giving its exact supporting Stacks place. I read the latest blueprint sec-six-functors-basics/sk-thm-sf-ctf-stability proof, as well as the recorded chapter and unit. This is a supporting geometric input of the existing compactification/direct-image route, not a change of the chapter or unit route. No realization fields belong to this item.

## Unfinished work

None at this one-level split. The three newly stated inputs are intentionally left unsplit for later workers.

## Not duplicates

def-sfb-space-universal-relative-purity vs def-trf-relative-assassin: the existing node defines the relative associated points only for schemes; the new definition uses that scheme notion on etale charts and defines absence of relative impurities after arbitrary base change for an algebraic-space source.

lem-sfb-space-proper-support-universal-purity vs lem-sfb-space-proper-support-universal-flattening: the new theorem concludes only absence of impurities for a finite type module under a finite type quasi-separated morphism; the item constructs a finite-presentation scheme representing all flat base changes of a finitely presented module. Purity is a prerequisite, not a clause of the item's conclusion.

lem-sfb-space-proper-support-universal-purity vs def-sfb-space-proper-quot-functor: the existing node defines proper-support quotients and the carrier convention; it has no assertion of universal relative purity. The shared 0CZI tag concerns only the carrier formulation.

lem-sfb-space-proper-support-universal-purity vs lem-sfb-space-module-proper-carrier-support: the existing theorem equates proper annihilator support with existence of a proper carrier; it does not assert specialization of relative associated points or universal purity. The new theorem uses the carrier formulation of 0CVI, not another equivalence of supports.

lem-sfb-space-proper-support-universal-purity vs lem-sfb-noetherian-module-hom: the existing theorem represents module Hom with Noetherian base and flat proper-support target; the new theorem proves purity without Noetherianity or flatness and represents no Hom functor. Their common 0CZI is background for proper support.

lem-sfb-space-proper-support-universal-purity vs def-sfb-space-flat-proper-coefficient: the existing definition specifies flatness and proper annihilator support; universal relative purity is a different predicate and is not asserted there.

lem-sfb-space-proper-support-universal-purity vs lem-sfb-space-module-base-change-flat-proper-support: the existing theorem preserves flatness and proper support under base change, assuming the module is already flat. The new theorem assumes no flatness and concludes universal purity, needed before finding flat base changes.

lem-sfb-space-pure-dimension-flatness-representability vs lem-sfb-space-proper-support-universal-flattening: the new input is the all-n representability theorem 0CX1 for universally pure modules over arbitrary scheme bases, with an algebraic-space output and no proper-support assumption. The item must first prove purity, identify the n=0 condition, prove schemehood by 0463/03XX, and interpret the representing bijection. Thus the item is not replaced by a new copy of itself.

## Review by Q49

I read spaces-flat.tex, including situation-pre-pure, definition-impurity (0CV8), definition-pure (0CVD), lemma-proper-pure (0CVI) and its reduction to a closed proper carrier, situation-flat (0CWX), lemma-pre-flat-dimension-n (0CWS), definition-flat-dimension-n (0CWT), theorem-flat-dimension-n-representable (0CX1), lemma-when-universal-flattening (0CX2), and the schemehood paragraph in theorem-existence (0CXB). For the new purity definition I also read spaces-divisors.tex, lemma-relative-assassin and definition-relative-weak-assassin (0CV0). In the finite type quasi-separated case the fibres are locally Noetherian, so the source's weakly associated and associated versions agree. I use universal purity only: absence of all scheme-test impurities implies the pure hypothesis of 0CX1 by restricting to the test neighbourhoods in that definition. No strict-henselization comparison theorem is hidden in the item's proof. For the carrier version of 0CVI I read spaces-perfect.tex 0CZI, all three equivalent conditions and its proof.

For step 1 I opened the complete statement of lem-sfb-space-proper-support-universal-purity. It requires a finite type quasi-separated map and a finite type module with a proper closed carrier. Finite presentation supplies quasi-compactness and quasi-separatedness; finite algebra presentations supply finite generators, and the local finite free presentation supplies finite generators of F. The item's actual carrier i_*G is exactly the new theorem's hypothesis. No flatness or Noetherian hypothesis has entered.

For step 2 I checked every hypothesis and the full conclusion of lem-sfb-space-pure-dimension-flatness-representability. Both finite presentations come from the item, universal purity comes from step 1, Y=Spec R is a scheme, and 0 is a permitted nonnegative n. The cited theorem gives finite presentation and monicity of E_0 over Y as well as the bijection on every scheme test. Those are statement clauses, not information borrowed from its future proof.

For step 3 I read def-kun-transcendence-degree and def-pc-scheme-module-flat-over in full. The first defines transcendence degree as a supremum of cardinalities; nonnegativity follows from the empty independent set, without a dimension theorem. The second explicitly equates base-flatness with flatness of every ordinary module stalk over the corresponding base local ring. In the new P_0 definition every chart point is tested, so the tensor pullback condition is exactly the item's chartwise base-flatness. This is elementary substitution in explicit definitions, not an uncited algebraic-space descent theorem.

For step 4 I opened the full statements of lem-sfb-space-lft-monomorphism-separated-lqf and lem-a1-separated-locally-qf-space-representable. The former applies to a locally finite type monomorphism into a scheme, with no quasi-compactness or flatness assumption, and gives precisely the two chartwise/diagonal hypotheses of the latter. The target scheme is Spec R and the ambient base is Spec Z throughout. The latter returns a scheme and an isomorphism over the target, exactly what is needed. I declare 03XX as a generic off-unit tool use: it is the foundational schemehood criterion invoked by 0CXB, and no unit-local substitute is supplied. The 0463 node is already in the item's unit.

For step 5 I read def-sfb-space-morphism-properties, including its chart tests and diagonal/topological conditions. The isomorphism to h_T identifies charts with the identical scheme domain and identical map to Y; it also identifies the relative diagonal and point topology. Therefore the components of finite presentation transfer directly. On each test B the actual representing bijection commutes with the map to Hom(B,Y); its injectivity proves monicity and uniqueness, and its image proves existence exactly when F_B is flat. This is an elementary unpacking of the isomorphism and the step-2 statement, not an appeal to an unnamed representability theorem.

I checked small cases. If F=0 or X is empty, purity is vacuous and every base change is flat, so E_0 and T represent all maps into Y. If F is already flat, the same conclusion holds. For X=Spec Z and F=Z/p, proper support holds and flatness after A-base change is the condition that A/pA be flat over A, allowing mixed open-and-closed behaviours; the statement does not erroneously assert that the representing monomorphism is open or closed. An empty base causes no exception. For the all-n input, n=0 tests every point; larger n intentionally ignores lower-transcendence-degree nonflat points, and the zero module remains allowed. The new proper-support theorem needs only finite type, and does not assume its carrier module is finitely presented. The purity definition introduces its scheme tests, specializations, associated points and closure condition explicitly.

I searched the whole DAG by tags and concepts and the blueprint index with flattening, universal flattening, relative purity, impurity, associated point, proper support and flatness in dimensions. Existing proper-support carrier and base-change nodes do not assert purity, and existing schemehood nodes are reused. I inspected every actual search hit: Mathlib's support-specialization, scheme universally-closed/proper maps, flat modules and sitewise finite-presentation predicates do not state these inputs. Loogle's andFlattening is a Boolean tactic option. The second semantic phrasings did not change that verdict. All services answered and no unavailable response is reported as absence.

I checked delivery-errors B through E against the files: each new node introduces all objects and keeps only a statement; definitions are cited or given inline; TeX is singly escaped; exact Stacks tags and labels are supplied; blueprint references and searches are recorded; citations quote the statements actually used; no new clause simply relabels the conclusion; no proof step is over 2000 characters; no SGA is used. I corrected the draft by spelling out the n=0 point condition and the chart-by-chart transfer of finite presentation, so neither is hidden behind the word transport. The source statements and item are consistent; no statement dispute or route departure is necessary.
