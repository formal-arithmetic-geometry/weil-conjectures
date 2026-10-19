# Stage-1 report

## Files written

- dag/nodes/sec-smooth-purity/lem-kun-proper-base-change-torsion-ring.json: split; unchanged statement; explicit coefficient reduction to the existing Z/n theorem.
- dag/nodes/sec-smooth-purity/lem-kun-unbounded-abelian-exchange-comparison.json: statement only, unsplit; no matching Mathlib declaration after both semantic phrasings, both Loogle patterns and source grep. LeanSearch was unavailable, not a negative search result.
- citations.json: verbatim cited statements for every citation in all four proof steps.

## Attachments

None. In WeilConjectures/SixFunctors/Etale/BaseChangeTheorems/Proper.lean, AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring (line 154) has sorry at line 157. The nearby declarations isIso_baseChange_of_isProper and isIso_baseChange_of_isProper_of_isAddTorsion_ring quantify only over D-plus, not the item. The exact-tag search and concept search found no finished unbounded project declaration. The upstream master is reference material only.

## WANTED

None: the required Stacks sources are available locally.

## Problems found

The item is mathematically correct and its statement was preserved. The ancestor blueprint originally begins its torsion-ring projection-formula proof with “Write Lambda=Z/n”, which is not legitimate for arbitrary torsion rings (F_p[t] is a torsion ring and is not Z/n). This item already exists to repair that gap. Restriction along Z/n -> Lambda suffices; no identification of coefficient categories is made.

The existing lem-kun-0f0c statement is exactly the general Z/n unbounded proper-base-change theorem of Stacks 0F0C. Its imported proof incorrectly invokes a finite-type-over-a-field theorem without those hypotheses. I use its statement as a dependency, not that proof: the local source 0F0C proves it for arbitrary schemes by local finite fibre dimension and the finite-cohomological-dimension acyclic-complex argument. This separate node needs its own authorized split. I did not change it or add a duplicate of it.

The bounded-below lem-weil-pbc-exchange-forget-coefficients and module-abelian comparison/coherence nodes do not assert their conclusions for arbitrary unbounded complexes. The new generic comparison precisely isolates that missing tool. It asserts no proper-base-change isomorphism, has no properness or torsion hypothesis, and is not a renamed clause of this item. No flatness of Z/n -> Lambda is used and no claim that forgetting preserves injectives or K-injectives is made.

## Unfinished work

The new comparison is deliberately statement-only, as required for a one-level split. Its future proof must combine the canonical unbounded direct-image comparison of 0D6J(3), the exact inverse-image coefficient comparison, and compatibility with units, counits and the inverse-image square used in 07A7. Exactness alone does not prove the derived direct-image comparison. Conservativity follows by cohomology and the fact that the inverse of a bijective module-linear map is module-linear. Those arguments belong to the future split of this general tool.

## Review by NN

I read etale-cohomology.tex at lemma-projection-formula-proper-mod-n (0F0G) and lemma-proper-base-change-mod-n (0F0C), including the latter's proof. The former uses the latter on geometric fibres although it has a general torsion ring in its statement. The present reduction preserves that source route while explicitly handling the coefficient difference. I also read the ancestor lem-kun-0f0g blueprint and its unit and chapter. There are no unit proof steps to replace and no change to the unit or chapter.

For the new comparison I read sites-cohomology.tex at lemma-modules-abelian-unbounded, especially its canonical map constructed from I -> J and clause (3), and remark-base-change, where the exchange is the adjunct of the pullback-square comparison followed by the counit. The coherence clause is an explicit agent formulation combining these constructions, not a claim that 0D6J itself prints the entire exchange equation. I searched the whole DAG, the blueprint and the project source by coefficient forgetting, unbounded exchange, and the relevant tags. The existing closest comparisons are bounded below or on the pro-etale site. The Mathlib semantic hits concern underived pushforward, pullback and adjunctions; I inspected pushforwardNatIso (PushforwardContinuous.lean:228) and pushforward₀CompToPresheaf (Presheaf/Pushforward.lean:78), which do not assert a derived comparison or exchange equation.

Step 1 uses the definition of module derived categories in def-weil-pbc-derived-categories: a complex and its restriction have exactly the same underlying additive kernel, image and cokernel. The displayed action is well defined because n1=0, and the localization at quasi-isomorphisms supplies the restricted object. This is a short elementary construction, not a new lemma. Step 2 uses the full statement of lem-kun-0f0c: the ring is Z/n, f is proper, g arbitrary, and the complex unbounded. I read that node's statement and verified each of these hypotheses against the source. Step 3 uses precisely the new node's endpoint isomorphisms and its fixed-map equation twice, first for Z/n and then Lambda. The equality of underlying complexes from step 1 makes the abelian map identical in both equations; the inverses of the endpoint maps give the explicit conjugation formulas. Step 4 uses the conservativity asserted in the new node. citations.json copies those statements verbatim, without extending a bounded-below claim to the unbounded case.

I tested the coefficient reduction for n=1 (the zero ring, with only zero unital modules), Lambda=Z/n itself, the infinite ring F_p[t], and nonflat coefficient restriction such as Z/4 -> F_2. None requires preservation of K-injectivity. Empty schemes and identity squares give zero or identity maps with the same endpoint formulas. Arbitrary unbounded representatives are covered because the comparison tool quantifies over the entire D and 0F0C does so as well. The new statement includes no scheme finiteness, invertibility or constructibility hypotheses. I corrected an initially ambiguous target-comparison notation to a fully typed two-arrow composite before writing the final node.

Against delivery-errors B--E, the new node contains only a self-contained statement, its notions have definition dependencies, and its source gives tags and local labels. Searches recorded were actually run and unavailable results remain unavailable. All non-elementary work in the item's steps is cited, and no cited statement is used outside its hypotheses. The only elementary steps are the termwise coefficient construction and the final use of the explicitly stated reflection property. No source fact is smuggled in by a tag alone, no clause of proper base change is moved to a new node, and no other node is edited. The item points to the ancestor projection-formula fibre reduction and the new node records that ancestor through this item.

## Not duplicates
lem-kun-unbounded-abelian-exchange-comparison vs lem-sbc-coefficient-higher-direct-image-zero: only tests degreewise higher-direct-image vanishing for sheaves, under qcqs; the new node identifies the actual unbounded derived exchange.
lem-kun-unbounded-abelian-exchange-comparison vs lem-sbc-restrict-scalars-injective-direct-image-acyclic: asserts acyclicity of restricted injective sheaves, not an unbounded exchange comparison.
lem-kun-unbounded-abelian-exchange-comparison vs lem-sbc-restrict-scalars-pullback-square-comparison: bounded-below inverse-image square identity only, without derived pushforward or exchange.
lem-kun-unbounded-abelian-exchange-comparison vs lem-sbc-base-change-restrict-scalars-arrow: degree-q arrow for sheaves with qcqs hypothesis, not arbitrary unbounded complexes.
lem-kun-unbounded-abelian-exchange-comparison vs lem-sbc-restrict-scalars-derived-adjunction-identities: unit/counit coefficient identities on D-plus, not D or the exchange equation.
lem-kun-unbounded-abelian-exchange-comparison vs lem-sbc-restrict-scalars-derived-exchange: exchange equation only on D-plus, conditional on previously constructed comparisons; the new node is on unbounded D and supplies the canonical comparisons.
lem-kun-unbounded-abelian-exchange-comparison vs lem-sbc-base-change-restrict-scalars-comparison: degreewise sheaf base-change comparison, not the unbounded derived map.
lem-kun-unbounded-abelian-exchange-comparison vs lem-sbc-canonical-restrict-scalars-functor-comparisons: bounded-below coefficient comparisons only.
lem-kun-unbounded-abelian-exchange-comparison vs def-pc-derived-base-change-map: defines the QCoh ringed-scheme map; neither coefficient forgetting nor a comparison theorem.
lem-kun-unbounded-abelian-exchange-comparison vs def-weil-pbc-adjunction-mate: defines general mates, not a sheaf coefficient comparison theorem.
lem-kun-unbounded-abelian-exchange-comparison vs lem-weil-pbc-strict-tower-exchange-mate-normalization: strict pro-etale towers with adic coefficients and properness, not arbitrary small-etale coefficients.
lem-kun-unbounded-abelian-exchange-comparison vs def-weil-pbc-four-arrows: defines the adic finite-level arrows, not an unbounded etale coefficient-forgetting theorem.
lem-kun-unbounded-abelian-exchange-comparison vs prop-weil-pbc-derived-inverse-image-adjunction: bounded-below abelian derived adjunction only, not coefficient comparison.
lem-kun-unbounded-abelian-exchange-comparison vs lem-weil-pbc-module-abelian-derived-direct-image-comparison: bounded-below derived direct-image comparison, no unbounded exchange equation.
lem-kun-unbounded-abelian-exchange-comparison vs lem-weil-pbc-module-abelian-underived-exchange: underived exchange equality for sheaves, not unbounded complexes.
lem-kun-unbounded-abelian-exchange-comparison vs lem-weil-pbc-finite-level-rectangle: specific adic coefficient-reduction rectangle, not the arbitrary-ring unbounded etale exchange.
lem-kun-unbounded-abelian-exchange-comparison vs lem-weil-pbc-module-abelian-stalk-exchange: degree-q stalk comparison of sheaves, not the map on arbitrary unbounded derived complexes.
lem-kun-unbounded-abelian-exchange-comparison vs lem-weil-pbc-exchange-forget-coefficients: the closest theorem but explicitly D-plus throughout; the new tool handles unbounded D.
lem-kun-unbounded-abelian-exchange-comparison vs def-weil-pbc-derived-square-iso: defines inverse-image square isomorphisms without any coefficient or direct-image comparison theorem.
lem-kun-unbounded-abelian-exchange-comparison vs lem-weil-pbc-derived-exchange-unbounded-transport: its object K is bounded below despite allowing unbounded resolution I; all coefficients are abelian, not arbitrary ring modules.
lem-kun-unbounded-abelian-exchange-comparison vs lem-weil-pbc-frobenius-exchange-restriction: pro-etale adic quotient coefficients and Frobenius tower datum, not arbitrary etale coefficients.
lem-kun-unbounded-abelian-exchange-comparison vs lem-weil-pbc-module-abelian-derived-exchange-compatibility: fixed equation on D-plus only; the new node requires unbounded comparisons and conservativity.
lem-kun-unbounded-abelian-exchange-comparison vs lem-weil-pbc-etale-underived-exchange-restriction: underived abelian exchange for etale base change, not arbitrary cartesian base change and unbounded coefficients.
lem-kun-unbounded-abelian-exchange-comparison vs lem-weil-pbc-derived-exchange-bounded-comparison: bounded-below abelian object K and bounded-below source resolution, without coefficient forgetting.
lem-kun-unbounded-abelian-exchange-comparison vs lem-weil-proetale-direct-image-restriction-of-scalars: finite-ring comparison on the pro-etale site, without the etale exchange coherence clause.
lem-kun-unbounded-abelian-exchange-comparison vs lem-fin-coefficients-forgetful-direct-image: finite F_ell-algebra and direct image only, with no arbitrary-ring unbounded exchange equation.
lem-kun-unbounded-abelian-exchange-comparison vs lem-kun-0f0c: proper base change over Z/n is the existing theorem being used; the new node neither assumes properness nor asserts that any exchange is invertible.

## Second reading by NN

- Item statement: checked against etale-cohomology.tex, 0F0C lemma-proper-base-change-mod-n and 0F0G lemma-projection-formula-proper-mod-n, and the actual unbounded exchange definition; PASS. The torsion-ring extension is a coefficient reduction, with every scheme hypothesis preserved.
- Step 1: checked against def-weil-pbc-derived-categories and the explicit action of Z/n on the representing complex; PASS. The action factors through Z/n because n1=0, is compatible with the differential, and changes no additive kernels or images, so localization is legitimate. Elementary.
- Step 2: opened lem-kun-0f0c and compared its statement with 0F0C; PASS. Properness, arbitrary base change and unbounded Z/n coefficients are exactly its scope. Its pre-existing imported finite-type-over-a-field proof error is already reported above; this split cites its statement only.
- Step 3: checked both endpoint composites and the fixed-map equation in lem-kun-unbounded-abelian-exchange-comparison against 0D6J(3), the construction in its proof, 07A7 remark-base-change and def-kun-unbounded-exchange; PASS. Applying the equation for each coefficient ring gives the two displayed conjugations, with correctly typed inverses. The identical underlying representative supplies the identical abelian input, not an assertion that endpoint isomorphisms alone identify exchange maps.
- Step 4: checked the precise conservativity clause of lem-kun-unbounded-abelian-exchange-comparison; PASS. Reflection of the isomorphism proved in step 3 is elementary from that cited clause.
- New node lem-kun-unbounded-abelian-exchange-comparison: checked statement against sites-cohomology.tex, 0D6J lemma-modules-abelian-unbounded (3), and 07A7 remark-base-change; PASS after adding the missing K-injective-definition citation. The coherence equation is the explicitly marked agent formulation, not a verbatim additional clause of 0D6J. It requires no properness and proves no exchange invertibility, so is a strictly separate tool rather than a restatement of the item. It is not elementary: the unbounded pushforward comparison is the substance of 0D6J. All existing nodes listed under Not duplicates were opened; none supplies its full unbounded etale statement. Independent blueprint searches for coefficient forgetting, modules abelian and exchange and DAG searches for 0D6J and unbounded abelian coefficients found no duplicate. Independent msearch queries in three kinds are recorded with actual results; the semantic hits and pushforwardNatIso source are underived, hence no Mathlib leaf.

Small cases checked: the zero complex; the zero coefficient ring (n=1, only zero unital modules); Lambda=F_p and Lambda=F_p[t]; nonflat Z/4 to F_2 restriction; empty schemes; and identity squares. The new node also permits Lambda=Z and Lambda=Q, since it makes no torsion assumption. In these cases conservativity follows from unchanged cohomology and inverse linearity of an additive bijection, and the canonical comparison reduces to the expected zero or identity maps. No n=0 reduction is used: n is expressly positive. No flatness or preservation of K-injectivity by forgetting is used.

Changes: added [def-weil-pbc-kinjective-resolutions] and its statement dependency to the new node (B3); refreshed both verbatim citation quotes; appended the independent search results and this reading. No item statement or proof step needed a mathematical change. Kept all first-worker sections, including Review by NN. The delivery command in the brief has a trailing dot which the installed script rejects; use its documented two positional arguments without that dot, with --no-push for the dry run. No launcher script was modified.
