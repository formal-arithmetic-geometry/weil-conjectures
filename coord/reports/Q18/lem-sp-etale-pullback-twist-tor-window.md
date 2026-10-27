# Q18: lem-sp-etale-pullback-twist-tor-window

## Files written

- `dag/nodes/sec-smooth-purity/lem-sp-etale-pullback-twist-tor-window.json`: statement node, now split into five steps; statement unchanged; no exact Mathlib match.
- `citations.json`: verbatim statement excerpts for every dependency cited in every proof step.
- `report.md`: worker report and signed review.

No new nodes and no new Mathlib leaves. The search command also generated `searches.jsonl` in this sandbox. No Lean, compiler, repository mutation, or git command was used.

## Attachments

None. Searches of `lean/WeilConjectures/` for the item's blueprint tag, Tate-twist/Tor-amplitude terminology, K-flatness, and flat constructible pullback models found no declaration stating the entire item. The existing flat-model existence theorem in `SixFunctors/Etale/Derived/Finiteness/FlatModel.lean` and bounded-constructible theorem in `FlatConstructibleComplex.lean` cover components, rather than the given representative after arbitrary scheme pullback, the specified roots-of-unity line, and an arbitrary signed shift. They do not qualify as an attachment of this item. Structure-sheaf pullback theorems concern different coefficient categories.

## WANTED

None. All sources used are present in `literature/`.

## What needed repair

The item's statement is sound, but its proof was empty. Its source listed `lemma-pullback-ctf` without the tag; the proof sources now identify Tag 0963 and its label. The important simplification is reuse of `lem-sp-etale-pullback-line-flat-model`, an existing same-unit statement for an arbitrary locally trivial rank-one sheaf. Creating separate pullback/flatness/line-model nodes here would duplicate it. The final phrase about pullback preserving the interval for every bounded constructible finite-Tor object also requires existence of a representative; it is not enough to reason conditionally on a supplied representative. Step 5 therefore cites the existence clause of the already present `lem-sp-etale-scalar-flat-model`, specialized to the identity coefficient map.

The formula in the arbitrary-line node writes its target with the shift on the second tensor factor. Step 3 explicitly cites the existing Mathlib total-tensor shift node and the K-flat representing formula to move that shift to the whole derived tensor. This prevents an unstated shift identification. The original statement is unchanged; there is no statement dispute.

## Not duplicates

There are no newly created nodes to compare. The DAG and blueprint searches found the following facts to reuse:

- `lem-sp-etale-pullback-line-flat-model`: more general than the main assertion, since its line is arbitrary; already in the same unit. It is cited, not recreated.
- `lem-sp-etale-scalar-flat-model`: supplies flat-model existence on a Noetherian scheme; cited only for this existence clause in Step 5.
- `lem-asd-finite-etale-twist-line`: supplies local triviality for exactly the roots-of-unity scalar extension and its tensor powers used here.
- `lem-weil-pbc-finite-type-over-noetherian` and `lem-weil-pbc-total-tensor-integer-shifts`: existing Mathlib leaves for the scheme and signed tensor inputs.

I searched the entire DAG by the tags 03TT, 095I and 0963 and by bounded-flat, inverse-image, pullback and constructibility language. `tools/blueprint_refs.py` searches included `pullback twist`, `flat constructible`, `flat line` and `twist`, and its ancestor command identified `det-sp-reduction-exceptional`. The matching blueprint flat-model statements concern existence or the pro-etale setting, rather than the complete ordinary-etale given-representative statement here. The exact existing arbitrary-line generalization is a created node, not another blueprint node, so the item's `same_as` remains empty.

## Mathlib search results

I retained the inherited searches and added the five actual Q18 search-command records: two differently phrased LeanFinder queries, a Loogle query, a whole-Mathlib grep query, and LeanSearch. Both semantic searches returned ordinary module tensor exactness/flatness and related general category results. LeanSearch likewise returned module-flatness and scheme-flatness results. Their displayed types do not assert constructible small-etale complexes, the specified finite Tate line, K-flat representative comparisons, or the shifted Tor interval. Loogle and grep returned zero hits. The item is not a one-line specialization of these results. No unavailable service has been recorded as a successful negative search.

## Review by Q18

I read the current unit record and its current blueprint source, `main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-reduction/_section.md`, as well as the Charts paragraph of `sk-lem-sp-reduction-exceptional.proof.md`. This item supplies the domain/finite-Tor check for the chart expression in retained Steps 5--6. The split keeps that route. It works entirely with ordinary constant-ring module sheaves on small etale sites; it does not identify these categories with condensed or pro-etale categories. The relevant source arguments are the finite-complex proof of Stacks 0963 (`lemma-pullback-ctf`), the existence and finite-complex directions of 03TT (`lemma-when-ctf`), and the finite twist in 03PK (`section-kummer`) with groupoids Example 040M (`example-roots-of-unity`). I also read the constructible-tensor statement and its refinement argument at 095I. There are no new nodes whose sources need a separate review.

For Step 1 I opened the complete statement of `lem-weil-pbc-finite-type-over-noetherian` and the proof of `morphisms.tex`, `lemma-finite-type-noetherian` (01T6). It says precisely that a finite-type source over a Noetherian target is Noetherian. The target here really is Noetherian: a field has only the ideals zero and the whole ring, and its spectrum has one affine chart and one point. Thus the finite-type hypotheses in the item give both Noetherian schemes required below. I checked the definition in `properties.tex`, `definition-noetherian` (01OV); no assumption that the field is perfect or algebraically closed enters.

For Step 2 I opened the complete statement of `lem-asd-finite-etale-twist-line`. Its conclusion includes an actual etale cover trivializing every nonnegative power of exactly the displayed scalar extension of roots of unity. Its hypothesis is invertibility of N in every local ring, not any flatness of R over Z/N. The integer ell is nonzero in the characteristic-p field, so its power is invertible there and maps to a unit in every local ring. This also covers n=0, when N=1. The given NR=0 and finite commutative R match its coefficient hypotheses. This node is the sole off-unit theorem used as a generic tool, declared in `split_report.tool_uses`; it supplies the line input for the same-unit model theorem.

For Step 3 I opened the entire statement of `lem-sp-etale-pullback-line-flat-model`. It explicitly allows every morphism between Noetherian schemes, every finite commutative coefficient ring, every representing isomorphism for a flat constructible complex supported in [a,b], every etale locally trivial line, and every integer shift. Thus the substitution X=T', Y=T, f=u, C=P, E=R(c), r=s has all its hypotheses established before application. Its conclusion explicitly states the K-flatness, terms, support, and derived isomorphism being taken from it. I separately read `lem-weil-pbc-total-tensor-integer-shifts`, Mathlib `Algebra/Homology/BifunctorShift.lean` at its first and second shift isomorphisms (lines 95 and 156), and the K-flat representing formula in `def-kun-derived-tensor`. The second-variable comparison has the degree sign (-1)^(sp), so moving E[s] to the outside is a chain isomorphism before localization. This is a derived-object comparison, not a collection of per-degree cohomology isomorphisms. The support is [a-s,b-s] because the shifted term at j comes from j+s.

For Step 4 the additional conclusion of the same arbitrary-line node explicitly asserts constructible cohomology and vanishing after derived tensor with every degree-zero module sheaf in the desired interval. I compared this quantifier with the full statement of `def-kun-tor-amplitude`; it is the same condition, without a constructibility restriction on the test module. `def-weil-pbc-derived-categories` defines boundedness by finitely many nonzero cohomology sheaves. The zero terms outside the given finite interval make the cohomology zero there directly. This step is elementary because it reads off already cited conclusions and the two definitions; it does not claim that boundedness by itself implies finite Tor amplitude.

For Step 5 I read the whole statement of `lem-sp-etale-scalar-flat-model`. Its first conclusion is existence of P on a Noetherian scheme with finite coefficient ring, and all those hypotheses hold here. Taking the coefficient map to be the identity imposes no new hypothesis on R. I then checked the arbitrary-line theorem again with the constant line and shift zero. The identity cover trivializes the constant line, and the two displayed tensor-unit maps are inverse termwise, proving that the represented object is u*K. This establishes the final preservation assertion for any K, even if no representative was initially selected.

I checked B1--B10, C1--C8, D1--D5 and E1--E7 against these files and sources: no new statement-only node is disguised as a proof, no new elementary or duplicate node is created, and no new lemma restates a clause of the item. Every non-elementary input in the five steps is an existing cited statement. For C4 I compared every quoted clause directly with the source node's statement and generated `citations.json` with literal-substring assertions. The only bridge added during this review was the explicit total-tensor shift citation in Step 3. The same-unit scalar and arbitrary-line nodes have no dependency back to this item; no circular proof is introduced. The borrowed finite-type and shift inputs are existing Mathlib leaves; the Tate-line tool is explicitly declared. Each proof step is shorter than 2000 characters.

Small cases checked: empty T' gives the zero module category and no problematic nonempty-cover requirement; R=0 gives zero complexes and valid rank-one local trivializations over the zero ring; N=1 forces R=0; c=0 is the constant unit line; a=b leaves a single flat term; a positive shift sends that term to a-s, and a negative shift moves it upward. None requires R to be a field, nonzero, or flat over Z/N, and no finite projective dimension is assumed.

## Unfinished work

None in the authorized one-level split. The existing unsplit nodes used as dependencies remain separate queued items; I have not claimed their proofs finished.
