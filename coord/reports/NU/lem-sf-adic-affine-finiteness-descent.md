# Stage-1 delivery: lem-sf-adic-affine-finiteness-descent

Group NU; direct delivery; 2026-10-22. Only this sandbox was written. No Lean, compiler, Lake, build, or repository git command was used.

## Files written

- `dag/nodes/sec-six-functors/lem-sf-adic-affine-finiteness-descent.json`: split, eight proof steps; original conditional statement retained.
- `dag/nodes/sec-six-functors/lem-sf-native-adic-bounded-constructible-triangulated.json`: statement, unsplit; no Mathlib match. Triangulated closure for the actual locally finite continuous coefficient modules on a locally Noetherian scheme.
- `dag/nodes/sec-six-functors/lem-sf-native-adic-open-derived-localization.json`: statement, unsplit; no Mathlib match. Exact open restriction, cover conservativity, and the derived open base-change isomorphism for those modules.
- `dag/nodes/sec-six-functors/lem-sf-native-adic-mayer-vietoris-triangle.json`: statement, unsplit; no Mathlib match. A derived-category triangle for an arbitrary complex under a two-open source cover.
- `citations.json`: a verbatim statement quote for every use in every numbered step. Whole statements were copied so that their hypotheses remain visible.
- `searches.jsonl`, `search-results.jsonl`, `search-plan.json`: actual msearch invocation records and the corresponding returned hits. The two sandbox Python scripts reproduce the searches and write the JSON; they are working material, not requested repository files.

Three new nodes; zero new Mathlib leaves. New unsplit nodes have no proof, proof dependencies, or proof origin. Their statements introduce their schemes, coefficient rings, categories, functors and relevant hypotheses independently.

## Attachments

None. Searches of `lean/WeilConjectures/` by the exact blueprint tag, item id, adic finiteness, and Mayer-Vietoris found the source `SixFunctors/ProEtale/Adic/LowerStar.lean`, but no finished declaration of this conditional assertion. Its `finiteLowerStar_singleFunctor_of_isAffine` has `sorry`; the unconditional finiteness declarations use it. Their existence is not evidence of an attachment. The existing conditional cover lemmas are source material for the proof, not a declaration of the whole item with exactly its quantified affine hypothesis.

## WANTED

None. The item is a conditional extraction from the available Lean source. I reconstructed that extraction and marked its proof origin `agent`. No SGA source was used. In particular, an unconditional affine finiteness theorem was neither cited nor reconstructed here.

## What was wrong or incomplete

The initial item had no proof. Its existing Mathlib searches were retained, and the new queries were added. Its statement needs no repair: it is conditional on affine finiteness and includes the target quasi-compactness that makes local bounds uniform. No statement dispute was found.

The important distinction is between an arbitrary quasi-separated source and a separated source. One cannot assert that its affine opens have affine intersections. The proof first treats a quasi-compact open contained in a fixed affine open, then uses the class of such opens to handle the quasi-separated source. Quasi-compactness of intersections is proved by finite affine covers and the existing quasi-separated criterion. This avoids silently adding separatedness.

The inherited blueprint ancestry terminates at a maintainer seed. `tools/blueprint_refs.py ancestor lem-sf-adic-affine-finiteness-descent` returned `None`. I preserved its null ancestor and its existing creation chain, gave precise places in the package clause served by each new node, and prepended the item to the new nodes' `via` lists. There is no invented imported ancestor or change to a chapter/unit route.

## Searches and source reading

I read `GOAL.md`, the three-level restriction in `SETUP.md`, stage 1, the worker brief, the six-functors chapter and package unit, and delivery-errors B through E in full, including the merged copy. I read the available current package proof and the ordinary-direct-image finite-cover paragraph in the current `sk-prop-sf-finiteness` proof for context. The actual conditional argument follows the inspected `LowerStar.lean` declarations rather than any unconditional literature input mentioned in those files.

Before creating nodes, I searched the full DAG by native/adic coefficients, affine-cover finiteness, Mayer-Vietoris, derived open exchange, constructible kernels, and the source declaration names. Blueprint searches included `finiteness`, `Mayer`, `Mayer Vietoris`, `adic constructible`, `constructible kernels`, `open base change`, `derived open`, `locally finite continuous`, and `bounded constructible`. None states a new node's native-coefficient assertion. Existing scheme and generic derived-category results were reused instead of recreated.

For every new node I ran leanfinder, loogle, grep and leansearch using its own mathematical assertion, then a second semantic phrasing. All queries and their actual outputs are saved. Some Loogle queries returned unknown identifiers; these are recorded as query failures/no usable hit, not as a declaration match. The services themselves responded. The triangulated searches return the standard derived t-structure and triangulated category, but do not supply native constructibility closure. The localization searches return ordinary scheme structure-sheaf restriction or condensed module constructions, not this pro-etale ringed-site exchange. Mayer-Vietoris searches return squares and an abelian-sheaf cohomology long exact sequence, not the derived triangle for these module sheaves under arbitrary direct image. I opened the relevant Mathlib MayerVietorisSquare and SheafCohomology/MayerVietoris files to check that distinction. No generic hit specializes to the entire new statement in one line.

## Not duplicates

lem-sf-native-adic-bounded-constructible-triangulated vs lem-sf-native-weil-constructible-abelian: the latter concerns Frobenius-equivariant sheaves over a finite field; it does not state triangulated closure for underlying native module sheaves on an arbitrary locally Noetherian scheme, including schemes in characteristic zero.
lem-sf-native-adic-bounded-constructible-triangulated vs lem-sfb-dc-ell-adic-triangulated: the latter uses condensed coefficient internal modules and stratified finite presentations, not the locally finite continuous coefficient sheaf used here; their equivalence is not assumed.
lem-sf-native-adic-bounded-constructible-triangulated vs lem-sfb-adic-constructible-triangulated: the latter is a residue-constructibility property for completed integral coefficients, not this rational native module category.
lem-sf-native-adic-open-derived-localization vs lem-sf-native-adic-open-restrictions: the existing node gives restriction of open extension by zero and disjoint-support vanishing; it does not give derived direct-image open exchange or joint conservativity.
lem-sf-native-adic-open-derived-localization vs lem-sf-native-adic-constructible-pullback: the existing node gives constructibility under pullback, not exactness, cohomology comparison, open exchange or cover detection. It is separately cited where used.
lem-sf-native-adic-mayer-vietoris-triangle vs lem-pc-relative-mv-pinned-triangle-comparison: the latter concerns quasi-coherent structure-sheaf complexes and a relative base-change presentation, not this native pro-etale module category.
lem-sf-native-adic-mayer-vietoris-triangle vs lem-kun-0f10: a cohomological-dimension/finiteness result for field schemes does not state a derived module-sheaf Mayer-Vietoris triangle.

The new nodes use the inspected project source as their source, so they introduce no shared Stacks-tag source pairs. The geometry citations retain their own precise Stacks tags and labels; no section number was substituted for a tag. None of the three new statements is the conditional affine-to-qcqs finiteness theorem or a restatement of one of its conclusions: none assumes affine finiteness and none concludes finiteness of a general pushforward.

## Review by NU

I checked the argument against `LowerStar.lean` at its triangulated finiteness property, `finiteLowerStar_of_bounded`, `finiteLowerStar_of_openCover`, `FiniteFor.finsetSup`, `FiniteFor.of_quasiSeparatedSpace`, and the target localization and boundedness proofs. I did not use its affine theorem. I also inspected `BaseChange.lean` at `adicDerivedBaseChangeIso`, `Module.lean` at exact upper star, and `MayerVietoris.lean` at cover conservativity and the cone vanishing argument. For the new triangulated assertion I read `Abelian.lean` at constructible kernel/cokernel closure and `Extension.lean` at short-exact extension closure, together with the zero/finite-product statements in `Constructible.lean`. These are native module results; they do not identify discrete, completed, condensed or Frobenius-equivariant coefficient categories.

Step 1 uses exactly the locally finite-type/local-Noetherian statement of `pqf-lem-locnoeth-lft`, the small-ringed-site K-injective theorem `prop-pur-kinjective-resolutions-exist`, the generic triangulated right-derived-functor theorem, and the new native triangulated-closure statement. I checked smallness from the item's chosen representative, commutativity of the function ring pointwise, and additivity/left exactness from the direct-image definition. Local Noetherianity is obtained from the field and is the hypothesis required by the new closure node.

Step 2 cites the actual cohomological truncation triangle and truncation cohomology statements, not the existing bounded-complex lemma about terms of a complex. That distinction matters: the hypothesis is constructibility of cohomology, not of chosen complex terms. The finite induction has the zero base, the shifted cohomology objects, and the final truncation isomorphism explicitly. Triangulated right derivation and target closure are cited again. The affine hypothesis is used exactly for affine source and affine target locally finite type over K.

Step 3 uses exact open restriction from the new localization node, the existing native constructible-pullback theorem, and the actual derived Mayer-Vietoris triangle, with target triangulated closure. Its three finiteness assumptions are on the two restrictions and their overlap. Step 4 is the written strong induction using that same two-open triangle: the overlap is a union of at most one fewer intersections, all in the stated intersection-closed class. It uses no unmentioned finite-cover finiteness theorem.

Step 5 uses `lem-weil-pbc-qcqs-over-affine` only when the target is affine. I checked the quasi-compact-open inclusions with the quasi-separated ambient source before using the finite-type open-immersion and composition nodes. The finite affine cover of a quasi-compact open is exactly what `lem-pqf-finite-affine-cover-qc-open` states. I applied the separated affine-intersection result to the ambient affine A over Spec Z, which is separated by the existing affine-source theorem; I never applied it to the general source T. Step 6 cites the quasi-separated affine-cover criterion for quasi-compact intersections and the finite-affine-cover node for a quasi-compact whole scheme. Finite unions of the finitely many pairwise intersections give the explicit compactness check; this is elementary topology, not an unproved affinity claim.

Step 7 uses finite-type base change and quasi-separated base change exactly as stated in the cited geometry nodes. It uses the existing native pullback theorem only for constructibility and the new open-localization statement for exactness and the derived isomorphism. I checked that the target affine opens remain locally finite type over the same field, and that the coefficient action in the base-change isomorphism is the precomposition action in the item.

Step 8 is elementary gluing after step 7: exactness identifies restricted cohomology, the given definition glues constructibility, finite minima/maxima give one interval, and joint conservativity detects the zero sheaf outside it. The elementary label is for that explicit gluing, not for an uncited finiteness theorem. Every cited node was opened and its statement checked; `citations.json` contains literal statement text, with no paraphrased quote substituted.

I tested empty source and target, the zero complex, empty cohomology intervals, repeated cover members, disjoint open covers, and a cover with one member equal to the whole scheme. For the structural statements, a one-point scheme reduces the new closure assertion to bounded finite-dimensional coefficient modules; the open exchange is the identity for the whole open and is zero for the empty open; the Mayer-Vietoris triangle becomes C -> C -> 0 when one member is empty. The nonseparated case is handled by quasi-compact overlaps and the inner affine cover, not by an unallowed separatedness hypothesis. No step exceeds 2000 characters. I checked that the new nodes are unsplit statements only and that proof_deps is exactly the union of step uses.

Generic tools outside the unit are declared in split_report.tool_uses: the K-injective existence theorem, triangulated right derivation, and the cohomological truncation triangle. They supply the underlying derived-category construction, not an alternative route to the unit's finiteness conclusion. The existing Mathlib geometry leaves are tools in their own right.

## Unfinished work

No part of the one-level split remains unwritten. The three new structural nodes are deliberately statement-only items for later work. Server dry-run validation and delivery results are recorded below after running the required tool.

## Validation

The first required dry run exited successfully: `OK (not pushed) deliver/NU/lem-sf-adic-affine-finiteness-descent at 67cc98c9f9a: preflight passed`. This included the server DAG and split checks, citation verification, and actual Mathlib search-log verification. After recording this result and including the two initial item search invocations in its search list, I requested a final dry run before the direct push. The delivery tool output is the authoritative record of the final commit.
