# def-pur-td-datum — NC, stage 1, 2026-10-26

## Files written

- `dag/nodes/sec-smooth-purity/def-pur-td-datum.json`: definition, split; no Mathlib match. Preserves both datum arrows, the functor, the displayed unit and counit, and both triangular endomorphisms. Names the canonical comparisons used in those formulas and proves the functor has the claimed finite-Tor domain using existing nodes.
- `citations.json`: four verbatim statement quotations for the four nodes used in proof step 1.
- `searches.jsonl`: the original records produced by the required msearch command; seven searches, two semantic phrasings, with no exact match.
- `report.md`: this report. `prepare.py` is a sandbox-only preparation/checking script, not a project file.

There are **0 new nodes and 0 Mathlib leaves**.

## Attachments

None. I searched `lean/WeilConjectures/` for the id and for the notion. `AlgebraicGeometry.Etale.TraceDiagonalDatum`, its `functor`, `unit`, `counit`, `leftTriangle` and `rightTriangle` occur in `WeilConjectures/EtaleCohomology/Purity/Smooth/TraceDiagonal.lean`, lines 96–165. I read those definitions and `TraceDiagonal/Basic.lean` lines 65–278. These concern ambient unbounded small-etale module derived categories with a finite ring, not the complete item with its restrictions to the finite-Tor constructible categories and its coefficient conventions. The ambient definitions alone do not establish those restrictions. I therefore make no ATTACH claim and do not use their source text as a proof of the item.

## WANTED

None. The definition and its sole functoriality proof are present in the current blueprint, and all required construction notions and supporting statements already have DAG nodes.

## Audit of the imported material

I read AGENTS.md, the standing stage-1 brief, worker role, stage-1 contract, GOAL.md, SETUP.md (especially its three blueprint levels), delivery-errors B–E in full, and the chapter/unit records. The item is not the key statement of `sk-prop-a1-inv`, so no unit realization fields are changed. The current blueprint is `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-a1-inv/def-pur-td-datum.md` and its `.proof.md`; I used these rather than an old snapshot. Its statement agrees with the live `blueprint_update` except formatting/order. I retained the update and import metadata.

The prescribed archive-directory query found no earlier attempt of this item. The active sandbox held only dispatcher markers, so I copied the live item before editing. There is no repair note or lead note for the item.

The imported definition gave its isomorphisms without naming projection, compact-support base change, compact-support composition, or the pullback section comparisons. Merely citing tensor functoriality did not show that the displayed functor lands in the stated full subcategory. These omissions are repaired by existing dependencies and by the single proof step; no theorem is relabelled as a new node. The explicit finite-stage sentence repeats the final convention of the live `def-pur-conventions`: direct constructions are at finite coefficients, and higher-coefficient forms are supplied by the chapter's coefficient transport. The two arrows and all displayed composites are retained; no hypothesis on the trace or diagonal class has been added, and the triangular identities are not imposed on a datum.

During dependency review I checked transitive paths and found that the broad summaries `thm-sf-ctf-stability` and `fix-prop-projection-formula` reach this item through the projective-line adjunction argument. They cannot be used here. Instead this split uses the narrower `lem-sf-pullback-tor-amplitude`, `lem-sf-tensor-ctf`, `lem-sf-native-finite-tor-preservation` and `lem-weil-finite-compact-projection-formula`, which do not reach the item. Every proposed dependency was checked for a path back to the item before writing it.

## Not duplicates

No new nodes. The whole-DAG and whole-blueprint searches for “trace–diagonal” and “diagonal datum” found this definition and `thm-pur-td-criterion`. The latter assumes the datum and triangular identities to deduce an adjunction; it is not another definition of these data. Existing projection, preservation, origin and comparison lemmas are reused, not restated as new nodes.

## Review by NC

I read the current item and proof against their latest blueprint text. There are no new nodes, hence no new lemma sources to certify. For the one proof step I opened all four cited node files, rather than using their titles or proofs: `lem-sf-pullback-tor-amplitude` explicitly states preservation of the same pro-etale finite-Tor constructible subcategories; `lem-sf-tensor-ctf` clause (ii) explicitly states closure for two such inputs; `lem-weil-derived-tensor-functorial` explicitly preserves identities and composites on pairs of derived morphisms; and `lem-sf-native-finite-tor-preservation` clause (i) explicitly puts the compact-support image back in the finite-Tor constructible category. Thus the first three type the functor and its action on maps, and the fourth types both iterated triangular composites. The global finite-field coefficient datum supplies the finite ring killed by an invertible positive integer, finite-type targets and compactifications required by the last statement. No unrestricted pro-etale exceptional adjunction is invoked.

I separately opened and read the statements of every construction dependency. The fibre-product universal property gives the diagonal and the two section equations. Separatedness means that this diagonal is closed; `lem-weil-pbc-closed-immersion-proper` states that it is proper, in particular separated finite type, so projection and composition apply. The projections are base changes of the given separated finite-type map. All schemes are finite type over the fixed field, hence quasi-compact and quasi-separated; the finite ring is Noetherian. The finite-Tor object condition therefore satisfies the local-Tor constructible-origin theorem, `lem-sfb-constructible-local-tor-etale-origin`, which supplies finite-Tor etale representatives, exactly the witness required by the pro-etale form of `lem-weil-finite-compact-projection-formula`. This avoids assuming that geometric stalks detect arbitrary pro-etale complexes. The same origin supplies the bounded-below witness required by `thm-cbc-finite-level-proetale` for the self-square. Its target is precisely `Rp_{2!}Lp_1^*`, not an incorrectly interchanged projection.

For the first unit isomorphism, projection for the closed diagonal has input the coefficient unit on X and external object `Lp_1^*A` on W. The canonical pullback composition, canonical constant-ring compatibility, and pullback identity statements identify `LDelta^*Lp_1^*A` with A using `p_1 Delta=id`. Compact-support composition and `p_2 Delta=id` then identify the result with A. Identity shriek is computed with the trivial compactification, so no chosen identification is hidden. The last unit isomorphism is inverse projection for p2, with external finite-Tor object L, then inverse compact-support exchange. The counit uses inverse projection for f, trace, and multiplication by the coefficient unit. Signed symmetry is supplied by `lem-pur-derived-tensor-additive-constraints`; unit multiplication on a K-flat representative is an isomorphism term by term, so it introduces no additional theorem node. Naturality follows because each component used is a natural comparison and the middle maps are functor images of tensor with the fixed trace or class.

I checked the edge cases f=id, an empty source (all the displayed endomorphisms are then on zero objects where appropriate), zero trace or zero diagonal class, and L the coefficient unit. The formulas remain typed; zero arrows are legitimate data and are not made into adjunctions by the definition. For f=id the formulas reduce to multiplication by the specified trace and class under unit identifications, confirming that no triangular identity has accidentally been required. In particular no smoothness, properness of f, or orientation assumption is used. Invertibility is the existence of a tensor inverse; the construction does not secretly choose one or use a duality theorem.

For delivery-errors B I checked JSON/TeX, preserved metadata, blueprint references and actual search records. For C I checked exact statements and the four verbatim quotations, route-tool declarations and absence of dependency cycles. For D no new node is a clause of this definition, and the functoriality argument is carried by the item itself. For E I checked the domains, all map directions, both projection indices, and the finite-versus-higher-coefficient convention. The sole proof step is below 2000 characters. No SGA source is used, and no Lean file or compiler/build tool was touched.

## Unfinished work

None within this one-level definition split. The independent maintainer review remains the delivery protocol's next review.
