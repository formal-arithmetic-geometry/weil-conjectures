# Stage-1 worker report: def-sfb-eta

## Files written

- `dag/nodes/sec-proetale-coefficients/def-sfb-eta.json`: existing definition, split using three existing definition dependencies; no new nodes, no Mathlib leaves.
- `citations.json`: `[]`, since this explicit definition has no proof steps.
- `searches.jsonl`: required search command's append-only log; the node records the six searches executed during this repair.

## Attachments

None. Searches in read-only `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `Comparator` for `def-sfb-eta`, `condensedPushforwardHom`, `condensedPullbackHom`, and condensed/pushforward terminology found no declaration stating the item. The upstream-name index supplied no attachment. Upstream master `WeilConjectures/SixFunctors/ProEtale/ModuleObject/Basic.lean:415-420` has the intended definition but is reference material, not evidence of a completed proof.

## WANTED

None. This definition is sourced directly to the blueprint; it needs no Stacks theorem and uses no SGA source.

## Corrections and split

The mathematical definition is unchanged: for an arbitrary scheme morphism and a possibly noncommutative condensed ring, eta is the unit at the coefficient object on Y followed by pushforward of alpha. The imported citation `sk-def-sfb-finite-pushforward-pullback` has no DAG node. The earlier attempt correctly replaced that aggregate citation with `def-sfb-finite-upper-lower-star-adjunction`. I retained that repair and explicitly cited `sk-def-sfb-pulled-back-coefficients` for the objects and specified that the adjunction acts on abelian sheaves. No hypothesis or additional property was added.

The new snapshot has no chapter/unit fields on this item and no corresponding `dag/chapters/sec-proetale-coefficients.json` or `dag/units/sk-def-sfb-coefficient-morphisms.json`. I read the corresponding current blueprint `_section.md` files directly and left maintainer metadata untouched. The item realizes the eta definition in that unit; it is not the aggregate unit's key node, so there is no unit realization file to write.

## What remains

No mathematical work remains for this one-level definition split. The fresh second reader should inspect these files and run the delivery tool; this worker only runs `--no-push`.

## Review by Q66

I read main-20261015 `sec-proetale-coefficients/_section.md`, `sk-def-sfb-coefficient-morphisms/_section.md`, its `def-sfb-eta.md`, and `sk-def-sfb-finite-pushforward-pullback/_section.md`. The chapter supplies the pro-étale coefficient framework. The unit defines alpha by composition of pullback from the point and eta as its mate; the individual item requires precisely that formula. It does not assert the later ring-hom or composition properties. The upstream master formula at Basic.lean:415-420 agrees with this, but was not treated as an attachment.

I opened the statements of all three direct dependencies. `def-sfb-alpha` gives exactly alpha_f from f^*Lambda_Y to Lambda_X. `sk-def-sfb-pulled-back-coefficients` defines Lambda_X as p_X^*Lambda in abelian sheaves and defines a condensed ring as the corresponding ring object at the point; it also explicitly allows noncommutative rings. `def-sfb-finite-upper-lower-star-adjunction` gives the natural equivalence Hom(f^*F,G) = Hom(F,f_*G) for every scheme morphism. Its functor dependencies specify Grothendieck abelian coefficients, so choosing Ab gives the required category. I also read slopmaster2 UpperLowerStar/Defs.lean:213-240 to confirm which functors the adjunction names. There is no finiteness restriction on f despite the dependency's id. The first arrow therefore ends at f_*f^*Lambda_Y and the mapped alpha starts there and ends at f_*Lambda_X, so the composite is well typed.

There are no proof steps: this is an explicit composition of available arrows, not a theorem with an omitted proof. In particular the mate wording is exactly the forward-map definition of `CategoryTheory.Adjunction.homEquiv`, read at Mathlib/CategoryTheory/Adjunction/Basic.lean:159-170. It creates no extra non-elementary proof dependency. Thus C1/C3/C4 have no hidden proof-step citations and the empty citations file is exact. The three statement citations were checked against their actual statements, rather than against arguments inside their proofs.

I searched the whole DAG for the declaration and coefficient-morphism terminology and ran whole-blueprint searches for `condensedPushforwardHom`, `mate`, and `eta_f`, as well as the ancestor command. The aggregate `sk-def-sfb-coefficient-morphisms` contains this definition together with alpha and their ring properties, and its proof cites this item, so it is not a replacement dependency. The ring-hom, identity and composition nodes are subsequent properties, not duplicate definitions. No other node states exactly this definition, hence `blueprint.same_as = []`. No new node was introduced: B1/B5/B6/B8 and the per-new-node duplicate pairs do not arise; there is no restatement child, transferred proof, or new cycle as in D1-D4.

I repeated Mathlib searches exclusively through msearch.py: LeanFinder with two semantic phrasings, LeanSearch, Loogle for Adjunction.homEquiv_apply, and two grep patterns. All six calls returned successfully; exact queries and actual hit lists/counts/digests are recorded in the node and the tool log. I read the generic mate formula and the candidate module-unit maps in Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackFree.lean:40-101. Those module maps require a ringed-site coefficient morphism phi as input; here eta is that kind of coefficient map being constructed on underlying abelian sheaves from the separately defined alpha. They therefore do not supply a Mathlib leaf for this item. The second phrasing also returned scheme structure-sheaf maps, which concern different coefficients and sites.

For E1/E2/E4 I checked the zero condensed ring, an empty source scheme, and an identity morphism. In every case the unit at Lambda_Y and pushforward of alpha have matching middle object; the definition uses no nonemptiness, commutativity, finiteness or smoothness assumption. No identity or vanishing theorem is needed to form the map. The only change beyond the earlier citation repair was to make the coefficient objects/category explicit and refresh the searches. No statement dispute or route departure was found. The previous attempt's second-reading text was replaced with this worker's own source-based check, so the next fresh reader can sign independently.

## Validation

The final validation is `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q66 def-sfb-eta --no-push`; READY is reported only after it prints OK. Nothing is pushed by this worker.

## Second reading by Q66

- Item statement: read current main-20261015 `def-sfb-eta.md` (order 1562) and the parent coefficient-morphisms section (order 857), comparing arbitrary scheme morphism, arbitrary condensed ring, both arrow endpoints, the unit and the mate description; all agree, with no extra commutativity or finiteness hypothesis. No Stacks tag is claimed: this definition's source is the blueprint.
- Definition/composition (there are no proof steps): opened `def-sfb-alpha`, `sk-def-sfb-pulled-back-coefficients` and `def-sfb-finite-upper-lower-star-adjunction`; their statements supply respectively the map from f^*Lambda_Y to Lambda_X, both coefficient objects in abelian sheaves, and the adjunction for every scheme morphism. Also read `def-sfb-finite-upper-star` and `def-sfb-finite-lower-star` to check the coefficient-category hypotheses. The unit has target f_*f^*Lambda_Y, precisely the domain of f_*alpha_f. Verdict: well typed, with no hidden theorem citation (C1/C3/C4/E1).
- Mate wording: read Mathlib `CategoryTheory/Adjunction/Basic.lean:159-170`; its homEquiv sends a map a to unit followed by the right adjoint's map of a. Verdict: the alternate description is the definition of this equivalence, not an additional proof obligation. Empty `proof`, `proof_deps` and `citations.json` remain correct.
- New nodes: none. B1-B7 and the per-new-node source/duplicate tests are vacuous. Independently searched the blueprint index for `def-sfb-eta`: the other hits are its identity, composition and ring-hom properties, not replacement definitions. No restatement child or new proof dependency is introduced.
- Independent Mathlib search: ran LeanFinder via msearch.py with “Canonical coefficient sheaf homomorphism obtained by applying the right adjoint hom equivalence to an inverse image comparison isomorphism”; the actual eight hits are appended in `searches.jsonl` (digest ffdc646ac434dac4). Read `SheafOfModules.pullbackObjUnitToUnit` and its mate lemma at `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackFree.lean:40-101`; they take a ringed-site map phi as input and concern module unit objects, so do not construct this abelian coefficient map. Verdict: no leaf or new node needed.
- Attachment check: searched the read-only slopmaster2 `WeilConjectures` and `Comparator` for the item id and both condensed coefficient-map names, with no hits. Read upstream master `ModuleObject/Basic.lean:415-420` as a formula check only; it is not treated as a completed proof or attachment.
- Edge cases (E1/E2/E4): zero condensed ring, empty source scheme, identity morphism, and schemes over a field all retain the identical matching middle object f_*f^*Lambda_Y; none requires a nonzero coefficient, nonempty scheme, finite map or commutative ring. No assertion about invertibility or identity of eta is being proved here. Verdict: no statement dispute.

Changes: retained the correct node and the first worker's review unchanged; appended this independent reading and one genuinely executed search. No mathematical or dependency repair was necessary. Validation and delivery use the prescribed delivery tool only; no Lean or compiler commands were run.
