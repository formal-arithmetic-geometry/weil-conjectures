## Files written

- `dag/nodes/sec-smooth-purity/lem-exc-proetale-open-derived-image.json`: split statement, seven proof steps; no Mathlib match for the entire statement.
- `citations.json`: verbatim statement excerpts for all twenty step/node citations.

## Attachments

None. I searched the supplied slopmaster2 `WeilConjectures/` tree for the exact id and blueprint tag and for restriction/K-injectivity, then inspected the pro-etale derived and open-immersion infrastructure. Its generic preservation and derived-adjunction declarations do not state every clause of this finite-ring sheaf statement. Adic-sheaf statements and Zariski structure-sheaf statements have different coefficient categories. No ATTACH is claimed. Upstream master sorry declarations were not used as completed proofs.

## WANTED

None. The sources needed for this split are present locally.

## Corrections and scope

The item was an unsplit hidden lemma extracted from `lem-exc-proetale-support-triangle`. I preserved its statement and all inherited metadata and search records. The source archive's Proof sentence uses exact extension by zero to preserve K-injectivity and then computes the open derived image; the current main-20261015 ancestor retains the statement but has no proof paragraph. The seven steps make the coefficient identification and unit implicit in that computation explicit, without changing the unit or chapter route. This item is not the unit's key statement, so no unit record was changed.

The important distinction is coefficient commutativity. Both `lem-weil-proetale-weakly-etale-localization` and `lem-sfb-proetale-object-inverse-image-restriction` introduce a commutative auxiliary ring. I use them with Z only for their site and underlying inverse-image clauses. I do not specialize their commutative module clauses to the given A. Instead the ring-valued slice-sheafification leaf and the arbitrary-ring constant coefficient structure map identify A_T restricted to U with A_U. The RingCat interface of `lem-pur-kinjective-restrict-localized` and the explicitly noncommutative `lem-weil-pbc-ring-sheaves-grothendieck` then supply the needed module results. No constructibility, Noetherianity, boundedness, finite-Tor condition, or injectivity of each term of I is required.

## New nodes

None. The DAG already contains all the needed general results. In particular I reused the localized K-injective lemma instead of inventing another preservation clause, and computed the unit via the Hom bijection instead of moving the item's conclusion into a new lemma.

## Not duplicates

No new nodes. Whole-DAG searches by title and statement found the slice-localization, inverse-image, sheafification, arbitrary-ring Grothendieck, K-injective, and derived-adjunction nodes used here. Whole-blueprint searches with `tools/blueprint_refs.py search` for K-injective, restriction, localized restriction, and derived adjunction found no imported node stating this entire conjunction with its specified coefficient action and unit. `same_as` remains empty. The item's nearest imported ancestor is `lem-exc-proetale-support-triangle`.

## Mathlib searches

The exact commands and returned hits are recorded in `searches.jsonl` and appended to the item's `mathlib_searches`, preserving the inherited searches. Two LeanFinder phrasings, LeanSearch, Loogle for `"IsKInjective"`, and Mathlib grep were run with the required `msearch.py` command. All services answered successfully. The first semantic search and LeanSearch returned `Scheme.Modules.restrictFunctor`, `restrictFunctorIsoPullback`, `restrictAdjunction`, and its unit formula; I read the scheme-module source, which uses the Zariski structure sheaf, not the pro-etale finite coefficient ring sheaf. Loogle returned the generic K-injective definition, invariance, and bounded-below results. The second semantic search and grep found `CategoryTheory.Adjunction.derivedη_fac_app`; I read `Mathlib/CategoryTheory/Functor/Derived/Adjunction.lean`, especially lines 35-56 and 91-108. It is generic derived-adjunction infrastructure with localization and derived-functor hypotheses, not a one-line statement of this item's geometric and coefficient identifications. The proof uses existing DAG interfaces for K-injective localization and gives the explicit Hom computation, so no new Mathlib leaf is needed.

## Review by Q38

I read the chapter and `sk-prop-sf-localization` unit, the item's JSON, the archived ancestor Proof, and the main-20261015 ancestor. For the mathematical tools I opened Stacks `sites.tex` Section 00XZ and Tag 03CE (`lemma-localize-given-products`), `sites-modules.tex` Definition 04IX and Lemmas 03DI/03DJ, `sites-cohomology.tex` Section 08FH and Lemma 08FI (`lemma-restrict-K-injective-to-open`), and `derived.tex` Lemmas 070I, 070Y, 070K, and 09T5. I checked the 08BJ right-adjoint result against the existing node and its closed project interface. I also read the arbitrary-RingCat Grothendieck theorem and the closed general Grothendieck K-injective resolution instance in the supplied source. These support this split without a purity or trace argument.

Step 1 cites the geometric localization node for equivalence of sites and matching coverings, and the pro-etale object inverse-image node for its actual initial indexing pair and natural inverse-image identification. I read both statements, including their commutative-ring hypotheses: choosing Z satisfies those hypotheses while extracting only coefficient-independent assertions. The pair is initial in I_W and therefore terminal in I_W opposite, which is the orientation required for evaluating the colimit. Skeleton and universe conventions are those in the item, not a colimit over a large unbounded category.

Step 2 cites the actual definition of A_S as sheafification of continuous functions on the component quotient. The slice-sheafification statement explicitly allows rings and preserves the sheafification unit; it does not assume commutativity in its ring-valued case. The presheaves on the slice are literally the same, with the same multiplication. The canonical coefficient ring-map node explicitly permits noncommutative finite rings and describes constants and gluing over open fibres. Its map therefore agrees with the slice comparison, and the transported-action node defines exactly the action used in this item. These are a few substitutions of the cited formulas, so this step is elementary relative to its cited statements. It is not an appeal to exactness alone to identify an adjunction unit.

Step 3 reads the direct-image and colimit formulas from the inverse-image definition and uses the monomorphism clause of the geometric localization statement. The two written transpose formulas are mutually inverse by naturality at V times_T U to V and W times_T U = W over U. Their linearity follows from the restriction homomorphism on coefficients identified in step 2. The unit is the transpose of the identity and is also explicitly checked against the colimit coprojection of the originally specified adjunction. Thus this is a computation of the specified unit, not a choice of an unrelated adjunction. It uses the statement of the initial-pair node, not an unexported construction from its proof.

Step 4 invokes the full statement of the localized K-injective result with R = A_T. Its recorded signature uses RingCat and its statement has no commutativity restriction. The explicit zero-map parameter is supplied sectionwise. The only equivalences involved are the already specified identifications of sites and coefficient actions: they carry complexes, chain maps, and null homotopies to the same component formulas. Exactness of j^* comes from the arbitrary-ring exactness node, and the exact-functor derived leaf states the termwise triangulated descent used here.

Step 5 uses the arbitrary-ring module-sheaf Grothendieck node and the general Grothendieck K-injective resolution node. Both say what is needed for every integer-indexed complex, not just bounded-below complexes. The total-derived node gives existence and the comparison isomorphism on every K-injective. Its exact-functor hypothesis is verified by writing the shift and cone matrix for the additive termwise direct image; the derived-category definition explicitly supplies the cone triangles. This does not assume that j_* is exact on sheaves. Taking J = j^*I is valid by step 4.

Step 6 uses the closed right-adjoint preservation statement with right adjoint j_* and exact left adjoint j^*. It therefore has K-injective targets on both sides of the sheaf adjunction. The Hom-derived lemma supplies both outer bijections for arbitrary source M. The middle bijection is the already written sheaf transpose in each degree; the text checks the differential and homotopy equations, so it genuinely descends to homotopy classes. K-injective resolutions from step 5 let this natural calculation describe the adjunction on all derived objects. No chain map into a non-K-injective target is incorrectly identified with an arbitrary derived morphism.

Step 7 substitutes J = j^*I in that bijection. The identity transposes to the sheaf unit, and composition with the right-derived comparison beta gives beta composed with Q(eta_I). Identifying the target by that very comparison yields Q(eta_I), exactly as the item asks. No further theorem or comparison is hidden in this final elementary substitution.

I tested the statement on U = T, where every restriction, representation and unit is the identity, and U empty, where the restricted module category is zero, j^*I and j_*j^*I are zero, and the unit is I to zero. The zero ring gives zero module categories. For a genuinely noncommutative finite ring such as M_2(F_2), every formula uses left actions and ring homomorphisms only, without exchanging scalar factors or invoking a symmetric module tensor product. The proof works for an unbounded I without termwise injectivity. The naturality and unit checks work on disconnected objects as well: constants are glued over their open fibres. All newly written statements are the original item; there are no new nodes to test.

I checked delivery-errors B-E against these files: the statement is self-contained with its existing definition dependencies, every non-elementary fact has a node citation, every cited statement was opened and says the part used, no clause was repackaged as a new node, and there are no new statement-only nodes or duplicate tags to justify. All proof steps are below 2000 characters. The generic off-unit site/coefficient/derived tools are declared in `split_report.tool_uses`; they serve this unit's open K-injective computation rather than substitute a different route. The main correction made during preparation was to avoid applying commutative coefficient clauses to A and to include the exact sheaf and derived-unit identifications. No statement dispute was found.

## Unfinished work

None in this one-level split. The existing dependencies retain their own stage states; no Lean work or compilation was performed. Required server dry-run validation and direct push are recorded below after completion.

## Validation

The server `review_split` returned PASS with zero new nodes. The required `deliver.py Q38 lem-exc-proetale-open-derived-image --no-push` completed with exit 0 and `OK (not pushed)` at b50d905309, reporting that preflight passed. This includes the server DAG and split checks. The report's validation record is included in the final packaging check and push; the mathematical node and citations were unchanged after this successful dry run.
