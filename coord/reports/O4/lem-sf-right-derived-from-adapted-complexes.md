# Worker report: lem-sf-right-derived-from-adapted-complexes

## Files written

- `dag/nodes/sec-six-functors/lem-sf-right-derived-from-adapted-complexes.json`: statement; split into eight steps using five existing Mathlib leaves. The statement and its statement dependencies are unchanged.
- `citations.json`: nine step/node citations, each with a verbatim excerpt from the cited node's statement.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. The local helper `prepare_split.py` and search log are sandbox research records, not node deliveries.

## Attachments

None. I searched the read-only slopmaster2 project under `WeilConjectures/` for the exact blueprint tag, adapted-complex terminology and right-derived constructions. The existing right-derived APIs concern an additive functor on abelian categories, bounded-below resolutions, K-injective hypotheses, or the derived functor of an exact underived functor. None states this criterion for an arbitrary exact functor on the homotopy category and an arbitrary adapted class. The node's slopmaster2 audit is `none`; master is reference material only.

## Wanted literature

None. I read the local Stacks sources, not an unavailable reference.

## Corrections and route

The imported statement is correct and is kept in full. There is no statement dispute. The empty proof needed the argument behind Stacks 06XN's cofinality/essential-constancy assertion and 05SA's omitted functoriality details. I supplied it by computing fractions with adapted targets, proving independence and composition, then descending the replacement functor. This is an agent expansion of the cited source, recorded as `proof_origin.by = agent`.

The first preflight returned one self-contained-wording violation in Step 2: “the item’s hypothesis”. I replaced that phrase with the explicit assumption that G inverts quasi-isomorphisms with both endpoints in the adapted class. This was a prose repair; the formula and statement are unchanged.

The source-place wording now distinguishes 05S9's definition of a derived value from the universal comparison property proved here. In particular I did not treat that definition as a theorem asserting a Kan extension. The universal property is established by the formulas in Steps 7–8.

I read the chapter and the four steps of `sk-prop-sf-rf-shriek-preservation`, and paragraph 3 of the blueprint ancestor `lem-sf-projection-finite-constant`. This item serves the existing finite-cohomological-dimension argument through `lem-sf-finite-cd-derived-upper-bound`, Step 5. The construction stays below that unit route. Every external dependency reused here is already a Mathlib leaf; no off-route unproved tool is introduced and no unit binding is changed.

## Not duplicates

No new nodes. Whole-DAG and blueprint searches found the existing calculus, fraction representation/equality and localization universal-property nodes, which are cited. The existing `new-everywhere-defined-derived-functors` has a terse general prose statement, but its recorded Lean interface is for functors induced termwise from additive functors on abelian categories. That interface does not cover this item's arbitrary functor G, so I did not use its proof as though its statement supplied the needed general theorem. `lem-sc-nattrans-from-resolving-class` concerns the opposite resolution direction and extension into a nonlocalized functor, so it is not an exact attachment either.

## Mathlib research

I ran the required msearch.py commands for this item: LeanSearch, Loogle, two distinct LeanFinder formulations, and two grep queries. The exact queries and actual hit summaries are appended in `mathlib_searches` and logged in `searches.jsonl`. All services answered. I read the candidates in `Functor/Derived/RightDerived.lean`, `Localization/DerivabilityStructure/Basic.lean` and `Constructor.lean`. TotalRightDerived and the Kan-extension bridge assume existence; the derivability-structure constructor requires connected resolution categories, arrow resolutions and a localized equivalence. Those are not one-line instances of the two adapted-class hypotheses. I therefore retained `mathlib_match = null` and supplied the fraction argument. The second grep targets a single file; its wrapper reports line numbers as file entries, which is how it appears in the actual output. I read the actual file to assess the result.

For the reused leaves I also read `CalculusOfFractions.lean:743–765`, `Predicate.lean:278–332`, and `DerivedCategory/Fractions.lean:34–38`, and checked their statements against the DAG statements. No new search result or match was invented.

## Unfinished work

None in this one-level split. No Lean was written and no compiler, Lake or build tool was run. Delivery is reserved for the fresh second reader; this worker runs only the required no-push preflight.

## Review by N4

I read Stacks `derived.tex`, Tag 06XN (`lemma-find-existence-computes`) in full, together with Situation 05S8, Definition 05S9, Lemma 05SA and `equation-everywhere`. In `categories.tex` I read Tag 04VC (`definition-multiplicative-system`), the left-fraction construction, Tags 04VE/04VF (`lemma-morphisms-left-localization`, `lemma-equality-morphisms-left-localization`) and 04VG (`lemma-properties-left-localization`). There are no new nodes requiring a separate source review. The item follows the adapted-replacement computation of 06XN; its explicit fraction and comparison calculations supply the details the source abbreviates.

Step 1 uses `lem-pc-quasi-isomorphisms-multiplicative-system` for the left calculus itself, including the Ore axiom. Its statement really supplies both calculi for K(A); I do not obtain them just from the definition of localization. `def-weil-abstract-derived-category` states the cohomological criterion for a quasi-isomorphism, so two out of three is proved by applying each cohomology functor and cancelling isomorphisms. The required replacements are exactly the item's first hypothesis. No injective, boundedness or Grothendieck assumption is added.

Step 2 uses `lem-pc-left-localization-fraction-representation`. I checked its orientation: an arrow QI to QJ has numerator I to Z and denominator J to Z. The chosen replacement of Z makes the denominator an arrow between two adapted objects, precisely where the second hypothesis allows G(b) to be inverted. I never invert G of an arbitrary quasi-isomorphism.

Step 3 uses `lem-pc-left-localization-fraction-equality`. Its statement supplies a common target with equality of both numerators and denominators, and the common denominator in S. The refinement maps themselves become quasi-isomorphisms by two out of three. After resolving the common target, their endpoints are adapted, making their G-images invertible. The displayed cancellation proves independence, including independence from the chosen adapted target. The identity fraction recovers G on actual arrows of the adapted class.

Step 4 again uses the calculus node's Ore axiom. I checked the objects and direction in the square: b:J to P is the quasi-isomorphism; c:J to R is arbitrary; t:R to V is the new quasi-isomorphism. After replacement t' still has adapted endpoints. The explicit equality e'b=t'c proves the displayed composition identity. A potential mistake would have been to invert G(e'); e' need not be a quasi-isomorphism. The proof uses only G(t') and G(b) inverses and explicitly records this distinction.

Step 5 constructs H with the already proved fraction maps. Identities, composition and preservation of S follow from Step 4, so there is no hidden localization-equivalence theorem. Its citation of the calculus node supplies the square needed for naturality of alpha-zero. The equality ar_K=br_Lf proves that square after applying G and cancelling G(b). I separately checked H(r_K)=G(r_{I_K}); this is the identity required for uniqueness, and it does not require G(r_K) to be invertible for a nonadapted K.

Step 6 uses clause (1) of `lem-weil-pbc-localization-universal-property`, whose statement supplies both the descended functor and the natural factorization isomorphism phi for any chosen localization. Since H has already been shown to invert all S, its hypothesis holds. Computation for every adapted I follows because r_I has adapted endpoints. No claim about exactness or invertibility of G on all complexes is smuggled into this application; G's given exactness hypothesis is retained, and the asserted categorical universal property is proved using its underlying functor.

Step 7 uses clause (2) of the same localization node, and I read its full statement rather than just its title. Both source functors of the comparison, H and TQ, invert S, and their liftings are RG with phi and T with the identity. I verified the component formula v_K=T(Qr_K)^{-1} beta_{I_K}, the naturality calculation with both a and b, and v_K alpha-zero_K=beta_K. The descended u thus has the exact direction RG to T and satisfies beta=(u Q) alpha, even for an arbitrary T.

Step 8 uses clause (3) of the localization node for equality after restricting along Q. Before invoking it, naturality at r_K forces every competing component w_K to equal v_K, using H(r_K)=alpha-zero_{I_K}. This proves uniqueness without cancelling alpha-zero_K, which is not generally invertible. All nine node citations have a verbatim supporting statement in citations.json.

For delivery-errors B, the only delivered node already existed; its statement remains self-contained, its TeX is single-escaped, its blueprint ancestry is preserved and same_as is filled. No statement-only subnode contains a hidden proof because none is created. For C, every mathematical input beyond the explicit fraction calculations is one of the cited leaves, each read above; no cited proof is substituted for its statement. For D, all construction, independence, composition and universality arguments stay in the item's steps, rather than moving one clause into a new node. For E, I checked each use of the adapted-endpoint hypothesis and tested the formulas with the identity replacement, I equal to all complexes and G already inverting S, I consisting of K-injective resolutions when available, and the zero abelian category. The identity case gives alpha-zero equal to the identity and the ordinary localization; the zero case has only identity computations. There are no degree restrictions, infinite colimit assumptions, closure assumptions on I, or functorial-resolution assumptions. Existing statement and source hypotheses suffice in all cases.

## Dry run

The final sandbox is checked with `python3 /home/ubuntu/weil-launcher-nt/deliver.py N4 lem-sf-right-derived-from-adapted-complexes --no-push`. Its actual output is saved in `preflight.log`. This handover is ready only when that command prints OK. Nothing is pushed by this worker.

## Second reading by N4

I am the independent second reader. I read delivery-errors B–E, GOAL.md and coord/dag-sync.md, the node and all nine quoted citations, the unit/chapter records, and the blueprint ancestor's third proof paragraph. No shared project, source checkout or launcher file was changed; no Lean, Lake or compiler command was run.

- Item statement: checked against derived.tex 06XN (`lemma-find-existence-computes`), Situation 05S8 (`situation-derived-functor`), 05S9 (`definition-right-derived-functor-defined`), 05SA (`lemma-derived-functor`) and `equation-everywhere`; PASS. The two adapted-class hypotheses have exactly the right direction and endpoints. The explicit universal property is established below rather than attributed to 05S9. No statement dispute or statement change.
- Step 1: checked the actual statements of `lem-pc-quasi-isomorphisms-multiplicative-system` and `def-weil-abstract-derived-category` against 05RT and categories.tex 04VC LMS2; PASS. The Ore square has its new denominator on the correct leg; degreewise cancellation gives two out of three, and replacements are chosen without functoriality.
- Step 2: checked `lem-pc-left-localization-fraction-representation` and `Localization.exists_leftFraction` (CalculusOfFractions.lean:743) against 04VE; PASS. Postcomposition by the replacement preserves the localized arrow and produces a denominator with both endpoints adapted.
- Step 3: checked `lem-pc-left-localization-fraction-equality`, `LeftFractionRel` (:246) and `LeftFraction.map_eq_iff` (:757); PASS after source-location repair. The arbitrary-denominator common-refinement relation is in the left-calculus construction following 04VC, whereas 04VF explicitly treats equal denominators. Two out of three makes each refinement a quasi-isomorphism, so resolving its target licenses both cancellations of G-images.
- Step 4: checked the calculus node's actual Ore axiom against 04VC and the subsequent fraction-composition rule; PASS. The denominator is t'd, the equality e'b=t'c gives G(t')^{-1}G(e')=G(c)G(b)^{-1}, and no inverse of G(e') is required.
- Step 5: checked the calculus node's statement and 05SA against the displayed Ore square; PASS. The equation ar_K=br_Lf proves naturality after cancelling G(b). The identity H(r_K)=G(r_{I_K}) follows by cancelling Q(r_K) and using Step 3, with no inverse of G(r_K) required.
- Step 6: checked clause (1) of `lem-weil-pbc-localization-universal-property` against Predicate.lean `lift` (:304) and `fac` (:313), and 04VG(3); PASS. H inverts all quasi-isomorphisms by Step 5, and alpha_I is invertible because r_I has adapted endpoints.
- Step 7: checked clause (2) of that node against `liftNatTrans` (:326) and its component formula (:332); PASS. The maps beta_P and beta_{I_K} have the displayed types. Naturality at a,b and ar_K=br_Lf give v_LH(f)=T(Qf)v_K. The lifting formula is u_{QK}=v_K phi_K, so its direction is RG to T.
- Step 8: checked clause (3) against `natTrans_ext` (Predicate.lean:286); PASS. Naturality at r_K forces T(Qr_K)w_K=beta_{I_K}; this determines w_K without cancelling alpha_K. Equality on all QK then implies equality of transformations on the chosen localization.
- New nodes: none; PASS. There is no elementary helper, duplicate, clause-restatement or new Mathlib leaf to remove or restate. All five proof dependencies are existing Mathlib leaves; I read their statements and the fraction/calculus/localization declarations above. The definition dependencies introduce abelian categories, quasi-isomorphisms, exact functors and the homotopy-category triangulation.

Small cases: with I all complexes and G already inverting quasi-isomorphisms, choose identity replacements and obtain H=G and the localization comparison. With G the zero functor on complexes of vector spaces and I all complexes, the formulas give the zero functor in degrees 0 and 1 as well as every other degree. In the zero abelian category the same unique-map calculations apply. An empty adapted class cannot satisfy the replacement hypothesis, since the zero complex needs a replacement. No boundedness, closure of I under shifts/cones, or injective-resolution hypothesis is used.

I independently searched the whole DAG for 06XN/adapted-complex terminology and the read-only slopmaster2 source for right-derived constructions. `RightDerivedFunctor/Defs.lean:137–143` assumes K-injective resolutions, which the present arbitrary abelian category need not have. I ran two fresh msearch queries using different vocabulary: LeanFinder on localization of a full subcategory of fibrant replacement objects (8 hits), and grep on `hasRightDerivedFunctor_of|hasPointwiseRightDerivedFunctor_of|hasRightResolutions` (25 hits). Both services succeeded and their actual results are in searches.jsonl and the node. I read PointwiseRightDerived.lean:150–180 and DerivabilityStructure/Constructor.lean:10–52: the former needs inversion of every quasi-isomorphism, and the latter needs a localized equivalence, connected resolution categories and arrow resolutions. Neither gives this item by a one-line specialization. No attachment or new leaf is warranted.

Changes made and why:

- Corrected Step 3's source location to distinguish the general fraction-equivalence relation following 04VC from 04VF's equal-denominator lemma. The cited DAG statement and the mathematical argument were already correct.
- Added the two independent, actually run searches and their assessed results to mathlib_searches; preserved all first-worker searches and report sections.
- Added this independent review, including each proof step, the absence of new nodes, explicit small cases, and direct checks of the cited Mathlib interfaces.
- Rechecked all nine quotations verbatim against the current shared DAG and checked that each corresponds to the cited step. citations.json already passes these checks and is retained.
