# sk-d-local-term — Q09 stage-1 report

## Files written

- `dag/nodes/sec-trace-formula/sk-d-local-term.json`: definition, split using existing nodes only; no Mathlib match.
- `dag/units/sk-d-local-term.json`: only `realized` and `realized_by`; its unchanged statement is realized by the existing `def-trf-local-term-pair` together with the proper-ambient recipe `sk-d-local-term`; it has no proof steps.
- `citations.json`: `[]`. This item is a definition, so its `proof` and `proof_deps` are empty and there are no numbered proof-step citations. Its construction dependencies are all in `stmt_deps`.
- `searches.jsonl`: the five actual msearch records, preserved exactly as generated. Their queries, hits and verdicts are recorded in the item.
- `report.md`: this report.

New nodes: 0. Mathlib leaves: 0.

## Attachments

None. I searched the project Lean for the blueprint tag and localTerm/local_term/clopenIdempotent concepts, and read `WeilConjectures/SixFunctors/ProEtale/TraceFormula/Pairing.lean` lines 380–445, its introduction, and `Derived/ClopenIdempotent.lean`. `AlgebraicGeometry.ProEtale.GeometricOperations.localTerm` at Pairing.lean:409 is a concrete definition of the cut integral, but does not give every clause of the item: the displayed equality with the integral on B is in its docstring, not a theorem there; the traceClass docstring explicitly says the supported-pairing comparison is not formalized. The generic idempotent definition also does not prove the entire local-term item. I therefore do not claim an attachment from a docstring or from a partial declaration. No Lean was written or compiled. The upstream master source is not treated as evidence of a finished proof.

## WANTED

None. No external document had to be fetched.

## What needed correction or clarification

The imported node has the current main-20261015 definition, but its unit record retains the older master statement. The current node assumes proper ambient E and defines the scalar through an idempotent on E; the older unit permits arbitrary E and integrates on proper B. Neither statement is false. I preserved the current node's properness hypothesis and every one of its clauses, and preserved the unit text. The existing, reviewed `def-trf-local-term-pair` already states the more general unit construction, so I recorded it in the unit realization rather than weakening it to the narrower current node or writing a new copy.

The item did not explicitly name the finite-coefficient context, the canonical middle comparison, the open adjunction, or the notions behind restriction. These are now named as existing construction dependencies. I wrote `\int_E(\alpha\circ e_B)` with parentheses so the scalar integral is applied to a morphism of the right type. No target statement was changed. There is no statement dispute and no change of coefficient category: A remains the finite ring of sk-d-setup on the ordinary pro-etale category, with exceptional adjunctions on the full constructible finite-Tor subcategories.

The initial dependency list contained the five high-level sketch notions and the diagonal-pairing lemma; those are still needed. The split additionally names the operations, immersions, exact extension by zero, properness, restricted sections, and the existing integration results used to interpret its comparison formula. No claim is delegated to a new restatement of the item.

## Construction and comparison check

This is a definition rather than a theorem proof; the following are the checks of its data and of the comparison assertions retained from its source.

1. **Clopen geometry and the composite.** From the definition of an open immersion, j_B identifies B with the open subscheme on its image. If that image is also closed, the structure-sheaf map from E to the pushforward of its restriction is an isomorphism at every point of B and has zero target off B; hence it is surjective, so j_B is a closed immersion by `def-weil-closed-immersion`. `lem-weil-pbc-closed-immersion-proper` (a), (b), (c) gives properness of j_B and of B over s. The same argument applies to V=E\B. This is precisely the hypotheses of the proper comparison in `prop-functor-package` (3). The two adjunctions are those stated in `def-weil-pbc-proetale-operations` and `prop-weil-open-closed-recollement-adjunctions`; the termwise counit is specified in `def-weil-open-closed-recollement`. `def-weil-extension-by-zero` and `lem-weil-extension-by-zero-exact` justify using j_! termwise. Thus the three arrows defining e_B have the displayed domains, with no hypothetical unbounded exceptional adjoint.

2. **Idempotence, written out.** Put P=j_B^*, J=Rj_{B*}=j_{B!}. Let s_L:L→JPL be the ordinary unit and r_L:JPL→L the open counit. The adjunctions are P⊣J⊣P. The ordinary counit a:PJ→id and the open unit b:id→PJ are inverse under the canonical clopen comparison: on a sheaf on B, both are the identity restriction map, and these identities hold degreewise and descend. The ordinary triangle gives P(s_L)=a_{PL}^{-1}, and the open triangle gives P(r_L)=b_{PL}^{-1}=a_{PL}. Under the ordinary adjunction, the adjunct of s_L r_L is a_{PL} P(s_L) P(r_L)=a_{PL}, also the adjunct of id_{JPL}; injectivity of the hom bijection gives s_L r_L=1. Therefore (r_L s_L)^2=r_L(s_L r_L)s_L=r_L s_L. Evaluating at A_E proves the claimed e_B^2=e_B. This uses the actual adjunction statements, not a claim extracted from their proofs. It is elementary category algebra; it is not a new node.

3. **Restriction and equality of scalars.** The previous triangle calculation gives P(e_B)=1. On V, restriction of J=j_{B!} is zero. This follows directly by restricting the extension-by-zero construction to the disjoint open, or from proper base change in `prop-functor-package` (4) for j_B and V→E: their fiber product is empty, and direct image of the zero object is zero. Hence the section αe_B restricts to α|_B on B and to zero on V. The notation α|_B is exactly the display in `def-trf-local-term`, including constant pullback, open purity and the dualizing-composition comparison; the same display appears in `lem-trf-integration-component-sum`. Both B and V are proper by point 1, E is separated finite type because it is proper, and the coefficient ring is the finite A required there. Apply that lemma to the two-piece decomposition E=B⊔V, including empty pieces if necessary. It gives ∫_E(αe_B)=∫_B α|_B+∫_V 0. The statement of `lem-trf-integration-linear` makes the last term zero (its additivity gives I(0)=I(0)+I(0)). This proves the comparison without using a mere definition node as a theorem and without deducing equality of arbitrary derived morphisms merely from their restrictions. The equality being used here is a scalar equality supplied by the component-sum lemma.

4. **Pairing and endocorrespondences.** `sk-d-corr` defines E(C,D) with the opposite support-map convention; `sk-d-pairing` supplies a section with precisely domain A_E and target ω_E. `sk-d-trace-class` supplies the diagonal trace class directly on F=Fix(c). The actual statement of `lem-trf-trace-class-diagonal-pairing` gives ⟨u,1_K⟩=Tr_c(u) in Hom(A_F,ω_F), with no sign or twist, on its specified constructible admissible domains. Applying the same e_B and integration to this equality is elementary and proves LT_B(u)=LT_B(u,1_K). `def-trf-local-term-pair` supplies the same restricted-integral notation for general pairs and explicitly includes the diagonal specialization. The reduced clopen point notation is supplied by the Point components paragraph of `def-trf-local-term`. No isolated fixed point is assumed automatically reduced, and no local term is identified with a stalk trace for a general correspondence.

## Not duplicates

No new nodes were created. Searches of the whole DAG and `tools/blueprint_refs.py search` for “local term”, “clopen idempotent”, “integration”, and “recollement”, plus the project Lean concept/tag search, found all interfaces reused above. I also searched ancestor sk-d-local-term. The item has `blueprint.is=sk-d-local-term`, so its `from` remains null rather than inventing a new ancestry.

`def-trf-local-term` and `def-trf-local-term-pair` are related, but do not state this whole idempotent recipe on proper E: they define local terms by integration on proper B and do not require E proper. `lem-trf-integration-component-sum` is a more general finite-partition integration theorem, used as such. It is not copied into a new two-piece leaf. There is no other imported blueprint node stating the entire recipe, so `blueprint.same_as=[]`. The notions are reused by references instead of adding an idempotent-comparison or proper-component helper. I checked that none of the added dependencies reaches sk-d-local-term, so the added edges do not create a cycle.

## Mathlib search reading

All searches were run through msearch.py for Q09/sk-d-local-term; no direct Mathlib grep was represented as a logged search. The declaration-name search `"localTerm"` and the AlgebraicGeometry source grep returned zero hits. The first semantic phrasing returned ordinary structure-sheaf local sections and quasi-separatedness lemmas. The second returned generic truncation, fraction and projective-object results in the derived category. LeanSearch returned clopen characteristic functions, integral-closure trace, a stalk map, a parser, and a Hom-complex cohomology class. I read their returned types: none defines a dualizing-complex integral or local term. The second phrasing was run before concluding absence. Every query and actual hit list is preserved, with no unavailable service misclassified as a no-match. These results do not turn the item into a Mathlib leaf.

## Review by Q09

I read the main-20261015 sk-d-local-term `_section.md` (order 2679), the master `_section.md` (order 2335), the complete recorded chapter and unit, and the stage-1 and delivery-errors B–E rules. I compared the main `def-trf-local-term`, `def-trf-local-term-pair`, `lem-trf-integration-component-sum`, and `lem-trf-integration-linear` texts with their current DAG statements. I read every statement named in the item's final stmt_deps, including the current actual admissibility and integration definitions. For the properness fact I also read Stacks `morphisms.tex`, labels `lemma-closed-immersion-proper` (Tag 01W5) and `lemma-composition-proper` (Tag 01W3). The existing node includes both exactly. No new node needs an additional source or a statement-only audit, and no SGA source is cited.

For the first construction check I verified closedness, finite type, separatedness and properness before invoking proper coincidence; exactness of the open functor is cited, and the ordinary and open adjunctions are distinct and correctly oriented. For the second I checked that the units/counits really are canonical clopen restrictions, then recomputed the adjunct of s r and the idempotent product rather than assuming an arbitrary ambidextrous adjunction gives a projection. For the third I compared the full restricted-section formulas in both cited statements, checked that the component theorem permits an arbitrary finite clopen partition (not only connected components), and checked properness of each of the two pieces. I used linearity for the zero summand; the component theorem is never cited as though its statement asserted equality of global derived morphisms. For the final comparison I checked the legs of the opposite pair and the diagonal support, the D^b_ctf/finite A domains and the exact diagonal-pairing equality. The fixed-point clause is notation for a reduced clopen component, not a theorem claiming all general fixed points have that form.

I tested B=∅ (e=0, scalar 0), B=E (e=1, scalar ∫_E α), E=∅, and E a disjoint union of two k-points with α=(a,b) (e_B projects to the first coordinate and LT_B=a). These tests also check the orientation of e_B. A nonreduced single point is allowed for the general construction; the special Frobenius notation alone specifies a reduced component. Taking α=0 gives zero for any piece. The coefficient n=1 case changes no construction. The source's formulas survive these cases. The older unit's example E=A^1⊔Spec k, B=Spec k remains covered by its existing general definition and is not silently excluded from its realization.

The corrections made on this reading were to expose the missing construction dependencies, cite exactness and linearity explicitly, parenthesize the cut integral, and distinguish the current proper-ambient node from the older more general unit. There is no relabelled new lemma, hidden source proof used as a statement, false edge-case claim, or fabricated search. This definition has no proof steps to number; `citations.json` is intentionally empty. The four detailed construction checks above explain the elementary checks and every non-elementary statement used by the definition.

## Unfinished work

None in the one-level split. This is a stage-1 handoff only. A second reader is to review and deliver it; I do not push.

## Second reading by Q09

This is the ordinary stage-1 reading. The recovery condition is false: the
stage-1 item JSON exists and the specified Q09 stage-2 packet does not exist.
I independently read the current item, all 24 direct dependency statements,
the main-20261015 source (order 2679), the master unit source (order 2335),
the chapter record and main chapter text, and delivery-errors B–E.
The item is a definition with no numbered proof steps and no new nodes;
the four construction checks in the worker report are audited below.

- Construction check 1: checked `def-weil-open-immersion`,
  `def-weil-closed-immersion`, and `lem-weil-pbc-closed-immersion-proper`
  against Stacks `morphisms.tex`, `lemma-closed-immersion-proper` (01W5)
  and `lemma-composition-proper` (01W3). The closedness hypothesis is present,
  so both pieces and the immersion are proper. Ordinary pullback/right
  direct-image adjunction and open extension-by-zero/ordinary-pullback
  adjunction have the orientations stated in their cited nodes. PASS.
- Construction check 2: checked the actual units and counits, rather than
  treating arbitrary ambidextrous adjunctions as compatible. Here is an
  explicit check of the canonical identification used in the worker's
  calculation. For any pro-etale object W over E, its inverse images W_B
  and W_V form a disjoint clopen cover. The definition of extension by zero
  restricts to M on W_B and to zero on W_V. Sheaf gluing therefore gives
  (j_!M)(W)=M(W_B), since sections on the empty intersection form the zero
  module. The direct-image formula in `def-weil-pbc-proetale-operations`
  gives (j_*M)(W)=M(W_B) as well. The canonical comparison is the identity
  on these sections. Restricting either adjunction to B gives the identity
  map, while restricting the extension to V gives zero. These descriptions
  commute with restrictions and morphisms of M, hold termwise on complexes,
  and descend to the derived functors: j_* is identified with the exact
  j_!, and the ordinary pullback is exact. Thus the worker's identification
  a=b^{-1} is justified for the canonical comparison. Its subsequent
  adjunct computation s r=1 and e squared=e is correct. PASS.
- Construction check 3: checked the full statement (not the proof) of
  `lem-trf-integration-component-sum` and the source file of the same name,
  including its arbitrary finite clopen partition and empty-support case.
  Its restriction is the same constant-pullback/open-purity/dualizing-
  composition composite as in `def-trf-local-term`. On B the cut section is
  alpha restricted to B; on V it is zero by the preceding sectionwise
  calculation. Both pieces are proper, so the two-term integral identity
  applies. `lem-trf-integration-linear` gives integral(0)=0 by cancellation.
  This proves a scalar equality and does not assume restriction detects
  arbitrary morphisms in an ambient derived category. PASS.
- Construction check 4: checked the opposite support convention and domain
  of `sk-d-corr`, the bounded constructible finite-Tor inputs of
  `sk-d-pairing`, and the precise Hom-set equality in
  `lem-trf-trace-class-diagonal-pairing`. The latter's admissible diagonal
  pair is exactly the pair used here. Applying the same projector and
  integral preserves that equality. The point notation requires a reduced
  clopen component; it does not assert a stalk-trace formula for a general
  correspondence. PASS.
- New nodes: none; B1–B7 and the per-new-node duplicate checks are vacuous.
  I independently searched the DAG for local terms, clopen projectors and
  integration components. The existing local-term definitions are more
  general in ambient properness, but do not state the whole projector
  recipe. No new copy of a clause or elementary comparison is needed. PASS.
- Unit realization: compared the unchanged master unit text to
  `def-trf-local-term-pair` and its source. That definition covers arbitrary
  ambient E with proper B, so the unit is not accidentally restricted to
  the proper-ambient main snapshot. The unit has no proof steps. PASS.
- Attachment: independently read Pairing.lean:409–414 and its implementation
  notes at lines 46–75, and Derived/ClopenIdempotent.lean:47–86. The concrete
  localTerm is the cut integral, but the comparison with integration over B
  is explicitly not formalized in those notes; the diagonal comparison is
  also not formalized there. A docstring is not a finished proof of these
  clauses. No unsupported closed attachment is claimed. PASS.
- Edge cases: empty E, B empty, B=E, alpha=0, and two k-points with
  alpha=(a,b) give respectively zero, zero, the full integral, zero and
  the selected coordinate. A nonreduced point is permitted for the general
  construction, but is not the special reduced-point notation. The smallest
  allowed coefficient exponent n=1 causes no change; n=0 is outside the
  fixed coefficient convention. PASS.
- Searches: independently ran msearch LeanFinder with the new phrase
  "Compactly supported trace of a dualizing sheaf morphism restricted to an
  open closed component of a scheme", and a whole-Mathlib grep for
  `dualizing|Verdier|local.?term|clopen.?idempotent`. Read all returned hits:
  ordinary structure-sheaf restrictions and general Verdier references do
  not supply this definition. Recorded the real capped results without
  interpreting the grep cap as an exhaustive absence proof. PASS.
- Citations: `proof=[]`, so `citations.json=[]` is correct. All 24 direct
  dependencies exist. A read-only traversal of the available dependency
  graph found no path from any of them back to this item; the required
  authoritative DAG/preflight checks remain the delivery tool's task.

Changes: added the explicit canonical-comparison check above and the two
independent Mathlib search records. No mathematical statement, dependency,
unit text, or first-worker review was changed. The main definition and the
older unit are both faithful to their respective sources, so no statement
dispute is raised. Preserved backups before updating the packet. No Lean
was written or compiled and no live project or launcher file was modified.
