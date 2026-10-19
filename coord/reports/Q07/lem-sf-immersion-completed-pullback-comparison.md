# Stage 1 report

## Files written

- `dag/nodes/sec-smooth-purity/lem-sf-immersion-completed-pullback-comparison.json`: item split into six proof steps; no new DAG nodes.
- `citations.json`: 17 verbatim statement citations for the six steps.
- `searches.jsonl`: the mandated Mathlib search log (four searches completed; one LeanFinder search was initially delayed but completed and is recorded).

## Attachments

No new Lean declaration attaches to this item. The source search found no declaration tagged `(blueprint: lem-sf-immersion-completed-pullback-comparison)` and no sorry-free declaration stating the item.

## WANTED

None. The Stacks and Bhatt–Scholze sources needed for the route are already present in `literature/`.

## What was checked and changed

The imported item statement was retained. I checked its coefficient category and hypotheses against the current main-20261015 parent proof: $u$ is a locally closed immersion, the coefficient map is the canonical inverse-image isomorphism, and the claim concerns the completed quotient tower and its actual completion unit. The split makes the completion-unit issue explicit instead of inferring it from a noncanonical object isomorphism.

The proof uses only existing DAG statements. Step 1 reads `lem-weil-pbc-profinite-coefficient-inverse-image`, which supplies the canonical finite coefficient projections and transitions, and `lem-weil-pbc-proetale-immersion-limit-preservation`, which supplies exactness and countable-product preservation for module inverse image along a locally closed immersion. It also uses the exact-functor derived statement. Step 2 reads the ringed-topos K-flat pullback and module tensor-comparison statements and `def-weil-pbc-completed-pullback`; their statements give the chain-level finite reductions and naturality in quotient maps that the step uses.

Step 3 is the unit check. I read `lem-weil-pbc-constant-completion-equivalence`, `lem-weil-pbc-ringed-koszul-completion-reflector`, `def-weil-derived-complete`, and `lem-weil-derived-limit-existence`. These statements say respectively that quotient-tower and Koszul completion agree with their units, that the reflector unit is an isomorphism exactly for locally complete objects, that derived completeness gives a derived-limit object but singles out no arbitrary map to a chosen model, and that derived limits are unique up to isomorphism. This proves invertibility of the specified source completion unit, rather than silently choosing a different cone map.

Step 4 reads the exact countable-product statement and the strict Roos derived-limit comparison. I checked the displayed Roos differential and verified that the product comparison intertwines the transition endomorphisms coordinatewise, so it yields an evaluation-compatible derived-limit isomorphism. Step 5 reads the completed-pullback definition and checks that the constant-tower map has the same coordinates; this establishes compatibility with the completion unit, every finite projection, and successive quotient transitions. Step 6 reads the integral-category definition, the pro-etale constructible-origin equivalence, and the finite-coefficient pullback preservation theorem; these supply constructibility and preservation of the common interval $[r,s]$ at every reduction.

I checked each cited node's statement directly and copied the used sentence/formula verbatim into `citations.json`. All proof dependencies are included in the item's `proof_deps`; no new node was needed because the DAG already contains the exact generic tools. Every prospective duplicate was searched before deciding not to create a node.

## Not duplicates

`lem-sf-immersion-completed-pullback-comparison` vs `lem-weil-pbc-proetale-immersion-limit-preservation`: the existing node proves exactness and limit preservation of the underived module inverse-image functor; this item additionally compares ordinary derived pullback with the strict quotient-tower completed pullback, proves the specified unit is invertible, and preserves integral constructibility.

`lem-sf-immersion-completed-pullback-comparison` vs `def-weil-pbc-completed-pullback`: the existing node defines completed pullback and its comparison map for arbitrary morphisms; this item proves that comparison is an isomorphism for derived-complete objects along a locally closed immersion and checks finite reductions and constructibility.

`lem-sf-immersion-completed-pullback-comparison` vs `lem-weil-pbc-pullback-preserves-bounded-constructible`: the existing node is only the finite-coefficient bounded-constructibility preservation result; this item includes the completed integral comparison and uses that result only for its final reduction-category clause.

## Review by Q07

I read the current item source in `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sf-localization/prop-sf-localization-all-stages.md`, including the returned Step 6 that this item realizes, and the parent DAG statement in `prop-sf-localization-all-stages.json`. I also read the full statements of all 12 proof dependencies listed in the item. For each of the six steps, the cited statements say exactly the fact used: coefficient projections and transitions (Step 1), exact inverse image and K-flat/tensor comparisons (Step 1–2), completion-unit and derived-limit uniqueness facts (Step 3), exact products and evaluation-compatible Roos models (Step 4), the strict completed-pullback unit construction (Step 5), and constructibility plus interval preservation at finite levels (Step 6). I verified that all hypotheses are present: the coefficient ring is $​\mathcal O_E$ with $A_n=\mathcal O_E/\varpi^n$, the ring map is an isomorphism for the immersion, $K$ is derived-complete, and the integral category supplies one uniform interval for all reductions. I checked the edge case of a zero complex (all maps and interval assertions are immediate) and the identity immersion (all comparison maps reduce to identities). I corrected the imported proof by separating object-level uniqueness of derived limits from invertibility of the actual completion unit, and by writing the coordinate calculation for the Roos transition map and successive quotient compatibility.

## What could not be finished

No Lean code or compiler was used, as required for stage 1. The item is otherwise complete pending the server delivery dry run.
