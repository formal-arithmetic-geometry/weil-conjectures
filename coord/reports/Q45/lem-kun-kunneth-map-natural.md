## Files written

- `dag/nodes/sec-smooth-purity/lem-kun-kunneth-map-natural.json`: item, statement, split into five proof steps; searched and not a Mathlib leaf.
- `citations.json`: thirteen verbatim statement excerpts, covering every `uses` entry of every step.
- `searches.jsonl`: searches actually run through the required msearch command.
- `report.md`: this report.

No new nodes and no new Mathlib leaves. The item reuses the existing monoidality lemma, the ringed-site tensor-descent theorem, the unbounded exchange definition's adjunction conventions, and the existing Mathlib adjunct-formula leaf. No other node or unit record was changed.

## Attachments

None. Searching `WeilConjectures/` and `Comparator/` for the item id and searching the Kunneth terminology found no declaration stating this naturality square. In `WeilConjectures/SixFunctors/Etale/Derived/Finiteness/Kunneth.lean:72`, `AlgebraicGeometry.Etale.nonempty_iso_kunneth` has a `sorry`, asserts existence of an isomorphism, and assumes finite coefficients over a separably closed field with invertible exponent. It neither states this canonical-map naturality nor covers this item's hypotheses. The externalProduct and HasKunnethComparisons definitions concern other interfaces and do not attach this item. The master checkout was not used as evidence of a completed proof.

## WANTED

None. The shared checkout lacks the untracked literature files, but the read-only archive at `/home/ubuntu/weil-launcher-nt/literature/` contains the master blueprint and Stacks sources; I read those copies without writing or fetching anything. No corresponding slopmaster2 markdown file was present at the parallel path.

## Corrections and source audit

STATEMENT-DISPUTED (unbound notation, repaired): the imported displayed square contains `Rc_*` without introducing the morphism `c`, and labels its vertical maps by unnamed `varphi, psi`. The type of the right-hand vertex requires a morphism from `X ×_S Y` to `S`. The immediately preceding source definition, `def-kun-kunneth-map`, explicitly specifies `c = f ∘ p = g ∘ q`. I added that binding, named the two given morphisms, and explicitly identified the existing derived tensor and Kunneth-map definitions. All hypotheses and every vertex and arrow of the original square are retained; this is a notation repair, not an added mathematical restriction.

The imported proof attributes the derived adjunction to `def-weil-pbc-inverse-image`. I opened its statement: it supplies the underived sheaf adjunction only, including the constant-coefficient module version. It cannot justify the unbounded derived adjunction by itself. Step 1 instead uses the already reviewed `def-kun-unbounded-exchange`, whose statement expressly supplies the canonical adjunction on unbounded module derived categories. Every morphism, including the composite `c`, is an edge of its identity base-change square, so its square hypothesis does not restrict this application. No bounded-below adjunction theorem is used.

I also opened `lem-weil-derived-tensor-functorial`: it is about pro-etale coefficients, so I did not use it for this etale statement. The existing `lem-weil-pbc-site-derived-tensor-descent` states bifunctoriality for arbitrary small ringed sites, and supplies precisely the missing morphism-level tensor fact. This is the single declared off-unit statement tool; the Kunneth unit has no separate etale tensor-bifunctoriality node. The use of this tool preserves the blueprint's comparison-counits-mate route.

## Mathlib and duplicate searches

All searches recorded in the item's `mathlib_searches` were actually made with `msearch.py`, with exactly the query text in `searches.jsonl`. LeanFinder was tried with both the scheme-theoretic external-product statement and a second cup-product/pushforward phrasing, and separately with the abstract adjunction argument. Loogle searched `"kunneth"` and the generic naturality declaration. Grep searched `kunneth|künneth|externalProduct` across Mathlib and `kunneth|künneth` in AlgebraicGeometry. LeanSearch returned Internal Server Error and is recorded as unavailable.

The generic candidate `CategoryTheory.Adjunction.homEquiv_naturality_left_square` is at `Mathlib/CategoryTheory/Adjunction/Basic.lean:249`; I read lines 226–275. It handles transposing an already commutative square. Applying it here first requires proving the square for the specific comparison-and-counits composite, which is steps 2–4; it does not make this item a one-line Mathlib specialization. I expanded the unit calculation instead, citing the existing adjunct-formula Mathlib leaf. The externalProduct hits were also inspected at `Mathlib/CategoryTheory/Monoidal/ExternalProduct/Basic.lean:32–82`: they tensor functors and do not define this etale derived Kunneth map.

I searched the whole blueprint via `tools/blueprint_refs.py search` for `Kunneth map`, `Kunneth`, `adjunction`, `naturality of adjunction`, and `tensor bifunctor`, and searched the whole DAG for the same concepts and generic hom-equivalence naturality names. The adjacent Kunneth nodes assert isomorphism or comparison with classical maps; none repeats this item's naturality statement. The six-functor coherence and ordinary Kunneth nodes concern other functors or more restrictive coefficient categories. Thus `blueprint.same_as` is empty. No new-node duplicate decision is needed.

## Unfinished work

No mathematical step is left open in the item's split. The dependencies retain their own independent stage-1/stage-3 work. This delivery does not assert that the entire dependency closure is proved in Lean. No Lean was written or compiled, no agents were started, and no delivery was pushed.

## Review by Q45

I read the master blueprint's complete `lem-kun-kunneth-map-natural.md`, the preceding `def-kun-kunneth-map.md`, the monoidality source `lem-kun-inverse-image-monoidal.md`, and the chapter/unit records. The unit's statement concerns ordinary unbounded etale Kunneth and has no numbered proof steps to replace. This item's proof stays on its own prescribed route: comparison, two counits, and a fixed adjunction. The statement repair above agrees with the preceding definition, including the order of the projections and the coefficient ring. No properness, finite type, torsion, invertible-order, or boundedness hypothesis has been introduced.

For the categorical argument I read Stacks `categories.tex`, Tag 0037 (`definition-adjoint`, line 3344 and the following paragraph), where the Hom bijections are natural in both variables and the unit/counit are transformations of functors. The same paragraph identifies the transpose as the unit followed by the right-adjoint map. For tensor I read `sites-cohomology.tex`, Tag 06YU (`definition-derived-tor`, line 3300 and its preceding construction), and Tag 07A4 (`lemma-pullback-tensor-product`, line 3684, including its proof). The latter explicitly says the comparison is bifunctorial. The blueprint is agent-written, and the expanded equations are therefore recorded with `proof_origin.by = agent`.

Step 1 uses the actual statements of four existing nodes. `def-weil-size-convention` permits small representatives in a larger universe; this checks the small-site hypothesis in `lem-weil-pbc-site-derived-tensor-descent`. On each etale site the ring is the constant commutative sheaf `Lambda_T`, so that theorem supplies an ordinary unbounded tensor bifunctor. `def-kun-unbounded-exchange` supplies the canonical unbounded module adjunctions, not a bounded-below or pro-etale replacement. Its identity-square specialization covers `f`, `g`, and `c`. `def-kun-kunneth-map` states exactly the transpose `a` decomposed here. In particular, the proof uses the definition's statement, not an object hidden in another proof. This step is non-elementary because it invokes tensor descent; the derived adjunction is the fixed data already provided by the cited definition.

Step 2 cites `lem-kun-inverse-image-monoidal` for its expressly stated bifunctorial isomorphism, and `def-kun-kunneth-map` for the chosen composition identifications. I checked the direction carefully: the comparison `m` goes from the tensor of pullbacks to pullback of tensor, whereas `chi` uses its inverse. The text introduces the separate morphism `J` before transporting to `H`, so the inversion equation has matching domains. Multiplying the naturality equation by inverses and composing with natural identifications is elementary; no extra monoidality or coherence lemma is being assumed.

Step 3 uses `def-kun-unbounded-exchange` only for its fixed adjunction data. Unit and counit are natural transformations by the definition of an adjunction. Both written counit equations have source `f^{-1}Rf_*E` or `g^{-1}Rg_*K` and the appropriate primed target. Applying the genuine functors `p^{-1}` and `q^{-1}` preserves composition. This is definitional naturality, not a new theorem about resolutions.

Step 4 cites the ringed-site tensor theorem for preservation of composition in the product category and the Kunneth-map definition for `a=d chi`. Tensoring the two equations from step 3 gives `d' H = B d`. Composing with the equation from step 2 gives `a' L(A) = B a`; the text writes every intermediate composite. This local inference is elementary once the explicitly cited bifunctor is available. No K-flat resolutions of individual morphisms have been chosen implicitly.

Step 5 cites the existing Mathlib leaf `lem-weil-pbc-adjunct-counit-identity` for the explicit adjunct formula, `def-kun-kunneth-map` to apply it to this particular map, and `def-kun-unbounded-exchange` for the unit. I read the leaf's full statement and the corresponding adjunction source. The seven-term equality follows from the unit naturality square for `A`, step 4, and preservation of composition by `R`. Its left endpoint is the bottom Kunneth map after the left vertical arrow; its right endpoint is the right vertical arrow after the top Kunneth map. This proves both-variable naturality, with single-variable naturality obtained by setting one map to the identity.

For B–E, there are no new statements to test for false hypotheses, no statement-only nodes accidentally carrying proofs, no duplicate nodes, and no relocation of the conclusion into an auxiliary lemma. I checked small cases directly: when `f=g=id`, both counits and comparisons reduce the calculation to ordinary tensor functoriality; when one complex is zero or `Lambda` is the zero ring, all displayed equations remain valid; identities in either coefficient variable give the expected one-variable square. The unboundedness is retained throughout. I checked the existing dependency closures for `def-kun-kunneth-map`, `lem-kun-inverse-image-monoidal`, `def-kun-unbounded-exchange`, and `lem-weil-pbc-site-derived-tensor-descent`: none reaches the item, so these edges introduce no cycle. The original gap was the compressed mate argument and its underived-only citation; both were corrected as described. All thirteen citations in `citations.json` are verbatim pieces of the statements read, not paraphrases of their proofs.

## Second reading by Q45

- Item statement: checked against the complete blueprint node `lem-kun-kunneth-map-natural.md` and the preceding `def-kun-kunneth-map.md`; the repaired bindings for $c$, $\varphi$, and $\psi$ preserve every displayed vertex, arrow, and unbounded-category hypothesis.
- Step 1: checked the chosen Cartesian-square identification against `def-weil-pbc-cartesian-square`, site size against `def-weil-size-convention`, the unbounded tensor bifunctor against `lem-weil-pbc-site-derived-tensor-descent`, the three adjunctions against `def-kun-unbounded-exchange`, and the transpose against `def-kun-kunneth-map`; all cited statements supply the claimed data.
- Step 2: checked the comparison direction and inverse cancellation against `lem-kun-inverse-image-monoidal` and the canonical identifications in `def-kun-kunneth-map`; the written domains and codomains match, and the two-line inverse/naturality calculation is elementary.
- Step 3: checked both counit naturality equations against the fixed adjunction data in `def-kun-unbounded-exchange`; applying $p^{-1}$ and $q^{-1}$ preserves the displayed compositions, so the elementary label is justified.
- Step 4: checked tensoring of the two Step 3 equations against the bifunctor and composition compatibility in `lem-weil-pbc-site-derived-tensor-descent`, then checked the transpose composite against `def-kun-kunneth-map`; every intermediate composite has matching type and the inference is elementary.
- Step 5: checked the mate formula against `lem-weil-pbc-adjunct-counit-identity`, the Kunneth transpose against `def-kun-kunneth-map`, and unit naturality against `def-kun-unbounded-exchange`; the expanded six equalities prove exactly the displayed square.
- New nodes: none; therefore B1--B7, duplicate searches, Mathlib leaf checks, and new-node edge cases are vacuous. Existing dependencies were searched by id and terminology; no duplicate naturality node or exact Mathlib declaration was found.
- Small cases: identities on either coefficient, $E=0$ or $K=0$, and the zero coefficient ring reduce every equation to functoriality or zero composition; the case $f=g=\mathrm{id}$ reduces to ordinary derived-tensor bifunctoriality.

Changes made in this second reading:

1. Added `def-weil-pbc-cartesian-square` to Step 1's `uses` and to `proof_deps`, and added its verbatim statement quote to `citations.json`; Step 1 explicitly uses the square's chosen pullback identification, so omitting this dependency violated C1.
2. Retained the worker's notation repair and expanded mate calculation after checking them against the source; no hypotheses were added or dropped and no auxiliary node was introduced.
