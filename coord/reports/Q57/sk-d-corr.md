## Worker report

Files written:

- `dag/nodes/sec-trace-formula/sk-d-corr.json`: the existing definition, split into eight explicit construction and Hom-calculation steps using existing nodes; the operation domains in the supported-class clause and final identification are corrected.
- `dag/units/sk-d-corr.json`: only `realized` and `realized_by` record the key definition; statement, route, source and other metadata are unchanged.
- `citations.json`: eighteen step/dependency entries, quoting the complete current statements so that domain qualifiers accompany the formulas.

New nodes: 0. New Mathlib leaves: 0. No new node or duplicate definition is needed. The sandbox's earlier four uncommitted clause definitions were removed by the preceding attempt; this retry creates none. The helper scripts are sandbox-only and are not delivery files.

Attachments: none for the whole item. I reread `WeilConjectures/SixFunctors/ProEtale/TraceFormula/Correspondence.lean` in the read-only slopmaster2 source. `AlgebraicGeometry.ProEtale.Correspondence` (133–152) states the tuple, not every clause of the item, and uses the globally supplied exceptional-functor setup. Its fixed and product constructions are at 164–209. `AlgebraicGeometry.ProEtale.SupportedClass` (109–111) already requires compactifiability. `AlgebraicGeometry.ProEtale.Correspondence.classEquiv` (762–770) requires geometric source, target and support, constructible inputs, and compactifications of the support map and product projection. These are not an attachment of the generic imported statement. Master source is reference material only; no sorry declaration was treated as finished evidence.

WANTED: none. I used the current main-20261015 blueprint, existing DAG statements, Stacks Tag 0D6D, and the existing categorical Mathlib leaf. No SGA source is cited.

What was wrong: earlier uncommitted child definitions duplicated clauses of the item. The saved generic Hom calculation used `sk-d-six` as though its comparisons and exceptional adjunctions were on the entire unbounded category. The current reviewed statement explicitly restricts those comparisons to `D^b_ctf`. Merely requiring that some ambient right adjoints exist does not justify applying that package's projection formula to arbitrary K. This retry repairs that domain error as described below; it does not insert an unused direct citation of the narrower `thm-sf-comp-composition`.

What remains after the required dry run: independent second reading and delivery by that reader. No delivery is authorized for this first worker; the worker hands over the sandbox only if the no-push check prints OK. No Lean was written, no compiler/Lake/build was run, no agent was started, and no live repository or launcher file was written.

## Source error

STATEMENT-DISPUTED: the main-20261015 `sk-d-corr` final Hom formula uses `Rc_!` and `p_1^!` after assuming compactifiability and an exceptional adjoint only for `c_1`. Its arbitrary-map supported-class sentence also presumes `Ri_!` exists. The missing domains are real, not just omitted notation. For example, over `s=Spec k`, let X be a countably infinite disjoint union of copies of s, take Y=C=s, take `c_1=id` and `c_2` the inclusion of one component, and take constant coefficients and the identity coefficient map. These satisfy the generic tuple conditions. But Z=X and `p_1:X→s` is not quasi-compact. A compactification over the field would embed X as an open subscheme of a proper finite-type k-scheme. Such a scheme is noetherian, so every open subscheme is quasi-compact, whereas X is not. Thus p_1 has no such compactification. This argument also works with the current blueprint convention in which the open immersion is not required a priori to be quasi-compact. The expression `p_1^!L` is outside the stated domain. The same map as i exposes the arbitrary-i supported-class error.

There is also a finite-Tor domain error in the saved repair: the now-reviewed `sk-d-six` supplies the projection formula only for its bounded constructible finite-Tor inputs. At the point scheme, `K=⊕_{j≥0} A_s[j]` lies in the ambient derived category but is unbounded, so the package's projection formula at M=K cannot be cited. This is a type/domain counterexample to that inference, not a claim that every wider projection formula is false.

The corrected statement keeps the generic tuple, opposite supports, factor exchange and fixed equalizer. A supported class is defined for a compactifiable i where the given operations actually supply `Ri_!A_T`; P and its Hom group remain ambient. For the final identification only, K and L lie in `D^b_ctf`, c and p_1 are compactifiable, and the exceptional adjunctions for c, p_1 and c_1 are supplied on the same full subcategories. The last right adjoint must agree at L with the one in u. Projection and composition use the package on that domain. This makes the formula typed and agrees with the bounded constructible intent of the unit record and the actual Lean class-equivalence declaration; it does not impose boundedness on every correspondence. The full-subcategory condition ensures the calculated Hom sets are the ambient Hom sets in the source display. No claim of an ambient unbounded exceptional adjunction is added.

I named p_1 and p_2 explicitly and retained all structure maps. The current item/source are main-20261015; the unit's verbatim text remains the older master snapshot, which this worker cannot rewrite. This correction concerns the source's missing operation hypotheses, not a target statement.

## Not duplicates

No new nodes survive. I searched the whole imported blueprint with `tools/blueprint_refs.py search` for supported class, correspondence and derived pullback, and searched `dag/nodes` for the notions and Tag 0D6D. I reread `def-trf-correspondence-between-pairs`, `lem-trf-correspondence-class`, `def-trf-supported-class` and `def-trf-fixed-scheme`: they use the older geometric/bounded-constructible/admissibility setting and cannot attach the generic tuple plus all clauses. Their support constructions are direct applications of the existing fibre-product universal property. The final class equivalence is expanded here, not moved into a new restatement. Ordinary pullback composition is already `lem-weil-pbc-proetale-derived-pullback-composition`; right-adjoint composition is already the categorical Mathlib leaf `lem-cat-right-adjoint-composition`.

The item retains exactly its six logged Mathlib queries: grep `Correspondence|SupportedClass|correspondenceClass`; Loogle `"Correspondence"`; LeanSearch `Cohomological correspondence supported class scheme exceptional pullback`; Loogle `"curryHomEquiv"`; and the two LeanFinder phrases about a cohomological correspondence and about classes as Hom of compact-support direct image into internal Hom. I read the sandbox's `searches.jsonl`, whose actual tool names, query texts and result lists agree with every retained entry. The first semantic search returns scheme-module adjunctions, the second returns light-condensed internal-Hom maps; neither states this item. Loogle returns algebraic congruence correspondences and general categorical currying. Those do not provide all scheme support data or exceptional operations. No search was fabricated, re-dated or relabelled, and no new Mathlib leaf is claimed.

## Review by Q57

I read the main-20261015 `sk-d-corr/_section.md` in full, the current `sk-d-six` source and its reviewed DAG statement, `sk-d-setup`, the chapter and unit records, the actual slopmaster2 tuple/class-equivalence source, and every dependency statement quoted in `citations.json`. For tensor–Hom I read `def-sfb-derived-hom-sheaves.md` and `def-sfb-derived-tensor-hom-adjunction-sheaves.md`. This is the ordinary sheaf-coefficient layer with `𝒜=Mod(A)`; no condensed-ring module-object category is substituted. For ordinary composition I read Stacks `sites-cohomology.tex`, `lemma-derived-pullback-composition`, Tag 0D6D, including its K-flat pullback proof. For exceptional composition I read `Adjunction.comp` in pinned Mathlib `CategoryTheory/Adjunction/Basic.lean:567–580` and `Adjunction.rightAdjointUniq` in `CategoryTheory/Adjunction/Unique.lean:102–108`. There are no new-node sources to validate.

Step 1 uses `sk-d-setup` for coefficients and categories, `sk-d-six` for the given operations and conditional adjunction, `def-weil-scheme-over-base` for the two structure-map equations, and `def-nagata-compactifiable` for its exact meaning. It defines a tuple where the stated functors and adjoint are supplied, and proves no unconditional existence of a correspondence or unbounded adjoint.

Step 2 uses precisely the universal map in `def-pc-fibre-product`: the commuting equations over s give c and the swapped opposite map; exchanging projections twice is the identity by uniqueness. Its other fibre product gives E. The two proposed structure maps coincide by the equality of the maps to Z. This is an elementary universal-property calculation, not an uncited theorem on intersection supports.

Step 3 again uses that universal property. I checked both directions: a map into the diagonal pullback has two equal legs, and a test map t with equal legs has the unique lift `(t,c_1t)`. Thus F is the equalizer for arbitrary X. I do not infer a closed immersion from this; no separatedness hypothesis is used.

Step 4 uses the same coefficient and operations nodes and the compactifiability definition. I repaired the implication “compactifiable, so the arbitrary ambient Ri_! is defined”: the definition now expressly requires the given operation on A_T. It is just the displayed ambient Hom set. There is no assertion of a right adjoint or of dependence only on the image of i.

Step 5 uses the tensor–Hom adjunction exactly as stated, with M in its first tensor slot. The evaluation expression sends α to evaluation after `1_M⊗α`. Precomposition by the symmetric braiding changes to the required `Rc_!A_C⊗M` ordering. `sk-d-setup` supplies pullback stability, so M is in the package's finite-Tor constructible domain. N is there by the stipulated restricted right-adjoint functor. A_C is constant free rank one in degree zero, so its constructibility and Tor interval [0,0] are elementary from the coefficient definition. The internal Hom can be computed in the ambient category; the proof never invokes an uncited internal-Hom preservation theorem.

Step 6 uses the projection formula actually quoted by `sk-d-six` at `(A_C,M)`, now with both inputs in its stated domains. I checked the direction: the formula followed by the unit isomorphism points to `Rc_!c^*M`; the Hom bijection precomposes with its inverse. `sk-d-setup` places `c^*M` and its compactifiable direct image in `D^b_ctf`. N is already there, so the stipulated exceptional adjunction on those full subcategories applies. The elementary part is substituting the cited maps, the unitor, and the adjunction Hom bijection; it does not assert a new projection formula for arbitrary objects.

Step 7 uses `prop-weil-pbc-proetale-constant-ring-map` for the ring-sheaf identifications. Its finite-ring hypothesis is satisfied by `A=𝒪_E/ϖ^n`. The identification for a composite agrees because both canonical maps send each constant section to the same constant section and sheafification gives the unique extension. The entire statement of `lem-weil-pbc-proetale-derived-pullback-composition` then applies to `(c,p_2)` with these compatible ring-sheaf identifications, giving `c^*p_2^*K≃c_2^*K`. The composition field of `sk-d-six` is applied on the stipulated full `D^b_ctf` categories: `Rp_{1!}Rc_!≃Rc_{1!}`. After transporting the restricted adjunction across that left-functor isomorphism, `lem-cat-right-adjoint-composition` gives `c^!p_1^!≃c_1^!` on the same categories. Its statement is the needed right-adjoint uniqueness result, not merely fully faithful Yoneda. Evaluation at L and the two component isomorphisms give the last Hom bijection. Pullback composition and the coefficient identifications remain declared generic tool uses; no unit route is replaced.

Step 8 composes those bijections and defines [u] by their inverse. Each inverse recovery is immediate. No lemma restating the final clause is created and no additional existence assertion is hidden.

For B1–B10, there is no new unsplit node, no proof disguised inside one, no invented Stacks tag or Mathlib line, and no purported complete Lean attachment. All object domains in the item are now introduced. Its blueprint `is` remains the import's id, `from` is null, and `same_as=[]` after the whole-blueprint search; the existing narrower nodes are not duplicates of its whole corrected definition. For C1–C8, I reopened all nine distinct cited statements, checked the exact coefficient/site/domain at their use, preserved the tool-use declarations, and rebuilt eighteen complete-statement verbatim quotes. The graph remains acyclic under the existing dependencies; server checks are still required. For D1–D5, all eight steps carry their arguments; no new node is a clause or the whole item. For E1–E7, I checked the infinite-disjoint-union failure, the unbounded point-complex failure, the ordinary-vs-exceptional leg orientation, and the inverse projection-formula direction. Empty supports give the zero unit and zero Hom group; equal legs give F=C; with identity maps the comparison is the identity by the package's coherence; zero coefficient objects yield zero groups. These cases do not need a dropped nonempty or dimension hypothesis.

What this retry corrected: the reviewed package's restricted comparison domains, the final exceptional adjunctions' common domain, their agreement with u, and the unsupported assertion that compactifiability itself supplies an arbitrary ambient functor. The previous report's claim that package comparison isomorphisms are unrestricted is withdrawn. The generic structure definition is retained; the final bounded constructible correction is explicit under Source error.

## Earlier dry-run failure and current route

Earlier attempts failed with `units: sk-d-corr cites sk-thm-sf-comp-composition, which its nodes do not reach`. That historical finding is no longer predicted by the current shared DAG. The now-reviewed `sk-d-six` has a genuine statement dependency on `thm-sf-ctf-stability`, which reaches `thm-pur-general-admissibility` and then `thm-sf-comp-composition`, realizing the required unit. I checked that path by reading the current dependency records. No unit metadata was changed to manufacture reachability. This item's calculation still does not directly apply the narrower finite-type etale-origin composition theorem to arbitrary ambient complexes.

## Server dry run

The required command is `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q57 sk-d-corr --no-push .`. It was started before the scope repair and reads the sandbox only after worktree admission, so the reviewed files above are its input. This check runs the maintainer preflight, DAG and split checks on the server. The worker answers READY only after it prints OK; a failure is repaired before that handover. No push is requested.

## Earlier second reading (a previous round; superseded)

- Item statement: I read the current `main-20261015` `sk-d-corr/_section.md` and the
  Lean `Correspondence.lean` declarations at lines 105–152, 162–209 and 762–785.
  The generic tuple, opposite support, fixed equalizer, supported Hom group, and
  class bijection are all present.  The final display is only typed on the
  bounded constructible subcategories with the compactification and adjunction
  data that the Lean `classEquiv` declaration requires; the report's explicit
  domain correction records the source omission.  The zero object, identity
  correspondence, point scheme, and empty support give respectively the zero
  Hom, identity comparison, ordinary unit, and zero Hom, so no nonempty or
  dimension hypothesis was introduced.
- Step 1 — PASS: checked against `sk-d-setup`, `sk-d-six`,
  `def-weil-scheme-over-base`, and `def-nagata-compactifiable`; it constructs
  data and makes no existence claim.  The ordinary leg is explicitly `c_2`.
- Step 2 — PASS: checked against the complete fibre-product universal property in
  `def-pc-fibre-product`; the two structure-map equations give the unique
  product map, factor exchange, and the two equal structure maps on the
  intersection.  The calculation is elementary.
- Step 3 — PASS: checked against the same fibre-product statement; the two equal legs
  give exactly the universal equalizer lift.  No separatedness or closedness
  assertion is used.  The calculation is elementary.
- Step 4 — PASS: checked against `sk-d-setup`, `sk-d-six`, and
  `def-nagata-compactifiable`; it defines the Hom group only when the supplied
  operation has the required domain and retains the support map.  This is
  elementary from those definitions.
- Step 5 — PASS: checked against the complete tensor–Hom adjunction node, the braided
  monoidal data in `sk-d-six`, and pullback/exceptional-domain data in
  `sk-d-setup`; the tensor slot, evaluation map, and ambient Hom categories
  have the displayed orientations.  It does not assume internal Hom preserves
  the restricted subcategory.
- Step 6 — PASS: checked against the projection formula and exceptional adjunction in
  `sk-d-six`, with `sk-d-setup` supplying pullback and compactifiable direct
  image stability.  Both inputs lie in the stated bounded constructible
  domains, and the unitor and inverse direction of the Hom transport are
  explicit.
- Step 7 — PASS: checked against the full constant-ring and derived-pullback
  composition statements, the restricted composition comparison in `sk-d-six`,
  and `lem-cat-right-adjoint-composition`.  The composite right adjoint is
  transported on the same full subcategories and evaluated at `L`; the map
  orientation is `p_2c=c_2` and `p_1c=c_1`.
- Step 8 — PASS: checked as the inverse of the bijections in steps 5–7; it introduces
  no new lemma or hidden existence assertion.
- New nodes: none. I independently searched the complete `dag/nodes` tree by
  Tag 0D6D and by correspondence, supported class, opposite intersection and
  fixed scheme. I read `def-trf-correspondence-between-pairs`,
  `lem-trf-correspondence-class`, `def-trf-supported-class`,
  `def-trf-fixed-scheme`, and `def-trf-correspondence`: their geometric,
  bounded-constructible hypotheses do not define the generic tuple here,
  and using the class lemma would merely repackage the final clause. The
  worker had already removed its four clause nodes. No B1–B7 new-node
  statements remain. I checked all 18 citation quotes against the complete
  current node statements and checked that every step dependency has a quote.
  I ran independent LeanFinder and Mathlib grep queries in different wording;
  the former returned eight underived sheaf-module adjunction declarations,
  the latter zero hits. Neither states this complete item. Both actual results
  are logged, and are added to the item's existing six search records.
- Changes made by this second reader: explicitly defined the diagonal by its
  two projections in step 3; spelled out why the tensor object is in the
  restricted domain by its unitor in step 6; replaced the compressed
  adjunction transport in step 7 by its Hom bijections, and wrote the final
  map and inverse. I strengthened the report's source-error counterexample
  to work for both compactification conventions: opens in a proper scheme
  over the field are quasi-compact by noetherianity. The worker's domain
  corrections and all 18 exact citations are preserved. No new nodes or
  Mathlib leaves were created, and no Lean or live project file was written.

## Second reading by Q57

- Item statement: checked against the main-20261015 blueprint section and the read-only slopmaster2 correspondence/class-equivalence declarations; PASS, with the recorded domain correction for supported classes and the final bounded-constructible Hom identification.
- Step 1: checked against `sk-d-setup`, `sk-d-six`, `def-weil-scheme-over-base`, and `def-nagata-compactifiable`; PASS, all tuple data and operation hypotheses are introduced without an existence claim.
- Step 2: checked against `def-pc-fibre-product`; PASS, the product map, factor exchange, intersection, and structure-map equality follow from its stated universal property.
- Step 3: checked against `def-pc-fibre-product`; PASS, the diagonal pullback has the stated equalizer property, including both universal directions and no extra separatedness hypothesis.
- Step 4: checked against `sk-d-setup`, `sk-d-six`, and `def-nagata-compactifiable`; PASS, the supported Hom group is formed only when the supplied `Ri_!A_T` operation exists.
- Step 5: checked against `def-sfb-derived-tensor-hom-adjunction-sheaves`, `sk-d-six`, and `sk-d-setup`; PASS, tensor slot, braiding, evaluation, and restricted-domain objects are stated with the correct orientations.
- Step 6: checked against the projection formula and exceptional adjunction clauses of `sk-d-six` plus stability in `sk-d-setup`; PASS, both inputs and the unitor-identified tensor object lie in the required full subcategory.
- Step 7: checked against the constant-ring and derived-pullback composition nodes, `sk-d-six`, and `lem-cat-right-adjoint-composition`; PASS, ordinary and exceptional composition are applied on their common domain and the final map/inverse are explicit.
- Step 8: checked against the preceding Hom bijections; PASS, the supported class is defined by their composite inverse and no conclusion is moved into a new node.
- New nodes: none; therefore no B1–B7 node statements or new Mathlib leaves required checking. Existing-node search covered the complete DAG and blueprint by correspondence, supported-class, fixed-scheme, opposite-intersection, and Tag 0D6D terms.
- Changes made in this second reading: retained the worker’s corrected operation domains and exact citation quotes; confirmed the source-error counterexamples and small cases; added this explicit review section. The dry run passed with preflight and DAG checks.
