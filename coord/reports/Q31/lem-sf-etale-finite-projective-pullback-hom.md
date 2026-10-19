# Worker report

## Files written

- `dag/nodes/sec-six-functors/lem-sf-etale-finite-projective-pullback-hom.json`: retained the statement and supplied a three-step split; no new nodes and no Mathlib leaves.
- `citations.json`: nine verbatim statement quotations, covering every node used by every step.
- `searches.jsonl`: seven searches run through `msearch.py` for the item.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the item id, its blueprint tag, finite-projective Hom and pullback-Hom terms, and the upstream declaration names. The only nearby declaration is the more general derived theorem `AlgebraicGeometry.Etale.DerivedCategory.nonempty_iso_leftDerivedUpperStar_derivedHom`; it has a dualizable derived first variable and does not state this ordinary constant-sheaf assertion for an arbitrary finite commutative ring.

WANTED: none.

## What was wrong or missing

The imported item had no proof. I did not create a finite-free child node: the free calculation is a two- or three-line basis argument from the sheaf Hom definition and the tensor-Hom adjunction, and the projective case is its explicit split-retract calculation. The existing `lem-sf-hom-finite-projective` and `lem-pod-finite-projective-tensor-hom` nodes concern coefficient-stage six-functor data and derived tensor-Hom, respectively; neither states the present arbitrary finite-ring etale pullback comparison. The imported Stacks proof's last displayed sentence writes `Hom(h^*E,F)`; the canonical map and the surrounding construction require `Hom(h^*E,h^*F)`, which is the corrected form used here.

## Not duplicates

- `lem-sf-etale-finite-projective-pullback-hom` vs `lem-sf-hom-finite-projective`: the existing node assumes a fixed six-functor datum and proves tensor-Hom/biduality for a coefficient-stage module, while this item is an ordinary sheaf pullback comparison for every finite commutative ring.
- `lem-sf-etale-finite-projective-pullback-hom` vs `lem-pod-finite-projective-tensor-hom`: the existing node is a derived coefficient-category tensor-Hom theorem (including completed and scalar-localized stages); this item is degree-zero etale sheaf Hom and adds a morphism-of-schemes pullback.
- `lem-sf-etale-finite-projective-pullback-hom` vs `sk-thm-sf-internal-hom-pullback`: the blueprint theorem fixes `A_{E,n}` and derived dualizable objects; it is not the arbitrary finite-ring ordinary sheaf statement here.

## Review by Q31

I read the item statement, its chapter `sec-six-functors`, unit `sk-prop-sf-biduality-general`, and the ancestor blueprint paragraph for the finite-projective term identity. I also read Stacks Project `cohomology.tex`, Tag 0GM7, the proof of clause (1), including the local strictly-perfect calculation and its final direct-summand sentence. The item hypotheses are exactly those needed there after specializing the ringed spaces to small etale sites with constant finite coefficient ring: `S'` and `S` are schemes, `g` is arbitrary, `F` is any module sheaf, and `M` is finite projective with no flatness or constructibility condition.

Step 1 uses the definition of the constant sheaf and the exact inverse-image statement. I checked that the latter really supplies both additive exactness and identification of the inverse image of the constant ring sheaf, so the maps `i` and `p` remain a split pair after constant sheaf formation and pullback. No complement of `M` is chosen. The edge cases `r=0` and `M=0` are included.

Step 2 uses the sheaf Hom definition and the closed tensor-Hom adjunction for the coordinate calculation, then the module-pullback tensor comparison and exact inverse image for transport to `S'`. I wrote the basis inverse explicitly, so the free calculation is elementary and the evaluation pairing is visibly the standard coordinate evaluation. The finite sum is preserved by the additive inverse image, and the constant ring sheaf is the one identified in the cited inverse-image theorem.

Step 3 uses the restriction/naturality clause of the sheaf Hom definition, the additive symmetric monoidal structure and natural adjunction of the sheaf tensor-Hom node, and the natural tensor pullback comparison. I opened each cited node and copied the exact used sentence into `citations.json`. The displayed inverse is obtained by precomposing with `g^*p`, applying the already-isomorphic free comparison, and precomposing with `i`; both composites reduce to `p i=1_M` by naturality. This verifies that the map is an isomorphism, that it is the evaluation-induced map required by the statement, and that it is natural in both variables. No step uses a proof detail of a cited node that its statement does not provide.

I checked the small cases `M=0`, `M=A`, `M=A^{\oplus r}`, `F=0`, `g=\mathrm{id}`, and `S'=\varnothing`; the coordinate map and the explicit retract inverse reduce to the expected zero, identity, finite-product, or unique zero maps. I ran the required LeanSearch, Loogle, LeanFinder, and Mathlib grep searches twice with distinct phrasings where applicable; all hits were generic sheaf/pullback infrastructure and none stated this theorem. `srvcheck.py ... check_dag` passed before this report was written. No Lean, compiler, Lake, build, or live-project command was run.

The source typo in the final Stacks sentence was corrected explicitly in the proof discussion above; no hypothesis or conclusion of the item was changed.

## What could not be finished

Nothing remains unfinished in this split. The required dry run is the next step.
