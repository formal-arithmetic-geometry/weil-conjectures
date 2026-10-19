# Worker report: sk-lem-coprojection

## Files written

- `dag/nodes/sec-smooth-purity/sk-lem-coprojection.json`: split into nine steps using existing DAG nodes; no Mathlib match for the whole item.
- `dag/units/sk-lem-coprojection.json`: filled only `realized` and `realized_by`, because the item is its unit's key statement.
- `citations.json`: a verbatim statement quotation for every cited node in every step.

There are zero new nodes and zero new Mathlib leaves. The never-landed helper `lem-pur-general-coprojection-etale` from the earlier sandbox attempt was removed; its general geometric co-projection assertion was a relabelling of the substantive conclusion, and its claimed closed audit was unsupported.

## Attachments

No finished attachment claimed. The four sorry-free bodies in `WeilConjectures/EtaleCohomology/Purity/Smooth/Coprojection.lean` state the main, base-pullback, twist and diagonal formulas, but the imported audit of the main declaration is `rests_on_sorry`, not `closed`. It has an additional explicit `HasCompactification` instance. Thus I did not treat its short body as a finished proof or replace the imported audit with a hand-written `closed` claim.

The missing-frontier entry `AlgebraicGeometry.Scheme.hasTorsionCohomologicalDimensionLE_of_isAffine` refers to `WeilConjectures/AlgebraicGeometry/Sites/AffineTorsionCohomologicalDimension.lean`, which does not exist at the prescribed source checkout path. Its old source frontier is retained as metadata; this split does not use that declaration or an affine cohomological-dimension bound. The other recorded open declarations already name existing DAG nodes. No speculative node for an unread, unavailable signature was introduced.

## WANTED

None for the mathematical proof. Maintenance should refresh the stale Lean audit mentioned above; its absent module cannot be read as directed by the standing brief.

## Statement and prior-attempt errors

STATEMENT-DISPUTED: the final specialization wrote a diagonal as an inclusion while introducing only an arbitrary morphism `f`. The main lemma applies to closed immersions; an arbitrary diagonal is not a closed immersion. For example, glue two copies of the affine line over a field along the punctured affine line. For the resulting doubled-origin scheme over the field, the pair of distinct origins belongs to the closure of the diagonal in the cross-chart affine plane, but is not on the diagonal. The diagonal is not closed. I repaired this typing/hypothesis omission by explicitly taking `f` separated in the final clause and writing its closed diagonal as `Delta : X -> W`. This states explicitly the closed diagonal already intended by the original notation; the main and base-pullback formulas have no new restrictions. The definition of separated used here is exactly `def-weil-proper-morphism`.

The imported statement says ordinary small etale sites, whereas its former dependency `sk-def-purity-conv` fixes pro-etale sites and coefficient rings `O_E/varpi^n`. The earlier sandbox also cited `def-weil-derived-tensor`, which is explicitly pro-etale, and used `pur9-cs-def-invertible`, whose ring is `O_E/varpi^n`, for an arbitrary finite commutative ring. I removed those mis-typed dependencies. The item now names the existing ordinary-etale tensor, category, constructibility, Tor and adjunction nodes, and spells out the generic inverse-pair and twist data inline. This does not identify distinct coefficient categories.

The blueprint proof tests only objects in `D^b_ctf(Z)` without supplying a preservation theorem that puts both represented objects in that subcategory. I use its identical five-line argument for every ambient object instead. This avoids assuming the conclusion objects are bounded constructible; the ambient closed adjunction and projection theorem actually supply these Hom bijections. No source route is changed: the same adjunction, tensor inverses, projection formula, adjunction, tensor inverses, and Yoneda are used.

## Not duplicates

No new nodes. Whole-blueprint searches for co-projection, right adjoints, inverse image, and tensor inverses, and whole-DAG searches by keywords, declaration and source tag, were read. `lem-pur-coprojection` is a related pro-etale statement in the chapter's fixed coefficient setting, not this ordinary-etale arbitrary-finite-ring statement. `lem-pur-immersion-twist` likewise has the chapter's different coefficient/site conventions. Accordingly the item's `same_as` is empty. Existing generic tools were reused rather than duplicated.

## Review by Q78

I read the current main-20261015 statement and full proof for `sk-lem-coprojection`, the unit and chapter records, the older related co-projection node, the ordinary-etale Lean module `Coprojection.lean`, its `Coefficients.lean` definition of `DerivedCategory.isInvertible`, and the project abstract tensor-adjunction implementation. The source uses the same Hom argument as the unit; its general helper needs tensor inverse data and projection, not an independent geometric purity theorem. I also read Stacks `etale-cohomology.tex`, Tag 0F0G, label `lemma-projection-formula-proper-mod-n`: it allows arbitrary unbounded objects over a torsion coefficient ring and a proper morphism. A finite commutative ring meets the coefficient hypothesis, and the separately cited closed-proper theorem meets the geometric one. There are no new nodes needing a separate source.

Step 1 reads and uses exactly the statements of the arbitrary-ring Grothendieck-sheaf theorem, the commutative-ringed-site closed tensor theorem, the small-ringed-site functorial flat cover, the generic derived monoidal theorem, and the ordinary-etale tensor-unit theorem. I verified the small representatives, commutativity, additive closed tensor and functorial flat-resolution hypotheses before invoking the derived monoidal result. Its K-flat formula is the tensor defined in the item.

Step 2 writes both natural tensor composites using the chosen two inverse isomorphisms, associativity and the unit. It then uses the existing Mathlib leaf `lem-weil-pbc-quasi-inverse-adjoint`, whose statement explicitly gives both adjunctions and natural Hom bijections. It does not assume an arbitrary pair of inverse-object evaluations already satisfies triangle identities: that leaf supplies an adjusted adjunction from quasi-inverse functors. Step 3 checks that the module inverse-image theorem supplies the coefficient-unit identification and exactness, that the exact-functor theorem identifies the derived inverse image termwise, and that `lem-kun-inverse-image-monoidal` states the needed two-variable comparison. Pulling back each inverse gives both required inverse orientations. No pro-etale comparison theorem is used.

Step 4 uses only closed-proper clause (a), the ordinary-etale finite-ring proper projection isomorphism, its actual map definition, and `lem-exc-closed-ambient`. I opened their statements and checked the sites, arbitrary finite ring, commutativity for tensor, properness and unbounded domains. In particular, a definition of the projection map is not used as evidence of invertibility. Step 5 writes all five Hom bijections in the source order and identifies the cited statement supplying each. The inverse in the third Hom step is the genuine projection isomorphism. Naturality in both variables comes from the cited adjunctions and natural projection transformation. The test category is the whole ambient category, so no unproved preservation input is hidden.

Step 6 uses the generic `lem-galois-yoneda-fully-faithful`, whose statement gives the actual bijection on natural transformations for every category. Applying its injectivity to the two composites verifies both inverse identities, rather than citing the scheme-only Yoneda lemma. Step 7 reads the inverse-image composition statement for abelian sheaves and writes the extra naturality check for each multiplication endomorphism by a constant scalar, then uses local constancy of the coefficient ring and the sheaf axiom to check every local scalar. This makes the comparison linear without assuming monoidal coherence of that comparison. Exactness and termwise derivation then give the composition isomorphism on complexes. Step 8 is an elementary even-shift reindexing in the total tensor definition, with the summand sign supplied explicitly; it uses the invertible twist and restriction data already quantified in the statement, not a theorem claiming a geometric Tate object exists for every finite ring. Step 9 checks closedness by the explicit separated hypothesis, obtains both invertible projection pullbacks from Step 3, and spells out the two co-projection applications with the unit inserted. The intermediate objects are allowed by the ambient strengthening actually proved in Steps 5-6. The hypothesis that omega is invertible is assumed in the item, so the blueprint's downstream smooth-purity citation is unnecessary.

I checked the small cases: the coefficient unit as `L` gives inverse tensor functors equal to the identity; `i = id` gives associativity/unit identifications; an empty closed subscheme gives the unique isomorphism in the zero derived category; `m = 0` gives the untwisted formula; either diagonal tensor factor can be the unit. The nonseparated doubled-origin example detects the final clause's omitted closed-diagonal condition. The zero ring causes no exception: its module derived category is zero. The steps do not use finite type or Noetherianity anywhere. I checked every proof dependency for a return path to the item by reading the DAG; none has one.

I checked delivery-errors B-E against the actual JSON and the sources: no new statement-only nodes, no elementary or clause nodes, no fabricated search, no unsupported attachment, no inferred definition-as-theorem, no unnamed non-elementary input, and no replacement of the unit route. Every `uses` entry has its exact statement quoted in `citations.json`. Off-unit generic tools are individually justified in `split_report.tool_uses`; these serve the unit's own Hom calculation.

The recorded item Mathlib searches are the exact queries in `searches.jsonl`, with two different phrasings of the geometric co-projection and generic right-adjoint formulation. I read the returned generic derived-adjunction, module-tensor, and projection hits; none states the ordinary-etale exceptional comparison. Loogle's unknown-identifier responses are recorded as such rather than as a found theorem. All services used in these runs answered; no unavailable service is claimed absent.

## Unfinished work

No mathematical step is left unfinished. This sandbox is submitted to the required server preflight through `deliver.py Q78 sk-lem-coprojection --no-push`; READY is reported only after it prints OK. This worker does not push; the fresh second reader repairs and delivers.

## Second reading by Q78

- Item statement: checked against blueprint node `sk-lem-coprojection` and its proof source; the finite commutative coefficient, ordinary small-etale categories, ambient definitions, and all three specializations are present. Verdict: PASS after retaining the explicit separated hypothesis needed for the closed diagonal.
- Step 1: checked every cited tensor, Grothendieck, flat-cover, and derived-monoidal statement; the hypotheses are verified for the constant commutative ring sheaf and the K-flat tensor is identified. Verdict: PASS.
- Step 2: checked the two-sided inverse calculation against `lem-weil-pbc-quasi-inverse-adjoint`; the natural Hom transfer follows from the cited statement. Verdict: PASS.
- Step 3: checked exact inverse image, termwise derived functor, monoidal comparison, and pullback of both inverse isomorphisms. Verdict: PASS.
- Step 4: checked closed-immersion properness, finite-ring ordinary-etale projection formula, its map definition, and the ambient exceptional adjunction. Verdict: PASS.
- Step 5: checked all five Hom bijections in order and their naturality; each non-elementary arrow is supplied by a cited node. Verdict: PASS.
- Step 6: checked the represented-presheaf argument against `lem-galois-yoneda-fully-faithful`; injectivity gives both inverse identities. Verdict: PASS.
- Step 7: checked inverse-image composition, scalar linearity, exactness, and passage termwise to derived categories. Verdict: PASS.
- Step 8: checked the even-shift reindexing and signs against `def-kun-derived-tensor`; the Tate inverse and restriction data are explicit. Verdict: PASS.
- Step 9: checked separatedness gives a closed diagonal, both pulled-back factors are invertible, and the two applications of Step 6 produce the displayed parenthesized formula. Verdict: PASS.
- New nodes: none; therefore B1–B7 and duplicate-node checks are vacuous. Existing keyword/tag searches were read, including the related pro-etale co-projection node, and no duplicate was introduced. Verdict: PASS.
- Small cases and edge hypotheses: checked the unit, identity immersion, empty closed subscheme, zero ring, zero twist, and doubled-origin nonseparated example. Verdict: PASS; the latter confirms why separatedness must remain explicit.
- Changes made: no JSON or citation changes were necessary. Added this independent second-reading record only; the split remains zero new nodes and zero Mathlib leaves.
