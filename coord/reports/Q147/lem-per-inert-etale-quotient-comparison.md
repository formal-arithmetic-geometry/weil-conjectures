# Q147: lem-per-inert-etale-quotient-comparison

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-inert-etale-quotient-comparison.json`: statement node, split into fourteen proof steps using existing nodes; no Mathlib match.
- `citations.json`: verbatim statements for every proof citation, numbered by step.
- `report.md`: this report. Search evidence remains in `searches.jsonl`.

There are zero new nodes and zero new Mathlib leaves. This resumed attempt retained the earlier sandbox split, report, citations and search log, and compared them against the current repository record (still unsplit). Its creation metadata, ancestry and existing searches were retained. The only statement edits insert references defining separatedness, local Noetherianity, geometric points, finite morphisms and fibre products. They change no hypothesis, conclusion or mathematical meaning. The corresponding statement dependencies were added.

## Attachments

None. I searched the project source under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact blueprint tag and for inertia, inert etale comparison, stabilizers and quotients. The matches in `FundamentalGroup/ExtendOverInertia.lean` concern extending finite etale covers from an open subscheme under a condition on inertia. They do not assert this item's finite-group quotient square or its log clause. I found no declaration supplying every clause. Upstream master sorry statements were not treated as proofs. No Lean was written or compiled.

## WANTED

None. The Stacks source and ILO volume are available locally.

## Existing material corrected or clarified

The imported item had a statement and no proof. Its substantive statement agrees with its sources and was retained. The separatedness assumption makes the complement of the inert locus closed; the scheme proof does not assume that the order of the finite group is invertible. Flat base change for invariants is proved using the kernel of the finite family of differences, not a Reynolds operator.

The log clause is proved on sheaves of commutative monoids. In particular I did not cite an abelian derived exchange theorem as if it covered log structures. In this etale case inverse image is restriction and the structure sheaf and units restrict identically, so the claimed strictness follows by evaluating on each etale test scheme. This is a direct proof of the stated special case of ILO VIII 5.4.2; it does not assert existence or finiteness/saturation of arbitrary invariant log structures beyond the hypotheses of the item.

The blueprint and unit route have not changed. The supporting node still serves the abelian-inertia fourth-stage comparison in the recorded ancestry from `lem-per-artin-gabber-affine-curve` through `lem-per-gabber-abelian-stage-toric-chart`. This item is not the key node of its unit; no unit record was written.

## Mathlib and duplicate searches

The whole-DAG searches included Tag 0DT9 and the concepts of inert/etale quotients, relative fixed loci, henselian finite algebras, clopen etale sections, flat invariant base change, finite-presentation colimit descent and etale restriction of sheaves. The blueprint searches for `inert`, `invariant`, `henselian`, `etale quotient`, and `strict inert` yielded no other blueprint statement of this item. The generic existing nodes found by these searches are the proof dependencies, rather than newly introduced special cases.

The item searches were run using the mandated `msearch.py` command. Semantic results give etale stability/composition, ordinary finite-group orbit equivalences, and inertia-degree identities for prime ideals. These do not state quotient descent or monoid/log strictness. The Mathlib grep in `AlgebraicGeometry/Morphisms/Etale.lean` for `inert|stabilizer|quotient` returned no hits. A second semantic phrasing includes the log clause. The first Loogle attempt reports the identifier `AlgebraicGeometry.IsEtale` unknown on that service; that diagnostic is retained and is not evidence of absence. A subsequent valid `Algebra.Etale` search provides the ordinary algebra results. Every newly recorded query is present in the tool's log; earlier searches on the existing item are retained as inherited evidence.

## Not duplicates

No new nodes were created. In particular I did not introduce a general quotient-comparison node that simply repeats the scheme clause, nor a new log-strictness node that repeats the log clause. The steps carry both arguments. Existing henselian decomposition and retraction statements are cited in their full strength.

## Review by Q147

I read Stacks `groupoids.tex`, Tag 0DT9 (`lemma-etale`), including the strictly henselian decomposition claim, its proof and the final comparison. I also read Tag 03BK (`lemma-invariants-base-change`), especially its flat-kernel calculation. For the log clause I read ILO VIII 5.3.6--5.3.7 and 5.4.1--5.4.2, printed pp.124--127, from the available volume. The item uses the equal-group etale specialization, for which the monoid restriction computation supplies a direct argument. There are no new-node sources to review. The source's phrase "some details omitted" about universal bijectivity in 0DT9 is not used: the delivered comparison is an isomorphism on explicit clopen finite-stage neighborhoods and is descended by the existing fpqc isomorphism theorem.

Step 1 uses exactly the open-diagonal characterization in `def-weil-unramified-morphism`, the etale definition, the closed-diagonal meaning of separatedness, and the fibre product definition. Pulling back the relative diagonal identifies the fixed subscheme as clopen inside the inverse image of the target fixed subscheme. I checked that the bad locus is therefore closed in the entire source, not merely locally closed. Conjugation proves its invariance.

Step 2 uses the affineness clause in `def-weil-finite-integral-morphism`, and `lem-weil-pbc-lfp-affine-opens-finite-presentation` on the actual affine inverse images of quotient charts. Etaleness provides its locally-finite-presentation hypothesis. I do not assume the quotient ring itself is Noetherian or use any unproved invariant-ring finite-generation assertion.

Step 3 applies `lem-weil-pbc-flat-tensor-exact` to the actual kernel sequence of all differences. The group is finite, so its product is a finite direct sum and the componentwise tensor comparison is explicit. This proves flat base change for both A and B. It does not apply the stronger tame/arbitrary-base-change node, whose invertibility hypothesis is unavailable in the scheme part.

Step 4 uses the actual small filtered neighborhood colimit from `def-weil-pbc-strict-henselization-limit`. `lem-weil-pbc-strict-henselization-local-structure` asserts strict henselianity, which the definition alone does not. `lem-weil-pbc-filtered-colimit-algebras-underlying-module` and `lem-weil-pbc-filtered-colimit-flat-modules` justify flatness over C; each stage is etale and flat. The evaluation-image and evaluation-properties nodes give a surjection onto a field, so the lifted point lies over the closed point. I did not infer that closed-point assertion merely from the local-structure node, which explicitly omits a residue-field identification.

Step 5 uses `lem-weil-pbc-finite-over-henselian-local-product`, whose hypothesis is exactly finiteness over the henselian local H. The coproduct-of-spectra node supplies clopen components. `lem-weil-pbc-sepclosed-finite-extension-unique-embedding` gives both separable closedness and uniqueness of the geometric point of each component. The orbit-fibre hypothesis then identifies the component stabilizer with geometric inertia; topological stabilizers alone would not suffice over an arbitrary residue field.

Step 6 uses `lem-exc-etale-lift-sepclosed-base` at the specified geometric point, then `lem-weil-pbc-henselian-etale-retraction` with its actual residue-field-isomorphism hypothesis. The clopen-section node requires etale and separated; here both schemes are affine. Step 7 uses that same retraction's uniqueness for the fixed closed point to make the section K-invariant. Distinct translates lie above distinct components; hence their union is genuinely disjoint. This proves the equivariant copy instead of hiding it in a new node.

Step 8 is the elementary idempotent splitting of that invariant clopen union and the invariants computation already proved in Step 3. Steps 9 and 10 use the two precise assertions of `lem-weil-pbc-filtered-colimit-algebras-tensor-elementwise`: elements have stage representatives, and vanishing becomes true after a refinement. Finiteness of G, the finite presentation from Step 2, and the finite number of generators and relations are exactly what permits one common refinement. I checked both composites of the descended map. Equivariance follows from the specified structural map; no arbitrary nonequivariant isomorphism is substituted. No directed-poset theorem is applied to a merely filtered category.

Step 11 uses the etale base-change assertion of `lem-weil-pbc-etale-base-change-finite-limits`. The actual source cover is etale and surjective, so `lem-trf-etale-descent-through-source-cover` applies. For the comparison, finite affine refinements over an affine target give the flat, surjective, quasi-compact map required by `lem-weil-pbc-fpqc-descend-isomorphism`. The descended isomorphism is the canonical comparison, ensuring that overlaps agree.

Step 12 reads the set-valued formula and adjunction in `lem-weil-pbc-etale-inverse-image-algebraic-structures`, together with the exact site adjunction in `lem-weil-pbc-etale-localization-functor-adjoint`. The graph test object reduces the colimit to restriction. The proof describes multiplication, units and the unchanged covering condition, so it applies to monoids without an abelian-coefficient assumption. Step 13 uses `def-trf-fs-log-blowup` for the meaning of a log structure and log morphism and computes both invariant section monoids on the same test scheme. The structure-map identification includes units, so it proves strictness, rather than only an isomorphism of underlying monoid sheaves. Step 14 uses the fibre-product universal property and ordinary composition of section restrictions to prove the requested compatibility.

I tested the argument on the empty source, a trivial action, a free action, a nonfaithful action, disjoint copies of an etale neighborhood, and finite nonreduced algebras over the strict local base. Empty affine charts are vacuous; the finite product admits the zero-factor case. For a trivial action the copy is the ordinary henselian section and the final assertion is the original etale map. For free actions K is trivial, while for nonfaithful actions K can equal G; the translate construction handles both. No reduction or tameness is needed in Steps 1--11. With trivial log structure the log comparison reduces to the equality of unit sheaves. Retaining the stated fs and very-tame hypotheses does not introduce any new assumption in that computation.

Every cited statement was opened and its relevant hypotheses checked; `citations.json` copies the full statement verbatim for each occurrence. All fourteen steps are shorter than 2000 characters. Their elementary portions are the explicit fixed-locus, kernel, idempotent, finite-equation and restriction calculations, and no new clause of the item has been renamed as a dependency. The external generic tools are declared individually in `split_report.tool_uses` for route review.

## Unfinished work

No mathematical clause is left open in this stage-1 split. The initial resumed server dry run passed at 72dcb6898d. The final dry run is repeated after the repairs documented below; delivery uses the same required tool.

## Resumed source and citation review

The resumed review reread Stacks groupoids.tex, lemma-etale (0DT9) and lemma-invariants-base-change (03BK), and the retained ILO text at VIII 5.3.6--5.3.7 and 5.4.1--5.4.2. The current repository still has this item unsplit and has no blueprint_update. The existing chapter and unit records and current ancestor chain were read; no route or unit record was changed. The project-source searches again found no exact attachment. Every current statement of the proof dependencies was read, and the citation file was regenerated from those statements.

Two small proof clarifications were made. Step 6 now explicitly cites lem-weil-pbc-etale-base-change-finite-limits for etaleness after tensoring with the strict henselization; its first assertion supplies exactly this without hypotheses on the base morphism. In Step 10, equality of the other composite is forced inside the ambient B stages with the original C-indexed colimit theorem. This avoids silently appealing to an additional theorem about changing the filtered indexing category to an undercategory: the finite differences lie in the idempotent summand of B, and their vanishing in B implies their vanishing in the summand. Step 4 now names the relative separable closure explicitly as the field onto which evaluation is surjective; it does not claim surjectivity onto the entire algebraically closed field.

The successful logged fallback Loogle query Algebra.Etale has been added verbatim to mathlib_searches after reading its recorded results. The invalid-identifier Loogle query is marked unavailable, not used as negative search evidence. Existing queries and their evidence are retained. No new nodes or Mathlib leaves were introduced. All steps remain below 2000 characters; the explicit finite-equation descent, kernel and monoid-restriction computations use the cited statements rather than a hidden quotient-comparison lemma.
