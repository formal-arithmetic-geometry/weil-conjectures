# Worker report: lem-sfb-exceptional-curve-count

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-exceptional-curve-count.json`: statement, split into nine proof steps; no Mathlib match.
- `citations.json`: one verbatim statement quotation for each node used by each proof step.
- `searches.jsonl`: five searches actually run through msearch.py; the item's inherited Q40 searches are also retained in its JSON.

No new nodes and no new Mathlib leaves. The statement is unchanged. No unit/chapter file, repository file, Lean file or launcher file was written, and no compiler, Lake or build was run.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag and for exceptional curves and contracted curves. The only exceptional-curve textual hit was the unrelated ambient-adjoint elliptic-curve counterexample. There is no project declaration stating this item to attach.

## WANTED

None. The necessary Stacks sources are present.

## What was wrong or missing

The item was statement-only. Its parent correctly deferred the omitted induction measure in Stacks 0C5R to this node; I supplied the omitted finiteness, zero-measure base case and strict-decrease arguments. There is no statement dispute or change to a target, unit, chapter or proof route.

Two pre-existing source-reference issues are reported rather than edited. In 0C5R's first proof paragraph, “V contains all codimension 1 points of V” has the evident intended target Y: 0BFP supplies exactly that assertion for the regular target. Also `lem-sc-regular-dim1-dvr` states the correct theorem but its inherited external tag 00DV is Nakayama, not the DVR theorem. I read algebra.tex Tag 00PD, `lemma-characterize-dvr`, equivalence (3) with (1), and cite that correct place in the item's step source. The existing lemma's statement, not the incorrect tag, is what step 1 uses.

The item's inherited blueprint ancestor is null, as `blueprint_refs.py ancestor` confirms. Its detailed inherited `from.place` and `via` chain are retained; `split_report.blueprint` identifies the local 0C5R paragraph being realized. The item is not the key statement of its distant unit and no realized fields are changed.

## Searches and reuse

I searched the entire DAG for 0BFP, 0C5R, 0AGQ, 0AGR, exceptional projective lines, finite irreducible components of closed subsets, zero-dimensional finiteness, local-ring dimension chains and blowup flat base change. I opened the statements of the cited nodes. Whole-blueprint searches for `exceptional curve`, `contracted`, `0BFP` and `finite exceptional` produced no equivalent statement; the unrelated coefficient, torsor and purity hits do not count curves of birational surface maps. Thus `same_as` remains empty.

The fresh Mathlib searches used LeanFinder with both the contracted-curves phrasing and the exceptional-locus/components phrasing; Loogle with `AlgebraicGeometry.Scheme.Birational, AlgebraicGeometry.IsProper`; LeanSearch with the no-contracted-curves isomorphism criterion; and grep of AlgebraicGeometry for `exceptional.*curve|contract.*curve|birational.*surface|surface.*birational`. I read the returned signatures: normalization dominance, rational-map representatives and function-field maps, properness constructors/permanence, and the flat-surjective-monomorphism isomorphism theorem. None proves the surface criterion under this item's hypotheses; flatness and being a monomorphism are not assumptions here. Loogle and grep returned no hits. Every fresh search is recorded from its actual log entry. No service failure was reported.

## Not duplicates

No new nodes. In particular I did not create duplicate nodes for 0BFP, local surface blowup geometry, scheme sobriety, finite components of a closed subset, or dimension by generalization chains. The excellent/ample global surface-blowup node `lem-per-surface-point-blowup-geometry` is not applicable without extra hypotheses; instead I use the existing local regular-ring theorem and the existing flat localization comparison. No excellence, ample line bundle, finite-type-over-a-field, catenarity or algebraically closed residue field is assumed.

## Review by Q82

I read resolve.tex Tag 0C5R, `lemma-proper-birational-regular-surfaces`, especially the complete first proof paragraph ending “Some details omitted”. I also read varieties.tex Tag 0BFP, `lemma-modification-normal-iso-over-codimension-1`, including its four clauses and proofs; resolve.tex Tags 0AGQ/0AGR, `lemma-blowup` and `lemma-blowup-regular`; divisors.tex Tag 0805, `lemma-flat-base-change-blowing-up`; properties.tex Tags 02IZ/0BA8, `lemma-codimension-local-ring` and `lemma-Noetherian-irreducible-components`; schemes.tex Tag 01IS, `lemma-scheme-sober`; and algebra.tex Tag 00PD, `lemma-characterize-dvr`. There are no new-node sources to certify.

1. Step 1 checks all hypotheses of `lem-sfb-normal-modification-codimension-one`. Integrality supplies a reduced source and unique generic points; the dense-open isomorphism really identifies the local rings at those generic points, which is the cited node's notion of birationality. The target is Noetherian by hypothesis. `def-weil-regular-scheme` and the exact one-dimensional local-algebra statement `lem-sc-regular-dim1-dvr` discharge the DVR condition in clause (2), not just normality. `rem-pc-regular-normal` supplies normal local rings separately for later clause (3). `lem-sc-scheme-stalk-dimension-generalization-chains` supplies the actual comparison with local dimension; this is not inferred merely from a dimension definition. The topological chain bound then forces bad points to have local dimension exactly two.

2. Step 2 uses that same chain comparison to exclude a strict specialization of a bad point: prefixing it to a length-two chain would give length three. `lem-sc-scheme-sober` prevents distinct points with the same closure. Only after all points of the closed bad set are proved closed do I invoke `lem-sc-noetherian-closed-points-finite`. Its statement is exactly finiteness under these hypotheses, rather than merely finite components.

3. Step 3 invokes the statement of `lem-sc-noetherian-closed-subset-finite-components` on the closed set Z inside the given Noetherian X. It does not assume a new scheme structure on Z or finiteness of all fibres. The dimension estimate is written as an appended-chain argument using `def-kun-topological-krull-dimension`. Each component's image is one point because it is irreducible inside a finite set of closed points; that argument is included explicitly.

4. Step 4 is elementary from the preceding component cover and chain bound: a contracted curve cannot meet the isomorphism locus, lies in one component, and must equal that component since otherwise a chain of length three results. It proves, rather than assumes, that B(f) is a finite subcollection of components. No new node restates that clause.

5. Step 5 uses the unique generic point supplied by `lem-sc-scheme-sober` to prove that a zero-dimensional irreducible component is a singleton. A finite union of them makes Z finite. Only then does it apply the finite-fibre normal-target clause (3) of `lem-sfb-normal-modification-codimension-one`, with normality already established in step 1. This proves that the entire bad locus is empty, and hence the zero-curve base case. The reverse implication is the singleton-fibre observation.

6. Step 6 is the elementary set inclusion B(g) subset B(f) from f = b g. It neither compares dimensions on different surfaces nor assumes a bijection of exceptional components.

7. Step 7 checks dimension two and regular locality for A before applying `lem-sfb-local-surface-maximal-blowup-geometry`. `lem-weil-pbc-spec-local-ring-canonical-morphism` explicitly supplies flatness, and the closed-point local map is the identity. `def-nagata-blowup-flat-base-change-map` introduces the actual comparison whose invertibility is stated by `thm-nagata-blowup-flat-base-change`; the definition is not being cited as a theorem. Fibre-product associativity then identifies the special fibre with b's fibre at y, and `def-pc-scheme-fibre` explicitly states the homeomorphism to the underlying inverse-image subset. This avoids the excellent/ample hypotheses of the other global blowup node.

8. Step 8 checks the projective-line facts directly from `def-sc-p1-standard`'s two polynomial charts and their nonempty Laurent-polynomial overlap. Their domain coordinate rings give irreducibility through `def-pc-integral-scheme`; (0) and (t) give distinct points over any field, including finite and imperfect fields. `lem-sfb-regular-point-blowup-geometry` states the complement isomorphism needed for b's birationality. The exceptional fibre is a proper closed subset, not the whole target.

9. Step 9 uses properness only through the closed-map property stated by `def-weil-proper-morphism`. Birationality makes g's image dense and therefore surjective. Apply the exact finite-component-cover statement to F, not to a non-Noetherian base change. The closed images cover the irreducible E, so at least one equals E. Its component has dimension at most one by the previous chain argument and cannot be zero-dimensional by the sober-space singleton argument. This gives a specific member of B(f) outside B(g). It proves only the strict decrease required here; it does not hide the stronger assertion that a component maps isomorphically onto E.

All proof citations have their own entries in citations.json, using the full verbatim statement so that no missing hypothesis or clause is concealed by an abbreviated quotation. `proof_deps` is exactly the union of the uses lists. The off-unit local-algebra, normality, finiteness and flat-base-change tools are declared in `split_report.tool_uses`; they are generic inputs rather than replacements of a unit's proof step.

For edge cases I checked f an isomorphism (empty S and Z, t = 0, B(f) empty, and no y to which the final clause applies); a single point blowup with g the identity (E supplies the lost curve); several bad points (finite closed-point image argument still works); potential zero-dimensional fibre components (handled in the base case, not miscounted as curves); nonclosed codimension-one points; finite or imperfect residue fields; and regular surfaces not assumed excellent or quasi-projective. All arguments use global dimension only as a bound on chains, without a dimension-additivity or catenarity assumption. No proof step exceeds 2000 characters and none packages a hidden independent comparison or source “standard” claim as an uncited lemma. B1-B10 are met without introducing any new node; C1-C8, D1-D5 and E1-E7 were checked against the actual statements above. The main repair during this check was to use the existing generalization-chain theorem explicitly rather than leaving the passage from local dimension to closed bad points implicit, and to use the closed-image component argument instead of assuming an isomorphism onto E.

## What remains unfinished

Nothing in the requested stage-1 split. The existing cited nodes keep their own statuses. This delivery does not claim their Lean proofs are complete.

## Validation

The required server dry run exited successfully: `OK (not pushed) deliver/Q82/lem-sfb-exceptional-curve-count at a2c9ea18f6e: preflight passed`. The complete preflight includes the server DAG and split checks. This final report records that result; the delivery is checked once more after this report-only update, before pushing.
