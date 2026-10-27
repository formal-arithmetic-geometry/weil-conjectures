# Q66: lem-trf-flattening-ambient-module-preparation

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-flattening-ambient-module-preparation.json`: existing statement, now split into seven steps; statement and statement dependencies unchanged. Mathlib searches find component facts, not the entire assertion.
- `citations.json`: one entry for every step-node citation, copied verbatim from the actual cited statement (29 entries).
- `searches.jsonl`: the search command's actual log; five new searches, including a second semantic phrasing. The original five search records of the item are retained.
- No new nodes or Mathlib leaves. `prepare.py` is a sandbox-only preparation script, not a delivery file.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint id and for flattening, ambient-module and affine-immersion notions. The project has the closed affine-space immersion existence theorem, but that does not supply the module assertions or the full item. In particular, `AlgebraicGeometry.exists_immersion_affineSpace_of_quasiAffine` at `WeilConjectures/Mathlib/AlgebraicGeometry/AffineSpace.lean:396` covers only the immersion input, not an attachment for this item.

## WANTED

None. All sources used are present locally.

## Problems and corrections

The item's statement is correct without adding quasi-separatedness of `g`. Its parent needs that extra hypothesis later for gluing strict transforms, but the present preparation does not. I retained the exact statement. There is no repair note for this item and no previous sandbox split or report to supersede.

The source Stacks 081R leaves verification of the module-flattening hypotheses implicit. This split supplies it. Instead of choosing arbitrary affine source pieces and invoking 04II to obtain an immersion, choose pieces above affine base opens and embed them by a chosen finite list of algebra generators. This is the explicit affine-coordinate version of the same ambient-module reduction. It changes neither the unit route nor the item. In fact the ambient opens can be affine. No appeal to an arbitrary immersion admitting an unexplained quasi-compact neighbourhood is needed.

A quotient ring is always a finite module but need not be finitely presented as a module. Accordingly step 4 proves only finite type. Steps 5 and 6 use the good-open finite-presentation hypothesis and the existing kernel-finiteness lemma, with zero polynomial variables, before asserting a finite module presentation. Off the closed support the stalk is zero; it must not be identified with a source stalk that does not exist.

## Blueprint and duplicate searches

Read `dag/chapters/sec-trace-formula.json`, `dag/units/sk-i-curve-zero.json` and the item's current blueprint ancestry. The item is a descendant input to the local-term locality semistable-alteration branch, specifically the Stacks 081R ambient preparation preceding module flattening. It is not the unit's key node, so no unit record is changed.

Ran `tools/blueprint_refs.py ancestor lem-trf-flattening-ambient-module-preparation` and whole-blueprint searches for `quasi-affine`, `finite presentation`, `closed immersion`, `closed immersion finite presentation`, `quasi-compact open`, `open immersion`, `ambient module`, and `flattening`. Also searched all DAG nodes by tags 02FV, 04II, 081R and by closed-immersion, finite-presentation, finite-type, affine-pushforward, and quasi-compactness notions. Read the actual candidate statements. Existing nodes cover every necessary input. No blueprint node states this whole preparation; `same_as` remains empty.

## Not duplicates

No new nodes. In particular I reuse `lem-a1-map-over-base-finite-presentation` (02FV), `lem-weil-pbc-finite-presentation-surjection-kernel-fg`, `lem-weil-pbc-quasi-coherent-finite-type-affine`, the affine-structure-algebra theorem, and the existing closed-subspace stalk calculation instead of creating their special cases. The affine-immersion existence theorem 04II was also read; the explicit generator construction in step 2 needs only the existing definitions.

## Mathlib searches

The new log contains leanfinder queries in two different phrasings, a Loogle pattern with `AlgebraicGeometry.IsClosedImmersion, AlgebraicGeometry.LocallyOfFinitePresentation`, the recorded grep regex for affine-space immersions and finite-presentation pushforwards in `AlgebraicGeometry`, and a LeanSearch query. Every service answered successfully. Read all hits: finite morphism coordinate finiteness, affine covers, local finite presentation of affine space, closed immersion affine/quotient descriptions, and quasi-affine immersion facts are components only. No hit states the conjunction of this item. Read the grep source `Mathlib/AlgebraicGeometry/QuasiAffine.lean:40-60`. Also read `Mathlib/RingTheory/FinitePresentation.lean:298-299` to verify the existing kernel-finiteness node's declaration, including the allowed case of zero variables. No invented or unavailable search is recorded as a successful absence result.

## Review by Q66

I read the item source in `literature/stacks-project/flat.tex`, Tag 081R `lemma-flat-after-blowing-up`, both the finite-affine-cover paragraph and the ambient-immersion/module paragraph. I read `morphisms.tex` `lemma-quasi-affine-finite-type-over-S` (04II), 02FV `lemma-finite-presentation-permanence`, 01TQ `lemma-locally-finite-presentation-characterize`, 01TV `lemma-closed-immersion-finite-presentation`, 01S7 `lemma-affine-separated`, 01S8 `lemma-characterize-affine`, 01SA `lemma-affine-equivalence-algebras`, and 02GP `lemma-open-immersion-etale`. I read `algebra.tex` `lemma-compose-finite-type` and `lemma-finite-presentation-independent`; `properties.tex` 01PB and 01PC; and `sheaves.tex` 00AE `lemma-stalks-closed-pushforward`. No new-node source review is required because no new nodes are created.

For step 1 I opened the finite-affine-cover node, which requires only a quasi-compact scheme and gives a finite affine cover, and the finite-type definition, which explicitly supplies finite affine covers with finitely generated coordinate algebras over each affine base open. T satisfies the former hypothesis and g the latter. The resulting W_i cover W without assuming that W is quasi-separated.

For step 2 I opened the spectrum, relative-affine-space and closed-immersion definitions and the affine-scheme qcqs theorem. They supply the contravariant spectrum morphism, the polynomial chart over the selected base open, the quotient criterion for a closed immersion, and quasi-compactness of the affine ambient. Sending each coordinate to its selected generator is explicitly a surjection. This is a routine construction, not an unproved new immersion-existence lemma. Its dimensions are finite by the finite-type hypothesis.

For step 3 I opened the affine-space smoothness statement, the smoothness definition, open-immersion etaleness and the etale definition, composition of locally finitely presented maps, and qcqs permanence. The first four give local finite presentation of each factor; composition gives that of p_i. Permanence applies because V_i is affine, hence quasi-compact, and the target T is quasi-separated. No separatedness of g is used.

For step 4 I opened the affine relative-spectrum theorem, whose clause (1) explicitly says the pushed structure algebra is quasi-coherent. A closed immersion is affine by the cited closed-immersion definition. Its same affine quotient description gives sections R/I. This is cyclic, and the cited affine-module criterion (a) is exactly the implication from finite generation of sections to finite type of a quasi-coherent sheaf. I do not infer coherence or finite presentation from cyclicity.

For step 5 I opened qcqs permanence (3), which includes local finite presentation under arbitrary base change, the open-immersion theorem and etale definition, composition, and the actual 02FV node. The source W_i,U is an open in W_U; composing this locally finitely presented open inclusion with the assumed W_U→U gives local finite presentation of W_i,U→U. The target V_i,U is locally finitely presented over U, hence locally finite type by its finite algebra presentations. These are precisely 02FV's two hypotheses. The restricted closed immersion is a restriction to an open in the ambient, so its affine quotient description is unchanged.

For step 6 I checked clause (4) of the affine structure-algebra theorem: it explicitly identifies restriction of a pushed structure sheaf to an open with pushforward from its inverse image. The closed-immersion definition gives affine inverse images and the quotient R/I. The affine-opens local-finite-presentation node then applies to both affine opens, not to a non-affine inverse image. The kernel-finiteness node says every polynomial presentation has finitely generated kernel; n=0 is permitted and identifies the polynomial ring with R. If I has m generators, the displayed row map R^m→R has image I, so its cokernel is R/I. The affine sheaf criterion (b) states exactly that finite module presentation is equivalent to finite presentation of the quasi-coherent sheaf on that affine open.

For step 7 I opened the closed-subspace additive-sheaf stalk node. It gives the zero stalk off the image and the germ isomorphism on the image. Its statement is additive, so I separately wrote why this germ identification respects base-ring scalars: both actions multiply by the same pullback germ. This is checked on representatives and needs no extra module comparison lemma. The flat-morphism definition says exactly that the resulting source local ring is flat over the base local ring. The module-flat-over definition explicitly includes the equivalent stalk criterion used to conclude. Only the given flatness over U is used, with no attempted flatness extension outside U.

I tested W empty (empty cover), U empty (all good-open assertions vacuous), U=T, n_i=0 (surjective coefficient map and zero-variable kernel theorem), empty inverse images of affine opens (R/I=0 is allowed), and the zero ring. If I=0 the relation module has zero generators; if I=R the quotient is zero and is finitely presented. Bases need not be Noetherian and W need not be quasi-separated. No step exceeds 2000 characters; each assembly step has its actual dependencies and no hidden long lemma. All citation quotes are literal statements of the cited nodes, not their proofs. I checked B1–B10, C1–C8, D1–D5 and E1–E7 against the files: no new-node duplicates, no restated clause nodes, no tag-only non-elementary inputs, no unsupported hypothesis, and no alteration of the unit route.

The split_report declares five generic off-unit tools: open inclusions are etale, local finite presentation composes, 02FV permanence, affine pushed structure algebras with restriction, and the closed-subspace stalk formula. Each is used as its stated general tool; no alternative flattening theorem is substituted. Definitions, Mathlib leaves and closed nodes need no route exception.

## Unfinished work

None within this stage-1 item. Existing cited nodes retain their own independent status. No Lean was written and no compiler, Lake or build command was run.
