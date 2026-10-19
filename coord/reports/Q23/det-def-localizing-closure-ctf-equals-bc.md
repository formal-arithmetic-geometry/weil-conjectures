## Files written

- `dag/nodes/sec-proetale-coefficients/det-def-localizing-closure-ctf-equals-bc.json`: the existing statement and proof route retained, the two long proof steps separated into shorter arguments, and the item marked `split`; no new statement node was needed.
- `citations.json`: 42 verbatim statement quotations, one for every item-step/cited-node pair.

No new nodes and no Mathlib leaves were created. The item-level Mathlib searches are retained and the fresh msearch calls are recorded in `searches.jsonl`; they found only general derived-category, projective-dimension, condensed-category, and spectrum infrastructure, not this constructible l-adic Tor-amplitude theorem.

## Attachments

None. I searched both read-only project source trees for the item id, its blueprint tag, `Dctf`, `Dbc`, and constructible Tor-amplitude declarations. No sorry-free project declaration states the full item. The declarations in `WeilConjectures/SixFunctors/ProEtale/Derived/TorAmplitude.lean` define the predicates and categories but do not prove this item.

## WANTED

None for this split. The proof uses the existing DAG statement `lem-weil-l-adic-extension-integers-dvr`; its source record notes Serre's *Local Fields* as background, but no additional source is needed to state or split this item.

## Findings and changes

The item is the blueprint node `det-def-localizing-closure-ctf-equals-bc` in `main-20261015`; its statement and proof route were retained. The current shared record already contains the reviewed mathematical repairs, so I did not alter its hypotheses, coefficient categories, or conclusion. In particular, the final thickness assertion is for every qcqs scheme and finite commutative ring, while the truncation counterexample is placed on a separably closed point.

The imported blueprint proof attempted to choose a globally open stratum. That is not valid for an arbitrary finite locally closed partition: three locally closed strata can meet cyclically, so no stratum need be globally open. The retained proof replaces that with induction on the number of strata after the cited affine-local partition lemma; the selected stratum is closed in an affine open and the complement is quasi-compact. The open–closed exact sequence then detects vanishing of tensor cohomology.

## Dedicated repair handoff

I read `coord/returns/Q23.md`, entry `det-def-localizing-closure-ctf-equals-bc (dedicated repair handoff)`. It requires repairing the old 2342-character step 5 by exposing its arguments and citing existing or new nodes, keeping the statement unchanged. The initial recovered dry run passed, but its mechanical acceptance did not discharge this content repair.

Old step 5 is now two steps. Step 5 sets up simultaneous induction on the number of nonempty strata and obtains the affine neighborhood and quasi-compact complement from `lem-sf-constructible-partition-local-closed-stratum`, after applying the cited open-restriction theorem. Step 6 explains exactly why local models survive restriction: pull back the cover, use the canonical coefficient isomorphism and exact inverse-image lift from `sk-prop-sfb-cartesian-coefficients`, and preserve the finite scalar-matrix cokernel presentation of `det-def-sfb-constructible-local-model`. These are existing statements, so no duplicate auxiliary lemma is introduced. It then applies the established local-model calculation on the closed piece and the induction hypothesis on the open piece.

I also separated the old long step 10 into the explicit periodic-resolution calculation (now step 11) and the perfect-complex/truncation example (now step 12). Each uses the already cited K-flat and one-factor derived-tensor statements. All twelve steps are below 2000 characters; the largest is the unchanged finite-ring thickness step (1839). The statement, Lean records, source route, and other mathematical arguments are unchanged. Step references and citations were updated with the new numbering.

## Review by Q23

I read the item source and proof in `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-def-localizing-closure/sk-def-localizing-closure-ctf-equals-bc.md`, the chapter record, the `sk-def-localizing-closure` unit, and the complete statements of all 31 nodes named by `stmt_deps` or proof steps. I checked that the item introduces the fixed prime, algebraic closure, finite extension, valuation ring, qcqs scheme, and each coefficient ring before using them, and that the finite-ring examples introduce their own scalar ring, point, and constant sheaves.

Step 1 uses the two condensed-ring definitions to identify scalar rings, the DVR statement for the integral cases, and the Smith-normal-form statement for the finite free kernel. These give the displayed length-one free resolution; the field case is the elementary minimal-spanning-set argument. Step 2 uses exact inverse image on abelian sheaves, the stated flatness and reduction facts for constant-to-completed integral coefficients, and the finite constant local-model presentation. I checked that no unproved flatness of a completed sheaf is silently used for the field case.

Step 3 uses the definition of flat sheaf, K-flatness of bounded-above flat complexes, and the ringed-topos projection computation. The finite direct-sum tensor functor is exact by the definition, and the resulting complexes have exactly the asserted intervals. Step 4 uses weakly-etale localization to identify slice sites, exact slice restriction, the derived-tensor restriction comparison, and the sheaf-axiom argument for joint conservativity. I verified that cohomology restriction and the tensor comparison are the statements of those nodes, not facts taken from their proofs.

Step 5 prepares the corrected strata induction. The constructibility definition supplies the partition and stratum models, the partition lemma supplies an affine neighborhood where the selected stratum is closed with quasi-compact complement, and the open-restriction theorem supplies constructibility of intersected strata. Step 6 uses the exact cartesian-coefficient pullback and the local-model statement's finite scalar-matrix cokernel clause to restrict presentations. This is a direct application of exactness, finite-sum preservation, and the same scalar entries; it adds no coefficient-flatness assertion. The closed piece is affine; the open piece is quasi-compact in an affine scheme, hence qcqs, so the induction hypothesis applies with at most one fewer nonempty stratum. Step 7 uses exact coefficient pullback, the derived tensor/pullback comparison, and the ringed open–closed short exact sequence. Its two outer terms vanish after restriction, so the middle tensor cohomology sheaf vanishes. The required quasi-compact-open hypothesis comes from step 5.

Step 8 uses the concentrated-cohomology identification, the Tor-amplitude shift and extension rules, the truncation triangle, and the long exact cohomology sequence. Induction gives `[a-1,b-1]` for the lower truncation and `[b-1,b]` for the top term; the extension rule gives `[a-1,b]`. Step 9 uses the definitions of finite Tor amplitude and localizing closure: equal full subcategories have the same defining intersection for their localizing closures.

Step 10 uses the finite-ring pro-étale/étale constructibility equivalence, exact classical-sheaf equivalence, weak Serre closure of classical sheaves, étale constructible Serre theorem, bounded-constructible triangulated-subcategory proposition, and the thick finite-Tor intersection from the Tor-amplitude definition. These statements establish kernels, cokernels, extensions and retracts for every qcqs `X`, without regularity of the finite ring. Step 11 uses exact constant-sheaf pullback, K-flatness of bounded-above flat complexes, the one-factor tensor computation, and the finite local-model presentation. The periodic free resolution has nonzero Tor in every nonnegative degree. Step 12 uses the perfect-complex definition, K-flatness, and the Tor-amplitude shift rule: the two-term finite-free complex is perfect, but its cohomology modules cannot be perfect since tensoring a bounded projective complex gives bounded cohomology. The same argument on every nonempty covering member rules out local perfectness. Thus the standard truncations leave the finite-Tor subcategory.

I checked edge cases explicitly: zero module and rank zero in the scalar resolution, empty strata and zero complexes in the induction, a one-stratum whole-space partition, zero/empty open or closed pieces in the open–closed sequence, vanishing extreme cohomology in the truncation induction, coefficient stage `n=1`, and the point example with `A=Z/ell^2`. Every entry of `citations.json` is copied verbatim from the corresponding cited node statement, and `proof_deps` is exactly the union of the twelve steps' `uses` lists. No Lean file, compiler, Lake/build command, live project, or launcher state was written.

## Unfinished work

None for this one-level stage-1 split.

The item is a detail of unit `sk-def-localizing-closure`; its key definition is the distinct node `sk-def-localizing-closure`. No unit realization file is delivered. The temporary sandbox-only realization copy was removed before preflight.
