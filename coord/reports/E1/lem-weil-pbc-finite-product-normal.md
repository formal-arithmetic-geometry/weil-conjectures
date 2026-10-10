# lem-weil-pbc-finite-product-normal

## Files

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-product-normal.json`: split the Stacks 0CYA proof into prime classification, localization, and normality transport; the empty product case has no primes.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-product-prime-factor.json`: statement, Mathlib leaf at `PrimeSpectrum.exists_comap_evalRingHom_eq` (`Mathlib/RingTheory/Spectrum/Prime/RingHom.lean:164`).
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-product-prime-localization.json`: statement, Mathlib leaf at `Localization.AtPrime.mapPiEvalRingHom_bijective` (`Mathlib/RingTheory/Localization/AtPrime/Basic.lean:410`).
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-normal-domain-ring-equivalence.json`: statement, Mathlib leaf using `IsIntegrallyClosed.of_equiv` (`Mathlib/RingTheory/IntegralClosure/IntegrallyClosed.lean:261`) and `MulEquiv.isDomain_iff` (`Mathlib/Algebra/Ring/Equiv.lean:970`).

## Attachments

None. Searching `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `Comparator` by item ID, proposed node IDs, and the product-normality notions found no matching declaration.

## Wanted

None. The Stacks source is available at `/home/ubuntu/c1-stacks-review/algebra.tex`.

## Source and Blueprint

The item statement agrees with Algebra Tag 0CYA, `lemma-finite-product-normal`, at lines 8260-8272. Its proof cites `lemma-disjoint-decomposition` (Tag 00EE) for product-prime classification, although Tag 00EE states the correspondence of idempotents and clopen subsets. Algebra Tag 00ED, `lemma-spec-product`, at lines 3822-3848 is the direct product-spectrum result; the split cites it. This is a source citation correction, not a change to the theorem or route. The item and the three ingredients have no `same_as` match in the imported blueprint according to `tools/blueprint_refs.py search`; the nearest ancestor is `lem-weil-pbc-normal-constant-generic`.

The Mathlib revision inspected is `v4.33.1`, the `mathlib` input revision in the read-only slopmaster2 `lake-manifest.json`; the same source is available at commit `0df444a360eaa60ab8c11dca51a86af692955474`. Its `PrimeSpectrum.exists_comap_evalRingHom_eq` at `RingHom.lean:164-187` supplies the finite-index prime classification, including the empty-index contradiction. `Localization.AtPrime.mapPiEvalRingHom` at `AtPrime/Basic.lean:405-408` is the evaluation-induced map and `mapPiEvalRingHom_bijective` at line 410 makes it an isomorphism, with no finiteness hypothesis. The node uses the finite case of that theorem to agree with Stacks 0CYA. `IsIntegrallyClosed.of_equiv` at `IntegrallyClosed.lean:261-268` and `MulEquiv.isDomain_iff` at `Algebra/Ring/Equiv.lean:970-973` give the two clauses of normal-domain preservation. Each declaration's hypotheses match the cited node after specializing the general Mathlib statements. No exact slopmaster2 declaration was found for the item or any of the three new leaves, either by blueprint tag or concept search.

## Checks

`tools/review_split.py lem-weil-pbc-finite-product-normal` passes; `tools/blueprint_refs.py check lem-weil-pbc-finite-product-normal` reports zero errors. On the fresh `sheaf-dag` tip, `tools/check_dag.py` reports zero cycles and exits 1 on seven existing reachability warnings and eleven route warnings concerning unrelated constructible nodes. No Lean was edited or built.

## Review by E1

I read Algebra Tag 0CYA, `lemma-finite-product-normal`, and Tag 00ED, `lemma-spec-product`, in `algebra.tex`, and the normality definitions at Tags 0309 and 00GV. The item has exactly 0CYA's hypothesis (each factor is normal) and conclusion (the finite product is normal). The three new node statements isolate the prime classification supplied by 00ED, the localization identity used in 0CYA's proof, and transport of the normal-domain condition across that identity. They introduce their rings, index, prime, and isomorphism explicitly; the prime-factor statement uses `def-weil-affine-spectrum` to identify prime ideals with points of the spectrum, and the localization statement uses `def-weil-pbc-localization-at-prime` for its local rings. None includes a proof in its statement or proof fields. Their source labels are the TeX labels and tags, and searches of the current DAG and imported blueprint found no duplicate node. Each is smaller than the item.

In step 1, `lem-weil-pbc-product-prime-factor` supplies exactly an index and factor prime whose coordinate comap is the given prime. Its Mathlib declaration has a finite-index hypothesis and includes the empty index: a prime of the empty product would produce an impossible index. Step 2 uses `lem-weil-pbc-product-prime-localization` for the displayed local-ring isomorphism and `def-weil-pbc-normal-ring` to obtain a normal domain on the factor side. The localization declaration is stated for any index set, so the finite case needs no extra hypothesis. Step 3 uses `lem-weil-pbc-normal-domain-ring-equivalence` to transfer both domain and integral closedness; the cited definition then gives normality of the product. The ring equivalence comes from step 2, and no proof step needs a fact hidden in a cited node's proof.

I checked the edge cases: for zero factors the product is the zero ring and has no prime; for one factor the coordinate map and its localization are identities. A zero-ring factor contributes no prime and causes no exception. The Mathlib leaves are exact statements or one-line specializations: `PrimeSpectrum.exists_comap_evalRingHom_eq`, `Localization.AtPrime.mapPiEvalRingHom_bijective` together with its map definition, and one declaration for each clause of normal-domain transport. The definition node identifies normal domains with `IsDomain` and `IsIntegrallyClosed` at each prime localization. The slopmaster2 audit of the item is `none`; no exact source declaration was found for the item or new leaves.

I corrected Mathlib line numbers in all three leaves and the worker report against the source at pinned commit `0df444a360eaa60ab8c11dca51a86af692955474` (B6). Preflight then required the `mathlib_match.line` integers, removal of new-node `merged_into` fields, and a cited definition in the prime-factor statement. I added the lines, removed those fields, and cited `def-weil-affine-spectrum`, which defines prime ideals as the points of an affine spectrum; I retained `def-weil-pbc-localization-at-prime` as the localization leaf's statement dependency (B3). No mathematical or route correction was needed. This review checks A-F: the sandbox has only this item's node files and report, the new nodes are self-contained Mathlib leaves, all non-elementary steps cite their stated inputs, and the proof is a genuine split of 0CYA.
