# Stage-1 report: det-sp-reduction-compatibilities

## Files written

- `dag/nodes/sec-smooth-purity/det-sp-reduction-compatibilities.json`: existing item copied from the repository, with its eight-step proof retained and status set to `split`; no new nodes.
- `citations.json`: 25 per-step citations, one for every node used by every proof step.

## Attachments

None. A search of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` found no declaration tagged `(blueprint: det-sp-reduction-compatibilities)` and no declaration stating the three clauses. The item remains a natural-language DAG statement.

## WANTED

None.

## What was wrong or changed

The repository copy was already a detailed split and had passed an earlier review, but it was still marked `unsplit` and lacked the delivery citation ledger in this sandbox. I changed only the status and added `citations.json`; the statement, dependencies, proof, blueprint metadata, mathlib search log, import flags, and existing review record are retained. No statement dispute was found. The proof uses no SGA source.

## Review by Q68

I read the item statement, the unit `sk-lem-sp-reduction`, the smooth-purity chapter record, and the current main-20261015 blueprint statement and proof. I searched the complete Lean source for the item id, its blueprint tag, and the coefficient-comparison terminology; no exact project declaration exists, so this is not an attachment. I also checked the old blueprint proof against the current eight steps and retained its route through the direct-image comparison, counit-defined exceptional comparison, ringed-topos tensor/exchange coherence, finite-ring constructible-origin comparison, and general-ring purity orientation.

For step 1 I checked the cited statements of `det-sp-scalar-extension-functor`, `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, and `lem-weil-pbc-finite-ring-constructible-derived-origin`: they provide preservation of the finite-Tor constructible domain, locally free Tate-line scalar extension and associators, the derived tensor/pullback isomorphism, and bounded etale origin. The step's identity-topos application and sign/associator discussion use exactly those statements and does not assume flatness. Step 2 uses the counit characterization in `det-sp-reduction-exceptional` and the naturality and cocycle data in `det-sp-reduction-direct-image`; I checked that the transpose calculation has the required domains and that the triangle identity is the only additional elementary adjunction identity. Step 3 uses the same two comparison statements and the scalar associator from `det-sp-scalar-extension-functor`; the displayed four-factor transpose is the direct expansion of those cited counit and cocycle identities.

For step 4 I read `det-sp-reduction-direct-image`, `lem-weil-pbc-ringed-exchange-tensor-coherence`, and `lem-cbc-extension-zero-projection-formula`. The proper square has the stated ringed-topos commutation, while the open part is exactly the extension-by-zero projection formula; the K-flat balancing check accounts for coefficient compatibility. For step 5 I checked every cited statement: `det-sp-finite-general-ring` supplies the shifted dualizing line and tensor-map setup; `lem-weil-pbc-finite-ring-constructible-derived-origin`, `det-ctf-finite-comparison-whole`, and `det-ctf-finite-comparison-localizing` supply the etale witnesses and transport of proper/open operations; `lem-weil-pbc-comparison-pullback` supplies the pullback square; `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` and `lem-weil-pbc-ringed-exchange-tensor-coherence` give the canonical tensor/exchange maps; and `lem-etale-proper-projection-formula-finite` plus `lem-cbc-extension-zero-projection-formula` give invertibility of the compactification projection. The hypotheses (finite admissible rings, separated finite-type schemes, compactification, constructibility and finite Tor amplitude) are verified in the item setting. Steps 4 and 5 exceed 2000 characters; I checked them for hidden independent lemmas and found each subclaim is either one of these cited statements or the displayed K-flat/adjunction calculation, so no additional node is warranted.

For step 6 I checked that the two displayed transposes use precisely the counit equation of `det-sp-reduction-exceptional` and naturality/cocycle of `det-sp-reduction-direct-image`. Step 7 uses clauses (1)–(2) of `det-sp-finite-general-ring` and the locally free/associative scalar-extension clauses of `det-sp-scalar-extension-functor`; the common exponent construction avoids any unsupported uniqueness claim. Step 8 is the direct substitution into clause (3) of `det-sp-finite-general-ring`, with the source identification already supplied by step 1. I verified the 25 entries of `citations.json` byte-for-byte as substrings of the cited node statements and checked that their nodes are exactly the `uses` of steps 1–8 and that `proof_deps` is their union.

I checked small cases in the statement and proof route: (d=0), (f=\mathrm{id}), (M=0) or (K=0), (A=B=C), identity coefficient maps, (n=m) in the common-prime-power construction, empty schemes, and nonflat quotient maps. These reduce respectively to identity adjunctions, zero morphisms, scalar unitors, or the stated associativity and counit identities. No hypothesis is silently added or dropped.

## Remaining work

No unfinished split work remains. The required next action is the prescribed delivery dry run.
