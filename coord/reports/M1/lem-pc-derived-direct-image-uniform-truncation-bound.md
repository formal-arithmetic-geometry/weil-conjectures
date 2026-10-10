# Stage-1 split: lem-pc-derived-direct-image-uniform-truncation-bound

1. Files written: `dag/nodes/sec-picard-framework/lem-pc-derived-direct-image-uniform-truncation-bound.json` (split); `dag/nodes/sec-picard-framework/lem-pc-unbounded-derived-functor-cohomological-bound.json` (statement, Mathlib no match); `dag/nodes/sec-picard-framework/lem-pc-derived-sections-pushforward-comparison.json` (statement, Mathlib no match); `citations.json`.
2. Attachments: none. A search of the project declarations under `WeilConjectures/` and `Comparator/` found no exact sorry-free declaration for the item or either new statement.
3. WANTED: `literature/stacks-project/perfect.tex`, Tags 08D5 and 08D4, for the item and both new nodes. This checkout contains the citation metadata but no Stacks source tree. I read the published Stacks pages for 08D5, 08D4, 01XJ and 01XK and wrote the proof as agent work under the local-source rule.
4. The imported item had no proof. Its statement agrees with Tag 08D5(2), apart from choosing a positive integer (increase the source's integer to at least 1), and its final truncation consequence is the last paragraph of that proof. Its inherited blueprint path reaches the first-step duality comparison through the derived-direct-sum lemma; the blueprint has no direct statement of this truncation input. The imported Mathlib records were replaced by current logged searches in the new nodes; the item itself was searched afresh with LeanFinder, Loogle, grep and LeanSearch (unavailable). No statement correction was needed.
5. Unfinished: no proof is requested for the new statement-only nodes at this stage. The missing local Stacks source is recorded above.

## Not duplicates

lem-pc-unbounded-derived-functor-cohomological-bound vs lem-sc-qcoh-acyclic-derived-pushforward-cohomology: the existing node assumes vanishing of every positive higher direct image and concludes an equality for `Rf_*`; the new node is Tag 08D4's arbitrary product-preserving additive functor with any finite cohomological bound and gives an upper vanishing bound.

lem-pc-derived-sections-pushforward-comparison vs lem-pc-cohomology-sections-affine-base: the latter compares ordinary cohomology of one quasi-coherent sheaf with sections of its higher direct image under a separated map to an affine base; the new node compares derived global sections of an arbitrary complex with the derived global sections of its derived pushforward on any open base.

lem-pc-unbounded-derived-functor-cohomological-bound vs lem-pc-finite-support-hi: the existing node bounds `R^pf_*` on individual quasi-coherent modules; the new node transfers such a bound to the right derived functor on an arbitrary unbounded complex with quasi-coherent cohomology.

lem-pc-derived-sections-pushforward-comparison vs lem-weil-pbc-cohomology-pullback-derived-unit: the existing node concerns etale abelian sheaves and a pullback map; this node concerns Zariski sheaves of modules and the composite `RΓ ∘ Rf_*`.

lem-pc-derived-sections-pushforward-comparison vs lem-pc-derived-direct-image-preserves-qcoh: the existing node says qcqs pushforward preserves quasi-coherent cohomology; the new node identifies derived global sections before and after any derived pushforward, without a qcqs hypothesis.

lem-pc-derived-sections-pushforward-comparison vs lem-sc-qcoh-acyclic-derived-pushforward-cohomology: the existing node computes each cohomology sheaf of derived pushforward under vanishing higher direct images; the new node compares derived global sections without any such vanishing.

## Review by M1

I read the item against the published Tag 08D5, especially its clause (2), its invocation of Tag 01XJ, the use of Tag 08D4 on `Γ(f⁻¹U,-)`, and its final truncation triangle. I read Tag 08D4(3) for the first new statement: the product hypothesis, the vanishing of `R^pF` for `p≥N` on quasi-coherent modules, and the upper support conclusion match one by one. I read the displayed derived-sections identity in Tag 08D5 for the second new statement. Both statements introduce their schemes, functors, categories and bounds, and neither contains proof steps. The Mathlib log records two phrasings where needed; LeanFinder returned only generic derived-category or underived pushforward declarations, Loogle and grep gave no match, and LeanSearch returned HTTP 500. Searches by tag and concept across all DAG nodes and the blueprint yielded the existing nodes named below, rather than a duplicate of either new statement.

Step 1 uses exactly the uniform integer, base-change clause and quasi-coherence in `lem-pc-finite-support-hi` (01XJ). Increasing it to `max(1,n₀)` preserves the conclusion. Step 2 uses that same node on the open base change, `lem-pc-affine-vanishing` on the affine target, and clause (2) of `lem-pc-leray-degenerate-sections` to identify source cohomology with sections of higher direct images. `pqf-def-cohomology` identifies these groups as derived sections. The product argument is the two-line product universal property, not an additional theorem. The qcqs condition survives restriction and base change by the hypotheses of 01XJ.

Step 3 uses the precise upper-bound conclusion of the new 08D4 node with `b=0`, then the precise derived-sections isomorphism of the second new node. The final sheaf vanishing is checked on an affine basis using cohomology of a K-injective representative. I checked that this argument does not assume quasi-coherence of `Rf_*E`, which Tag 08D5 proves later. Step 4 uses the truncation triangle named by `def-sbc-standard-tstructure-derived-category` and the derived functor of `def-pc-derived-direct-image`; the index calculation is explicit: `H^j(Rf_*T)=0` for `j+n+1≥N`, so `n≥N-q` suffices for the two terms adjacent to the desired map. The test cases `E=0`, affine `f` with `N=1`, and `q=0` with `n=N` satisfy the same inequalities. I corrected the initially overbroad derived-sections node by removing an affine quasi-coherence consequence that would have depended on the separate Tag 08D5(1) proof; only the independent derived-sections comparison remains.

## Second reading by M1

- Item statement: checked against Stacks Tag 08D5(2) and its final truncation argument; hypotheses and the positive bound agree, including the zero, affine, and degree-zero cases; verdict pass.
- Step 1: checked against Tag 01XJ and `lem-pc-finite-support-hi`; base-change uniformity and `max(1,n_0)` are valid; verdict pass.
- Step 2: checked against Tags 01XJ, 01XK, 08D4 and the existing Leray node; affine higher cohomology, product preservation, and the derived-sections definition are cited; verdict pass after replacing the duplicate definition citation.
- Step 3: checked against Tag 08D5's affine-open argument and both statement-only nodes; the restriction computation is explicitly supported by `lem-sc-derived-k-injective-restrict-open`; verdict pass.
- Step 4: checked against Tag 08D5's truncation triangle and Tag 08D4's index bound; the shift calculation gives both adjacent vanishings for `n >= N-q`; verdict pass.
- `lem-pc-unbounded-derived-functor-cohomological-bound`: checked clause by clause against Tag 08D4(1)-(2), including countable products and `N >= 0`; verdict pass, no Mathlib match.
- `lem-pc-derived-sections-pushforward-comparison`: checked against the displayed identity in Tag 08D5; schemes, open restriction, and derived functors are self-contained; verdict pass, no Mathlib match.

Changes made: corrected the item's `created.item` metadata; replaced the duplicate `def-sc-sheaf-cohomology-functor` dependency with existing `pqf-def-cohomology`; added the K-injective restriction node to Step 3 and its citation; updated the tool-use explanation accordingly. No statement or source was changed.
