# Stage-1 report: lem-trf-constructible-etale-ext-continuity

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-constructible-etale-ext-continuity.json` — repaired split; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-constructible-etale-finite-affine-syzygy.json` — statement-only syzygy node; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-constructible-etale-ext-mono-four-lemma.json` — corrected Mathlib leaf, `CategoryTheory.Abelian.mono_of_epi_of_mono_of_mono`.
- `citations.json` — verbatim quotes for every cited node in every step.

Attachments: none. No sorry-free project declaration states the item.

WANTED: none.

The returned version had three mathematical defects. The new four-lemma node had the vertical maps in the wrong positions: Mathlib's `mono_of_epi_of_mono_of_mono` says that alpha epi together with beta and delta mono implies gamma mono. I corrected that statement and checked the counterexample from the return (top row $\mathbb Z\xrightarrow{-1}\mathbb Z\to0\to0$, bottom row $\mathbb Z\to0\to0\to0$) against the old shape. Step 4 now uses the shifted Ext segment for the mono pass and the unshifted segment for the epi pass. It states a finite triangular induction: for a resolution through $K_{n+1}$, (M$_d$) is monomorphism for $K_r$ with $r\le n+1-d$, while (I$_d$) is isomorphism for $K_r$ with $r\le n-d$; the two four-lemma passes establish the next pair. Step 3 now gives the requested full-faithfulness argument: adjunction identifies maps out of a finite free presentation with a kernel of two Hom groups, stage-section colimits descend the finitely many sections, and eventual hom-lift plus the same kernel calculation gives both existence and eventual equality.

## Not duplicates

- `lem-trf-constructible-etale-finite-affine-syzygy` vs `lem-weil-pbc-constructible-module-finite-zero-cokernel`: one finite affine-free epimorphism versus its iterated kernel resolution.
- `lem-trf-constructible-etale-finite-affine-syzygy` vs `thm-constructible-serre`: closure under kernels versus the constructed affine-free resolution.
- `lem-trf-constructible-etale-ext-mono-four-lemma` vs `lem-pc-four-lemma-epi`: injectivity four lemma versus surjectivity four lemma.
- `lem-trf-constructible-etale-ext-continuity` vs `lem-weil-pbc-limit-pullback-sections-colimit`: Ext-group continuity versus degree-zero sections continuity used in Hom descent.
- `lem-trf-constructible-etale-finite-affine-syzygy` vs `lem-v2-constructible-prime-field-filtration`: the existing node concerns a prime-field filtration, while this node constructs arbitrary finite affine-free resolutions over a finite ring.
- `lem-trf-constructible-etale-finite-affine-syzygy` vs `lem-weil-pbc-constructible-module-finite-presentation`: the existing node gives one finite presentation, while this node iterates kernels to every prescribed length.
- `lem-trf-constructible-etale-finite-affine-syzygy` vs `lem-weil-pbc-constructible-stratification-intersection`: the existing node concerns intersections of constructible strata, not resolutions.
- `lem-trf-constructible-etale-finite-affine-syzygy` vs `lem-weil-pbc-module-sheaf-colimit-constructible-data`: the existing node concerns filtered-colimit data, not affine-free syzygies.
- `lem-trf-constructible-etale-finite-affine-syzygy` vs `lem-sfb-discrete-noetherian-constructible-serre`: the existing node is a discrete-Noetherian Serre closure statement, not a finite affine-free resolution.
- `lem-trf-constructible-etale-finite-affine-syzygy` vs `lem-kun-03sa`: the existing node states a different constructibility result and does not introduce the iterated affine-free kernels.
- `lem-trf-constructible-etale-finite-affine-syzygy` vs `lem-weil-pbc-constant-subsheaf-generic`: the existing node concerns generic constant subsheaves, not resolutions.
- `lem-trf-constructible-etale-finite-affine-syzygy` vs `lem-weil-pbc-constructible-subobjects-noetherian`: the existing node concerns constructible subobjects, not finite affine-free terms and exact sequences.
- `lem-trf-constructible-etale-finite-affine-syzygy` vs `lem-weil-pbc-affine-free-etale-family-models`: the existing node models a fixed finite family across stages; this node iterates finite epimorphisms and kernels on one scheme.
- `lem-trf-constructible-etale-finite-affine-syzygy` vs `lem-weil-pbc-affine-free-etale-module-arrow-descent`: the existing node descends one arrow between free families, not an arbitrary-length resolution.
- `lem-trf-constructible-etale-finite-affine-syzygy` vs `lem-weil-pbc-affine-free-finite-stalk-generation`: the existing node gives finite stalk generation, not an exact free resolution.

## Review by Q29

I reread the item against Stacks Tags 09YU (the constructible-module colimit/full-faithfulness lemma) and 0GIT (cohomology of filtered-colimit complexes), and reread the Mathlib source `CategoryTheory/Abelian/DiagramLemmas/Four.lean` lines 89–94. The item hypotheses are unchanged: the index is small directed and nonempty, all schemes are qcqs Noetherian with affine transitions, the coefficient ring is finite, and both sheaves are constructible. The syzygy node states exactly the finite affine-free presentation and constructible kernel closure supplied by Tags 095N and 03RZ. The mono leaf now matches the Mathlib theorem's component order exactly; its eight recorded searches include the corrected query and the direct source check.

Step 1 uses the syzygy statement for the recursively defined $K_r$ and exact sequence, and inverse-image exactness for transport. I checked that the syzygy node really defines $K_0$, each kernel, and constructibility, while the inverse-image node supplies exactness for module sheaves. Step 2 uses, with their stated finite affine-etale and qcqs hypotheses, the finite-family models, restriction-preserves-injectives, free-sheaf derived-sections calculation, coefficient-forgetting comparison, and 09YQ cohomology continuity; these give every-degree comparisons for each $E_r$. Step 3 uses the affine-etale site colimit and the pulled-back coefficient's stage-section colimit exactly on the finite affine summands. The finite-presentation node supplies the finite presentation, and the eventual-hom-lift node supplies a stage map; the written kernel argument supplies the relation and eventual equality checks rather than attributing them to either node. Step 4 uses the contravariant six-term exact segment and filtered-colimit exactness. For injectivity it uses the shifted segment and the corrected mono leaf with alpha epi, beta mono, delta mono. For surjectivity it uses the unshifted segment and the epi leaf with alpha epi, gamma epi, delta mono. The finite triangular ranges ensure every cited comparison is already available; at degree $n$, $r=0$ gives the target. Step 5 uses exact inverse-image composition and the exact-functor Ext comparison for canonicality and compatibility with later stages.

I checked the small edge cases explicitly: for $n=0$ the induction reduces to the degree-zero Hom comparison; for the terminal triangular boundary $r=n-d$ only the shifted mono pass is used, while the epi pass is applied at $r\le n-d-1$; and the old four-lemma orientation fails on the integer diagram recorded above. I also verified every `citations.json` quote is verbatim from its cited node and that no SGA source is cited.
