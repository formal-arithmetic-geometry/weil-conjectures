# Worker report: lem-trf-etale-finite-smooth-local-structure

1. Files written:

- `dag/nodes/sec-trace-formula/lem-trf-etale-finite-smooth-local-structure.json`: unchanged statement; three-step assembly, 2447 characters.
- `dag/nodes/sec-trace-formula/lem-trf-finite-smooth-preliminary-chart.json`: statement, unsplit; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-finite-smooth-integral-base-refinement.json`: statement, unsplit; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-marked-finite-smooth-affine-refinement.json`: statement, unsplit; no Mathlib match.
- `citations.json`: one verbatim statement quotation for each assembly citation.

2. Attachments: none. The upstream project search found no declaration of the item. The existing Sheaf theorem `AlgebraicGeometry.exists_affine_etale_finite_smooth_local_structure` at `lean/Sheaf/TraceFormula/EtaleFiniteSmoothLocalStructure.lean:100` ends in `sorry` at line 119 and is not an attachment.

3. WANTED: none.

4. Repair: the repository supplied the returned eleven-step split; the sandbox initially held only dispatcher marker files, no node, report, or search log. I copied the current repository item and retained all metadata, searches, citations and arguments. Its statement agrees with Stacks 057K (1)--(6) plus 057L (7) and is unchanged. This return requires actual distribution of work; the delivery introduces three independent statement-only nodes, not a shortened replacement for the old argument. The first creates the preliminary chart without imposing integral fibres; the second starts with any such finite/smooth diagram and refines the base; the third starts with any pointed finite-over-smooth geometrically integral diagram and makes it affine, without mentioning the original morphism. None assumes or cites the item.

5. Unfinished: proofs of the three new nodes, intentionally left unsplit for parallel stage-1 workers as the return requires. No Lean work was performed.

## Work distribution and retained arguments

The argument allocations have sizes 2198, 2189, 2019 characters. Every old step is reproduced below verbatim, together with the nodes it uses. These are handoff notes, not proof steps on the statement-only nodes.

### lem-trf-finite-smooth-preliminary-chart

Source: Tag 052E, lemma-local-structure-finite-type, proof; Tag 057K, lemma-local-local-structure-finite-type, proof through the affine choice of Y and finite presentation of h.

Old step 1 (641 characters):

Choose an affine open $S^a\subset S$ containing $s$, and an affine open $Z^a\subset p^{-1}(S^a)$ containing $z$. The affine-pairs criterion makes $Z^a\to S^a$ finite type. The germ of the fibre at $z$ has not changed: by the open fibre-product identification, $(Z^a)_s=Z^a\times_{S^a}\operatorname{Spec}\kappa(s)$ is the open subscheme of $Z_s$ lying over $Z^a$, and open neighbourhoods inside an open neighbourhood form a cofinal system in the definition of topological dimension at a point. Thus its dimension is still $n$. Work with this affine pair; every later map to it will be composed with the open immersions into the original pair.

Uses: `lem-weil-pbc-affine-opens-basis`, `lem-weil-pbc-lft-affine-pairs`, `def-kun-dimension`, `lem-weil-pbc-open-fibre-product`.
Source: Tags 052E and 057K, initial affine reduction.

Old step 2 (401 characters):

Apply the refined chart lemma to obtain $S_0,Z_0$ and $q:Z_0\to A=\mathbf A^n_{S_0}$, quasi-finite, with $t=q(z)$ and $\kappa(t)/\kappa(s)$ purely transcendental. The projection $A\to S_0$ is smooth of relative dimension $n$. Because the fibre of $q$ is finite discrete, $z$ is an isolated point in that fibre, so the hypotheses for the elementary etale finite-neighbourhood lemma hold for $q$ at $z$.

Uses: `lem-trf-refined-quasi-finite-polynomial-pure-transcendental`, `sbc-lem-affine-space-smooth`.
Source: Tag 052E, refined polynomial chart before the elementary etale construction.

Old step 3 (611 characters):

Apply the elementary etale finite-neighbourhood lemma to $q:Z_0\to A$. It gives $e:(Y_0,y_0)\to(A,t)$ etale with $\kappa(t)\simeq\kappa(y_0)$ and an open $W_0\subset Z_0\times_A Y_0$, finite over $Y_0$, whose fibre at $y_0$ is the single point $w_0$, mapping to $z$, with $\kappa(z)\simeq\kappa(w_0)$. The map $b_0:W_0\to Z$ is etale: it is an open immersion followed by the base change of $e$, then the open inclusion $Z_0\to Z$. The composite $h_0:Y_0\to A\to S_0$ is smooth of relative dimension $n$ by permanence, since $e$ has relative dimension zero. Its marked residue extension is purely transcendental.

Uses: `lem-weil-pbc-etale-local-finite-at-point-elementary`, `lem-weil-pbc-etale-scheme-base-change`, `lem-weil-pbc-etale-composition-cancellation`, `lem-sbc-smooth-relative-dimension-permanence`.
Source: Tag 052E, apply Tag 02LK over affine space, not over S.

Old step 4 (545 characters):

Replace $Y_0$ by an affine open neighbourhood of $y_0$ and $W_0$ by its inverse image. Finiteness persists by base change, and this inverse image is open in the former $W_0$; hence the etale map to $Z$, the singleton fibre and marked residue fields persist. The restricted $h_0$ still has relative dimension $n$, since an open immersion is etale. Affine $Y_0$ and $S_0$ are quasi-compact and quasi-separated, so $h_0$ is quasi-compact and quasi-separated. Smoothness gives local finite presentation. Consequently $h_0$ is of finite presentation.

Uses: `lem-weil-pbc-affine-opens-basis`, `lem-weil-pbc-open-fibre-product`, `lem-weil-pbc-finite-morphism-permanence`, `lem-weil-pbc-etale-composition-cancellation`, `lem-sbc-smooth-relative-dimension-permanence`, `lem-weil-pbc-affine-scheme-qcqs`, `lem-weil-pbc-qcqs-morphism-permanence`, `lem-pc-smooth-flat`.
Source: Tag 057K, affine neighbourhood of y and finite presentation of h.

### lem-trf-finite-smooth-integral-base-refinement

Source: Tag 057K, lemma-local-local-structure-finite-type, proof from the connected component T through the outer pullback diagram and the marked residue-field identifications.

Old step 5 (435 characters):

The fibre $C=(Y_0)_s$ is smooth over $k=\kappa(s)$ by base change; it is finite type since it is affine and its structure map is locally of finite presentation. Its point $y_0$ has purely transcendental residue field over $k$. Apply the smooth component lemma: the connected component $T$ of $y_0$ is an open quasi-compact geometrically integral $k$-scheme. In particular it is geometrically irreducible, as required for the next step.

Uses: `lem-sbc-smooth-relative-dimension-permanence`, `lem-weil-pbc-fibre-product-affine-spectra`, `lem-pc-smooth-flat`, `lem-trf-smooth-component-pure-transcendental`, `def-pc-geometrically-irreducible`.
Source: Tag 057K, component T; Tags 04KV, 056T and 033M.

Old step 6 (533 characters):

Apply elementary etale spreading to the finitely presented smooth $h_0:Y_0\to S_0$ and the geometrically irreducible open $T\subset (Y_0)_s$. It gives affine $(S_1,s_1)\to(S_0,s)$ etale with $\kappa(s_1)\simeq\kappa(s)$, and a quasi-compact open $V\subset Y_0\times_{S_0}S_1$ with geometrically integral fibres and $V_{s_1}=T\times_s s_1$. The map $V\to Y_0$ is etale, being the restriction of the base change of $S_1\to S_0$. The morphism $h_1:V\to S_1$ is smooth of relative dimension $n$ by base change and restriction to an open.

Uses: `lem-trf-geometrically-integral-fibre-neighbourhood`, `lem-weil-pbc-etale-scheme-base-change`, `lem-weil-pbc-etale-composition-cancellation`, `lem-sbc-smooth-relative-dimension-permanence`.
Source: Tag 057K, application of Tag 057J.

Old step 7 (536 characters):

There is exactly one point $y_1$ of $Y_0\times_{S_0}S_1$ over the pair $(y_0,s_1)$: the fibre-product point correspondence identifies these points with primes of $\kappa(y_0)\otimes_{\kappa(s)}\kappa(s_1)\simeq\kappa(y_0)$, a field. Its residue field is $\kappa(y_0)$ compatibly with the projections, by the fibre-product residue-field theorem. Since $y_0\in T$ and $V_{s_1}=T\times_s s_1$, this point belongs to $V$. Therefore $\kappa(y_1)/\kappa(s_1)$ is the original purely transcendental extension under these field identifications.

Uses: `lem-weil-pbc-fibre-product-points`, `lem-weil-pbc-fibre-product-point-residue-field`.
Source: Tag 057K, point (y,s′) and its residue field.

Old step 8 (685 characters):

Set $W_1=W_0\times_{Y_0}V$, with projection $\pi_1:W_1\to V$. It is finite by base change. A point of its fibre at $y_1$ must map to $w_0$, since $w_0$ is the only point of $W_0$ over $y_0$. Points over $(w_0,y_1)$ correspond to primes of $\kappa(w_0)\otimes_{\kappa(y_0)}\kappa(y_1)\simeq\kappa(w_0)$. Thus there is exactly one such point $w_1$, and its residue field is $\kappa(w_0)$ compatibly with the projection; in particular $\kappa(z)\to\kappa(w_1)$ is an isomorphism. The map $W_1\to W_0$ is etale, as a base change of $V\to Y_0$, so $b_1:W_1\to Z$ is etale. The morphism $a_1:S_1\to S_0\to S$ is etale and elementary at $s_1$. The pullback identities give $pb_1=a_1h_1\pi_1$.

Uses: `lem-weil-pbc-finite-morphism-permanence`, `lem-weil-pbc-fibre-product-points`, `lem-weil-pbc-fibre-product-point-residue-field`, `lem-weil-pbc-etale-scheme-base-change`, `lem-weil-pbc-etale-composition-cancellation`.
Source: Tag 057K, final pullback and the omitted marked-point details.

### lem-trf-marked-finite-smooth-affine-refinement

Source: Tag 057L, lemma-local-local-structure-finite-type-affine, proof: U prime, V prime, image W prime, U double prime, and the finite inverse image.

Old step 9 (719 characters):

For the affine refinement choose affine opens $U'\subset S_1$ around $s_1$ and $V'\subset h_1^{-1}(U')$ around $y_1$. Smoothness of $h_1$ implies flatness and local finite presentation, so $h_1$ is open. Hence $h_1(V')$ is an open neighbourhood of $s_1$ inside $U'$. Choose an affine open $U''\subset h_1(V')$ containing $s_1$, and set $Y=V'\cap h_1^{-1}(U'')$. The open fibre-product identification gives $Y=V'\times_{U'}U''$. All three schemes on the right are affine, so $Y$ is affine by the affine fibre-product formula. Put $S_1^{\mathrm{fin}}=U''$. By its choice, $Y\to U''$ is surjective; it is still smooth of relative dimension $n$, since the open immersion $Y\to V$ is etale and permanence applies with $m=0$.

Uses: `lem-weil-pbc-affine-opens-basis`, `lem-pc-smooth-flat`, `lem-weil-pbc-flat-lfp-open`, `lem-weil-pbc-open-fibre-product`, `lem-weil-pbc-fibre-product-affine-spectra`, `lem-sbc-smooth-relative-dimension-permanence`, `lem-weil-pbc-etale-composition-cancellation`.
Source: Tag 057L, affine opens U′,V′,U′′.

Old step 10 (676 characters):

Every fibre of $Y\to U''$ is a nonempty open subscheme of the corresponding geometrically integral fibre of $V\to S_1$. After any extension of the residue field it is still an open subscheme, by the open fibre-product formula, and remains nonempty by base-change stability of surjectivity. A nonempty open of an irreducible space is irreducible: two nonempty relatively open subsets are nonempty opens in the ambient space and must meet. Reducedness persists since its local rings are unchanged on passing to an open subscheme. Thus every extended fibre is nonempty, irreducible and reduced, hence integral by definition. This proves geometric integrality of the final fibres.

Uses: `lem-weil-pbc-open-fibre-product`, `lem-weil-pbc-surjective-base-change`, `def-pc-integral-scheme`, `def-pc-geometrically-irreducible`.
Source: Tag 057L, nonempty opens in geometrically integral fibres.

Old step 11 (624 characters):

Finally let $W=W_1\times_VY$ and restrict $\pi_1$ to $\pi:W\to Y$. This is finite, so $W$ is affine because $Y$ is affine. The points $y_1,w_1$ remain in these open subschemes; rename them $y,w$. The fibre at $y$ is still $\{w\}$. Open restrictions preserve all three marked residue fields, and the maps $b:W\to Z$ and $a:U''\to S$ remain etale by composition with open immersions. The relative dimension, geometric integrality and purely transcendental residue extension were retained in the preceding steps, while the commutative identity restricts to $pb=ah\pi$. Renaming $U''$ as $S_1$ gives every assertion of the item.

Uses: `lem-weil-pbc-finite-morphism-permanence`, `lem-weil-pbc-open-fibre-product`, `lem-weil-pbc-etale-composition-cancellation`.
Source: Tag 057L, finite source over affine Y and restriction of the marked diagram.

## Review by Q103

I read Stacks more-morphisms.tex at 052E, 057K and 057L against the item statement and all eleven old steps, and read 057J (normal morphism/irreducible fibre neighbourhood) for the integral-base refinement. The tag/label mappings in stacks-project/tags/tags agree with these places. I read the chapter and sk-i-curve-zero unit records, the current main-20261015 ancestor statement and proof, and preserved the inherited local-structure input and blueprint chain rather than changing the chapter/unit route.

Assembly step 1 uses precisely the statement of the preliminary-chart node: it allows a merely locally finite type morphism and fixes the topological fibre dimension at z; it gives affine Y0 and S0, a finitely presented smooth h0, an elementary etale b0 and a finite pi0 with a singleton fibre and purely transcendental marked extension. Its separate argument is old steps 1--4: affine-pair reduction and dimension on an open fibre; the refined polynomial chart; elementary etale finiteness over affine space (not over S); and affine restriction plus qcqs to obtain finite presentation. I opened each cited dependency statement; in particular the polynomial node gives the prescribed pure-transcendental image, the elementary-etale node gives both residue isomorphisms, and the qcqs permanence node gives finite presentation.

Assembly step 2 uses exactly the integral-base-refinement statement with the affine, finite-presentation, smooth-dimension, purely-transcendental and singleton hypotheses just supplied. Old steps 5--8 are its separate proof task: use the smooth-component node for the component T in the finite-type smooth fibre, use the integral-fibre-neighbourhood node for an elementary base neighbourhood, and compute the two unique marked points and their residue fields via the fibre-product-points and fibre-product-residue-field statements. Those statements give primes of the residue-field tensor product and identify the actual induced field maps, not merely abstract isomorphic fields. I checked the two tensor products are fields because one base factor is the residue-field isomorphism. This is what preserves singleton fibres; arbitrary etale base change would not suffice. Etale base change and smooth relative-dimension permanence supply the projection properties in the new conclusion. The assembly also cites the composition-cancellation node: its (1) makes j etale and its (2) composes b0 with rho and j with e. Isomorphism composition and substitution in the commutative square are elementary.

Assembly step 3 uses precisely the affine-refinement statement, whose hypotheses are finiteness, singleton marked fibre, smooth relative dimension n and geometric integrality, all supplied at step 2. The new lemma is independent of p, b0 and the elementary base neighbourhood. Its separate task is old steps 9--11: choose affine U prime and V prime, use smooth flat-lfp openness, choose U double prime inside the image, identify the final middle as an affine fibre product, and show the restricted fibres remain nonempty geometrically integral. I verified the openness, affine fibre product, finite permanence and surjective base-change node statements. In particular, no intersection of unrelated affine opens is assumed affine: both opens lie over the affine U prime and their product is affine. The image choice forces surjectivity; after every field extension, surjectivity keeps the open fibre nonempty, and reducedness/irreducibility pass to that open. Finiteness makes the final W affine. The new conclusion explicitly preserves induced residue-field maps and restricted equations; therefore the assembly can compose the two outside etale maps using the composition-cancellation node and retain pure transcendence without a hidden comparison theorem.

Edge cases: n=0 and r=0 are included (a trivial rational-function extension is allowed). The preliminary construction works over nonreduced and non-Noetherian bases because only affine finite type is used before the smooth finitely presented intermediate chart. The smooth fibre is finite type over a field, so the component input applies without assuming the base Noetherian. For a disconnected smooth fibre the chosen pure-transcendental point singles out the relevant component; Spec(C) over R fails that residue-field hypothesis, so it is not a counterexample to geometric integrality. In the affine refinement an arbitrary affine open need not meet every fibre; choosing the base inside its open image repairs precisely that issue. Empty base/source cases with marked points cannot satisfy the hypotheses. The finite map is not assumed flat or surjective away from its marked fibre. No new statement needs p locally of finite presentation.

C1/C4 audit: every non-elementary operation remaining in the assembly is one of the new conclusions or the explicit etale composition theorem. The report preserves the old dependency list for every future proof package; it does not pretend those proofs are complete. All citations.json quotes are entire verbatim cited statements. The three new nodes have empty proof/proof_deps and null proof_origin, no inline proof sketches in their statements. No assembly step exceeds 2000 characters, and the total is below 3000. The unchanged statement, sources, blueprint metadata and old search records have been retained. I read delivery-errors B--E and checked scope, self-contained objects, definition citations, finite-presentation hypotheses, induced rather than abstract residue isomorphisms, cycles and duplicate statements. No SGA source is used.

Mathlib searches: each new node has two semantic phrasings, a natural-language LeanSearch query, a Loogle pattern and grep; every query was run with msearch.py and retained in searches.jsonl, with full hits in search-results/. Initial Loogle patterns using IsSmooth were rejected by its older index; those are recorded as rejected queries, and I reran valid quoted-name patterns. The closest preliminary hits concern already smooth standard charts and elementary etale local algebra, not the finite/smooth factorization of an arbitrary locally finite type morphism. The integral hits give definitions/base-change stability or etale loci, not a neighbourhood with integral fibres and the marked pullback. The affine hits give an affine cover of a quasi-compact scheme or an affine open basis, not simultaneous shrinking to a surjective smooth map with integral fibres. I read Mathlib AlgebraicGeometry/Morphisms/Smooth.lean:84,99, Morphisms/Descent.lean:48, AffineScheme.lean:272, Geometrically/Integral.lean:40 onward, and RingTheory/Etale/QuasiFinite.lean:13 onward to reject these candidates. The item was also searched anew, while inherited search records were kept.

## Not duplicates

- lem-trf-finite-smooth-preliminary-chart vs lem-trf-coordinate-prime-affine-chart-realization: the new node constructs an elementary etale finite-over-smooth diagram for an arbitrary locally finite type morphism, with finite presentation of its smooth middle map; the existing node starts with a given localized polynomial ring map and coordinate prime and realizes a quasi-finite affine-space chart. It gives neither the elementary etale finite cover nor the finite/smooth factorization.

- lem-trf-finite-smooth-preliminary-chart vs lem-trf-finite-type-component-open-qc: the new node constructs a finite-over-smooth chart for an arbitrary locally finite type morphism, including the singleton marked finite fibre and its residue maps; the existing node only asserts openness, quasi-compactness and finite type of a connected component of a finite-type scheme over a field; it constructs no chart, base neighbourhood or finite pullback.
- lem-trf-finite-smooth-preliminary-chart vs lem-trf-pure-transcendental-relatively-algebraically-closed: the new node constructs a finite-over-smooth chart for an arbitrary locally finite type morphism, including the singleton marked finite fibre and its residue maps; the existing node is a field-theoretic relative-algebraic-closedness assertion; it constructs no scheme or morphism.
- lem-trf-finite-smooth-integral-base-refinement vs lem-trf-finite-type-component-open-qc: the new node refines a given finite-over-smooth diagram after an elementary etale base change, with integral fibres and compatible unique marked lifts; the existing node only asserts openness, quasi-compactness and finite type of a connected component of a finite-type scheme over a field; it constructs no chart, base neighbourhood or finite pullback.
- lem-trf-finite-smooth-integral-base-refinement vs lem-trf-pure-transcendental-relatively-algebraically-closed: the new node refines a given finite-over-smooth diagram after an elementary etale base change, with integral fibres and compatible unique marked lifts; the existing node is a field-theoretic relative-algebraic-closedness assertion; it constructs no scheme or morphism.

- lem-trf-finite-smooth-preliminary-chart vs lem-trf-cm-closed-point-flat-quasifinite-slice: the new node constructs the preliminary finite/smooth chart, without integral fibres; the existing node constructs a quasi-finite slice at a Cohen-Macaulay closed point.
- lem-trf-finite-smooth-preliminary-chart vs lem-trf-elementary-module-devissage: the new node constructs the preliminary finite/smooth chart, without integral fibres; the existing node constructs a module-support devissage and depends on the item, so it cannot be used as a geometric input here.
- lem-trf-finite-smooth-preliminary-chart vs lem-trf-etale-finite-smooth-local-structure: the new node constructs the preliminary finite/smooth chart, without integral fibres; the existing node is the parent being split and combines all three arguments, rather than stating this separate work package.
- lem-trf-finite-smooth-preliminary-chart vs lem-trf-fibre-regular-element-flat-hypersurface: the new node constructs the preliminary finite/smooth chart, without integral fibres; the existing node constructs a flat hypersurface from a nonzerodivisor.
- lem-trf-finite-smooth-preliminary-chart vs lem-trf-geometrically-connected-fibre-open-spreading: the new node constructs the preliminary finite/smooth chart, without integral fibres; the existing node spreads a given connected open fibre for a flat geometrically reduced map, without a finite cover or its marked residue fields.
- lem-trf-finite-smooth-preliminary-chart vs lem-trf-geometrically-integral-fibre-neighbourhood: the new node constructs the preliminary finite/smooth chart, without integral fibres; the existing node starts from a given geometrically irreducible open T and gives a fibre neighbourhood, without choosing T from a residue field or lifting a finite singleton fibre.
- lem-trf-finite-smooth-preliminary-chart vs lem-trf-polynomial-shear-leading-coefficient: the new node constructs the preliminary finite/smooth chart, without integral fibres; the existing node only gives a monomial coordinate shear for a polynomial.
- lem-trf-finite-smooth-preliminary-chart vs lem-trf-refined-noether-normalization-prime: the new node constructs the preliminary finite/smooth chart, without integral fibres; the existing node is a polynomial-ring prime-normalization theorem.
- lem-trf-finite-smooth-preliminary-chart vs lem-trf-refined-quasi-finite-polynomial-pure-transcendental: the new node constructs the preliminary finite/smooth chart, without integral fibres; the existing node only constructs a quasi-finite polynomial chart, without an elementary etale finite cover or the smooth finite-presentation intermediate diagram.
- lem-trf-finite-smooth-preliminary-chart vs lem-trf-smooth-component-pure-transcendental: the new node constructs the preliminary finite/smooth chart, without integral fibres; the existing node only proves that a component of a smooth scheme over a field is geometrically integral, without spreading or a finite diagram.
- lem-trf-finite-smooth-integral-base-refinement vs lem-trf-cm-closed-point-flat-quasifinite-slice: the new node refines a given finite/smooth diagram by an elementary base change and preserves the marked finite fibre; the existing node constructs a quasi-finite slice at a Cohen-Macaulay closed point.
- lem-trf-finite-smooth-integral-base-refinement vs lem-trf-elementary-module-devissage: the new node refines a given finite/smooth diagram by an elementary base change and preserves the marked finite fibre; the existing node constructs a module-support devissage and depends on the item, so it cannot be used as a geometric input here.
- lem-trf-finite-smooth-integral-base-refinement vs lem-trf-etale-finite-smooth-local-structure: the new node refines a given finite/smooth diagram by an elementary base change and preserves the marked finite fibre; the existing node is the parent being split and combines all three arguments, rather than stating this separate work package.
- lem-trf-finite-smooth-integral-base-refinement vs lem-trf-fibre-regular-element-flat-hypersurface: the new node refines a given finite/smooth diagram by an elementary base change and preserves the marked finite fibre; the existing node constructs a flat hypersurface from a nonzerodivisor.
- lem-trf-finite-smooth-integral-base-refinement vs lem-trf-geometrically-connected-fibre-open-spreading: the new node refines a given finite/smooth diagram by an elementary base change and preserves the marked finite fibre; the existing node spreads a given connected open fibre for a flat geometrically reduced map, without a finite cover or its marked residue fields.
- lem-trf-finite-smooth-integral-base-refinement vs lem-trf-geometrically-integral-fibre-neighbourhood: the new node refines a given finite/smooth diagram by an elementary base change and preserves the marked finite fibre; the existing node starts from a given geometrically irreducible open T and gives a fibre neighbourhood, without choosing T from a residue field or lifting a finite singleton fibre.
- lem-trf-finite-smooth-integral-base-refinement vs lem-trf-polynomial-shear-leading-coefficient: the new node refines a given finite/smooth diagram by an elementary base change and preserves the marked finite fibre; the existing node only gives a monomial coordinate shear for a polynomial.
- lem-trf-finite-smooth-integral-base-refinement vs lem-trf-refined-noether-normalization-prime: the new node refines a given finite/smooth diagram by an elementary base change and preserves the marked finite fibre; the existing node is a polynomial-ring prime-normalization theorem.
- lem-trf-finite-smooth-integral-base-refinement vs lem-trf-smooth-component-pure-transcendental: the new node refines a given finite/smooth diagram by an elementary base change and preserves the marked finite fibre; the existing node only proves that a component of a smooth scheme over a field is geometrically integral, without spreading or a finite diagram.
- lem-trf-marked-finite-smooth-affine-refinement vs def-trf-purely-transcendental-extension: the new node refines an already integral smooth finite diagram by affine open restrictions, with no base-change/spreading construction; the existing node only defines pure transcendence.
- lem-trf-marked-finite-smooth-affine-refinement vs lem-trf-elementary-module-devissage: the new node refines an already integral smooth finite diagram by affine open restrictions, with no base-change/spreading construction; the existing node constructs a module-support devissage and depends on the item, so it cannot be used as a geometric input here.
- lem-trf-marked-finite-smooth-affine-refinement vs lem-trf-etale-finite-smooth-local-structure: the new node refines an already integral smooth finite diagram by affine open restrictions, with no base-change/spreading construction; the existing node is the parent being split and combines all three arguments, rather than stating this separate work package.
- lem-trf-marked-finite-smooth-affine-refinement vs lem-trf-geometrically-integral-fibre-neighbourhood: the new node refines an already integral smooth finite diagram by affine open restrictions, with no base-change/spreading construction; the existing node starts from a given geometrically irreducible open T and gives a fibre neighbourhood, without choosing T from a residue field or lifting a finite singleton fibre.
- lem-trf-marked-finite-smooth-affine-refinement vs lem-trf-polynomial-shear-leading-coefficient: the new node refines an already integral smooth finite diagram by affine open restrictions, with no base-change/spreading construction; the existing node only gives a monomial coordinate shear for a polynomial.
- lem-trf-marked-finite-smooth-affine-refinement vs lem-trf-refined-noether-normalization-prime: the new node refines an already integral smooth finite diagram by affine open restrictions, with no base-change/spreading construction; the existing node is a polynomial-ring prime-normalization theorem.
- lem-trf-marked-finite-smooth-affine-refinement vs lem-trf-smooth-component-pure-transcendental: the new node refines an already integral smooth finite diagram by affine open restrictions, with no base-change/spreading construction; the existing node only proves that a component of a smooth scheme over a field is geometrically integral, without spreading or a finite diagram.

Whole-DAG searches by the source tags and finite/smooth, integral-fibre and affine-refinement concepts found no statement of these interfaces. blueprint_refs.py search for finite smooth, geometrically integral, affine refinement, 052E, 057K and 057L found no duplicate blueprint theorem. The closest existing nodes are the ingredients distinguished above. I also read lem-sbc-generic-geometrically-integral-affine-chart: it requires reduced affine source and integral affine base, concerns a generic point, and does not supply a pointed affine restriction for a general smooth family or a finite cover, so it is not a specialization usable here. The new nodes do not depend on the parent or each other; they can be worked independently.

## Promotion-return repair (2026-10-22)

The landing return says that the earlier completion existed only in the side DAG and asks for a delivery rebased onto the current DAG. I compared repair/returned-node.json with the current read-copy item field by field: they are identical. Comparing the sandbox item with that current node, only proof, proof_deps, mathlib_searches and split_report differ. The statement, statement dependencies, source, blueprint chain, Lean records, and maintainer-owned review/tool-use fields are retained from the current node. None of the three new ids exists in the current read-copy DAG.

I re-read all four statements cited by the three assembly steps: the three retained new interfaces and the current lem-weil-pbc-etale-composition-cancellation. All five citations.json entries remain exact verbatim substrings of those statements; the two copies of the existing-node quotation agree with its current statement. No cited interface changed, so no new Mathlib search question arose. I read and reused the retained search log and saved responses. The previous eleven arguments, source citations and duplicate comparisons remain in this report.

This repair also tightens the assembly itself: step 2 now lists every hypothesis supplied by the preliminary chart, writes out both induced residue-field composites (including the open-base inclusion), and derives the composite diagram identity from the two pullback identities. Step 3 now lists its input hypotheses and writes the restricted diagram calculation explicitly. This avoids leaving the residue-map compatibility and diagram equations implicit during the rebase. The three new statements and their balanced work allocation are unchanged.

I re-read Stacks 052E, 057K, 057L and 057J. The first package constructs a chart, the second makes its fibres geometrically integral by an elementary base change, and the third performs the affine restriction; they are separate arguments, not clauses obtained merely by restating the parent. The current source still justifies each interface. The existing Sheaf declaration still ends in sorry and no exact project declaration was found under WeilConjectures. The n=0, r=0, disconnected-fibre and non-Noetherian-base checks in the signed review continue to apply.

The required initial dry run completed against the delivery tool's freshly fetched DAG: OK (not pushed) at 4f120174ccf, preflight passed. That result precedes these assembly/report edits; a new dry run must validate the repaired content before the push. Rebase and commit construction are performed only by the unmodified authorized delivery tool.

## Validation

Server deliver.py --no-push completed successfully: OK (not pushed), preflight passed at cb5c22c785d on 2026-10-22. This includes the server DAG and split checks. Local read-only consistency checks confirmed the item statement is unchanged, all eleven old argument texts remain verbatim in this report, the assembly is 2141 characters (409, 916, 816), and all three new nodes are statement-only. The repository item still matched the retained returned copy at validation. A final dry run follows this report-only correction before the direct push.


## Resumed promotion-return repair (2026-10-22)

I continued the retained sandbox after the provider interruption. The initial required dry run exited successfully at 24a7b591447 (OK, not pushed); there was no active delivery command or push to repeat. I compared repair/returned-node.json against the current read-copy item again: no field differs. The sandbox changes only the proof, proof_deps, mathlib_searches and split_report. The three new ids remain absent from the current read-copy DAG. The delivery tool fetches origin/sheaf-dag again, builds the commit on that current base, and preserves the base's maintainer-owned metadata. This addresses the landing return's rebase request without trying to promote the side completion myself.

I reopened the three new cited statements and the current etale-composition-cancellation statement. The preliminary chart gives every marked-point equation and the commuting diagram used in step 1. The integral-base refinement gives e(s1)=s0, rho(w1)=w0, pi1(w1)=y1, h1(y1)=s1 and compatible induced residue maps; the composition theorem gives openness implies etale and composition of etale maps. The affine-refinement statement preserves the marked points, residue maps and diagram under its three open inclusions. All five citations.json entries remain verbatim portions of these statements. No cited interface has changed.

For an actual repair of the retained assembly, I have now written all the marked-point equations explicitly: the preliminary equations in step 1, their composites through the base refinement in step 2, and their preservation under the final affine restriction in step 3. These equations follow from exactly the cited interfaces; no additional lemma or hypothesis is used. The point conditions now accompany the already explicit diagram and residue-field computations, so every clause of the unchanged item is accounted for in the assembly.

I reread more-morphisms.tex at lemma-local-structure-finite-type (052E), lemma-local-local-structure-finite-type (057K), lemma-local-local-structure-finite-type-affine (057L), and lemma-normal-morphism-irreducible (057J), checking their tags in tags/tags. In particular 057J requires finite presentation, provided by the first package, and the rational marked residue extension selects the geometrically integral component used by the second package. The affine restriction uses the open image to ensure nonempty fibres, including after field extension. The zero-dimensional, trivial rational-function extension, disconnected-fibre and arbitrary-base checks in the signed review remain applicable. The existing Sheaf theorem still has sorry; the read-only WeilConjectures search found no exact declaration to attach.

I read the retained searches.jsonl and saved search results, including the rejected IsSmooth patterns and their successful quoted-name replacements. The statement and search questions are unchanged, so these searches are reused, without inventing or repeating queries. All eleven old arguments remain verbatim above, and all three new nodes remain statement-only. The revised assembly has 2447 characters (516, 1029, 902); every step is under 2000 characters. A final server dry run and direct delivery follow this update.

## Current-DAG repair and review by Q103 (2026-10-23)

The retained returned snapshot repair/returned-node.json is identical, field by field, to the current read-copy item. The three new ids are still absent from that DAG; the sandbox still changes only proof, proof_deps, mathlib_searches and split_report on the item. The released stage-1 repair order explicitly reopens this split item and requires the distributed argument, so the current split status does not supersede this repair. The authorized delivery tool constructs the commit on its freshly fetched current base.

The required initial dry run and the subsequent dry run both exited with a duplicate-tag failure: the current DAG now contains lem-trf-finite-type-component-open-qc and lem-trf-pure-transcendental-relatively-algebraically-closed. I opened both complete node files. The former supplies an open quasi-compact finite-type connected component over a field; the latter supplies relative algebraic closedness of constants in a finite rational function extension. They are ingredients of the smooth-component argument, not either chart/refinement interface. Four explicit comparisons have now been added under Not duplicates. This is a repair against the new DAG content, not an unchanged re-push.

I reread all three retained new statements and the current etale-composition-cancellation statement. They have not changed: step 1 obtains the preliminary diagram; step 2 applies the integral-base interface under its affine, finite-presentation, smooth-dimension, singleton and rational-residue hypotheses, and composes the two outside etale maps; step 3 restricts the resulting pointed finite/smooth diagram to affine opens and composes again. The induced residue maps and all marked-point and diagram equations remain explicit. Every citations.json quotation is still verbatim, and no non-elementary inference was added. I checked the source text in more-morphisms.tex at 052E (lemma-local-structure-finite-type), 057K (lemma-local-local-structure-finite-type), 057L (lemma-local-local-structure-finite-type-affine), and 057J (lemma-normal-morphism-irreducible), including their tag mappings. Finite presentation is provided before 057J; the purely transcendental marked field picks the component; the affine restriction uses an open image, so extended fibres stay nonempty. The n=0, r=0 and non-Noetherian-base cases remain included.

The current project search under WeilConjectures found no exact declaration; the existing Sheaf theorem still ends in sorry. I read the retained search log and saved results and reused those searches because no statement or search question changed. The three new nodes remain statement-only, and all eleven original arguments remain verbatim in the report. The server-only check_dag and review_split checks passed before these report changes. A fresh complete dry run is required after the duplicate comparisons, followed by direct delivery.

The complete dry run passed at 5258571d203. The ensuing push attempt exited before pushing because a newly visible 052E node, lem-trf-coordinate-prime-affine-chart-realization, triggered the same-tag gate. I read its full statement: it realizes an already given quasi-finite coordinate-prime ring chart as an affine-space scheme chart, and does not construct the elementary etale finite neighbourhood or finite/smooth factorization. The additional pairwise comparison is now recorded above. No interface or search question changed. A new dry run validates this report update before another push.
