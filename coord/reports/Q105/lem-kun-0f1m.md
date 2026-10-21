# Repair report: lem-kun-0f1m

## Files written

- dag/nodes/sec-smooth-purity/lem-kun-0f1m.json: original statement retained, six-step assembly.
- dag/nodes/sec-smooth-purity/lem-kun-lower-truncation-flat-model.json: statement, unsplit, no Mathlib match for the full flat truncation/kernel package.
- dag/nodes/sec-smooth-purity/lem-kun-kflat-short-exact-quotient.json: statement, unsplit, no Mathlib match for total tensor exactness and K-flat two-out-of-three.
- citations.json: verbatim statement quotations for every citation in every assembly step.

## Attachments

None. The project declaration in lean/Sheaf/AlgebraicGeometry/TorAmplitudeKFlatResolution.lean:134 ends in sorry. Searching WeilConjectures for the item tag and exact declaration produced no attachment. No Lean files were written or compiled.

## WANTED

None: all cited Stacks sources are available locally.

## Repair of the returned delivery

The sandbox initially contained only dispatcher brief files, with no item, report or search log to continue. I used the current repository's full seven-step version, preserving its statement, metadata, historical searches, and blueprint_update. This is the deliberate re-split requested on 2026-10-21, not an unchanged delivery of an already reviewed node. The old proof's truncation argument (steps 4-5) is now the first new task; its tensor-exactness argument (step 6) is the second new task. Both nodes are status unsplit with empty proof/proof_deps and null proof_origin; subsequent workers can work on them independently. The first assumes a flat cokernel but does not prove it or K-flatness of the quotient; the second assumes an existing short exact sequence but constructs neither a representative nor a truncation. Neither restates the item's equivalence or pullback assertion.

The original step 4-5 construction and step 6 tensor argument remain verbatim below as handoff material; they have not been erased or blurred. Steps 1-3 and 7 remain as the parent assembly, with the existence theorem, flat cokernel theorem, and pullback theorem used by their statements.

## Preserved argument for lem-kun-lower-truncation-flat-model

Form $\mathcal E^\bullet=\tau_{\ge a}\mathcal K^\bullet$ using [def-kun-truncations]: its terms are zero below $a$, $\mathcal N$ in degree $a$, and $\mathcal K^i$ above $a$; the differential from $\mathcal N$ is induced by $d^a$. All terms are flat by the preceding steps. The canonical map is the quotient $q:\mathcal K^\bullet\to\mathcal E^\bullet$. In degree $a$, the induced differential has kernel $\ker(d^a)/\operatorname{im}(d^{a-1})$ and there are no incoming boundaries, so $H^a(q)$ is the canonical isomorphism onto this quotient. In degree $a+1$ its incoming image is still $\operatorname{im}(d^a)$, and all higher differentials are unchanged; hence $H^i(q)$ is an isomorphism for every $i\ge a$. Below $a$, the source cohomology vanishes by step 2 and the target terms are zero. Thus $q$ is a quasi-isomorphism, and $\mathcal E^\bullet$ represents $E$.

Put $\mathcal I=\operatorname{im}(d^{a-1})$. The sequence $0\to\mathcal I\to\mathcal K^a\to\mathcal N\to0$ is short exact. Both $\mathcal K^a$ and $\mathcal N$ are flat, so the last assertion of [lem-weil-pbc-site-flat-quotient-tensor-ses] makes $\mathcal I$ flat. The kernel complex $\mathcal L^\bullet=\ker(q)$ has terms $\mathcal K^i$ for $i<a$, $\mathcal I$ at $a$, and zero above $a$, with the induced differential. It is bounded above with flat terms, hence K-flat by [lem-kun-kflat-criteria](1). We have a degreewise short exact sequence $0\to\mathcal L^\bullet\to\mathcal K^\bullet\to\mathcal E^\bullet\to0$.

The worker's hypotheses are now explicit: a termwise flat complex with vanishing cohomology below a and flat cokernel at a. Its proof should use the already existing lem-weil-pbc-site-flat-quotient-tensor-ses and lem-kun-kflat-criteria(1); these are not proof dependencies yet because the new node is delivered statement-only. The canonical boundary calculation and kernel identification are part of this task, not an assumption that the truncation is K-flat.

## Preserved argument for lem-kun-kflat-short-exact-quotient

We verify K-flatness of $\mathcal E^\bullet$ directly; a degreewise short exact sequence need not be a cone triangle in the homotopy category. Let $A^\bullet$ be any acyclic complex. Since each $\mathcal E^p$ is flat, [lem-weil-pbc-site-flat-quotient-tensor-ses] applied in degree $p$ with the sheaf $A^q$ gives $0\to\mathcal L^p\otimes A^q\to\mathcal K^p\otimes A^q\to\mathcal E^p\otimes A^q\to0$. Taking the direct sum over $p+q=n$ preserves exactness: finite direct sums of these sequences are exact by the biproduct identities, and their filtered colimit over finite subsets of the small set $\{(p,q)\in\mathbf Z^2:p+q=n\}$ is exact by [lem-pc-module-filtered-colimits-tensor]. For either chain map $f$, its tensor map in bidegree $(p,q)$ is $f^p\otimes1$; the identities $d f^p=f^{p+1}d$ and $(-1)^p(f^p\otimes d_A)=(f^p\otimes1)(-1)^p(1\otimes d_A)$ show that these maps commute with the total differentials. Thus we obtain a degreewise short exact sequence of total tensor complexes. The first two complexes are acyclic by K-flatness of $\mathcal L$ and $\mathcal K$ and [def-kun-derived-tensor]. The long exact cohomology sequence [lem-weil-pbc-complex-ses-homology-long-exact] has the exact segment $H^n(\mathcal K\otimes A)\to H^n(\mathcal E\otimes A)\to H^{n+1}(\mathcal L\otimes A)$. Both outside terms are zero, so $H^n(\mathcal E\otimes A)=0$ for all $n$. The definition of K-flatness proves the claim.

For the general statement's remaining two-out-of-three cases, use the other adjacent exact cohomology segments of the same tensor short exact sequence. The total maps on each summand are f^p tensor 1 and g^p tensor 1; the horizontal chain-map identity and the unchanged factor (-1)^p prove compatibility with the total differential. In the final proof the acyclic test can be on either side by the signed symmetry in def-kun-derived-tensor. The existing lem-pc-module-filtered-colimits-tensor, lem-weil-pbc-site-flat-quotient-tensor-ses, and lem-weil-pbc-complex-ses-homology-long-exact state the three inputs. This is Stacks 0G7B with its omitted direct-sum exactness expanded.

## Not duplicates

lem-kun-lower-truncation-flat-model vs lem-kun-0f1m: same source Tag 0F1M; the new node starts from a specified flat complex and a flat cokernel and proves the canonical quotient/kernel facts. It has no Tor-amplitude equivalence, resolution existence, or pullback assertion, and does not claim K-flatness of its quotient.
lem-kun-kflat-short-exact-quotient vs lem-kun-0f1m: source Tag 0G7B is invoked in Tag 0F1M; the new node is the generic total-tensor exactness and two-out-of-three tool, not a Tor-amplitude model theorem.
lem-kun-kflat-short-exact-quotient vs lem-kun-kflat-criteria: criterion (2) assumes a distinguished triangle in the homotopy category; the new node assumes a degreewise short exact sequence with flat quotient terms. Such a sequence need not be a distinguished triangle in the homotopy category. Criterion (1) only treats bounded-above flat complexes.
lem-kun-lower-truncation-flat-model vs def-kun-truncations: the latter defines good truncations and describes their cohomology, but does not give the flat boundary image, flat bounded-above kernel, or K-flatness of that kernel.
lem-kun-lower-truncation-flat-model vs lem-kun-tor-cokernel-flat: that node deduces flatness of N from universal tensor vanishing; the new node assumes N flat and constructs the quotient and its kernel.
lem-kun-kflat-short-exact-quotient vs lem-weil-pbc-site-flat-quotient-tensor-ses: that node treats a single sheaf-level short exact sequence, not integer complexes, exact infinite total sums, or K-flatness.

Whole-DAG statement scans for K-flat with short exact/truncation and tag searches, and blueprint_refs searches for K-flat, lower truncation, truncation kernel, flat quotient, and two out of three, found no existing statement of either new task. The module/sheaf distinction excludes the affine truncation-kernel lemmas about ordinary modules over an affine coordinate ring; they do not state this arbitrary etale sheaf-complex construction. Mathlib searches were executed using msearch.py and retained in searches.jsonl. Both semantic phrasings were read. CochainComplex.quasiIso_πTruncGE_iff (Mathlib/Algebra/Homology/Embedding/CochainComplex.lean:277) supplies only the ordinary cohomological part of the first task. Module.Flat.lTensor_shortComplex_exact and rTensor_shortComplex_exact (Mathlib/RingTheory/Flat/CategoryTheory.lean:41,46) concern flat tensor factors in ModuleCat, not a flat quotient of unbounded sheaf complexes; they do not state the second task.

## Review by Q105

I read Stacks sites-cohomology.tex Tag 0F1M (lemma-bounded-below-tor-amplitude) for the item and the first new task, Tag 0G7B (lemma-K-flat-two-out-of-three-ses) for the second new task, and Tag 0G7E (lemma-pullback-K-flat) for the final assembly step. I compared the current blueprint_update and the unit/chapter route. The previously corrected quotient direction K to P is essential: the degree-a arrow is a cokernel projection, not a canonical map P to K. The already repaired avoidance of a homotopy cone inference is retained. Module pullback need not be exact; the cited general ringed-topos theorem supplies precisely the moreover clause. The parent statement is unchanged, so there is no new statement dispute.

Step 1 uses the definition of derived tensor on a K-flat representative and the definition of lower Tor amplitude, both read in full; vanishing terms imply vanishing cohomology below a. Step 2 uses the flat-resolution theorem for an actual representative complex, and the same definitions to turn the amplitude assumption into universal tensor cohomology vanishing. Testing with the unit yields ordinary cohomology vanishing. The size convention gives the small skeleton needed for the site-level tools. Step 3 uses precisely lem-kun-tor-cokernel-flat: both its termwise flatness and its universal tensor-vanishing hypotheses have just been verified.

Step 4 uses the entire explicit quotient/kernel conclusion of the first new statement; it does not take anything merely from a proof. Its three hypotheses are flat terms, cohomology vanishing below a, and flat cokernel N, provided by steps 2 and 3. This gives a representative, a flat quotient complex and a K-flat kernel. Step 5 uses the second new statement with L and K as the two K-flat inputs and P the flat-term quotient. Its exactness hypothesis is explicitly supplied by step 4. Step 6 invokes the ringed-topos pullback theorem with that same fixed P; no coefficient-flatness assumption is added, and the representative is selected before the universal quantification over u. I read all the cited existing statements and placed verbatim quotations in citations.json. The new tasks' definitions likewise introduce the sites, coefficient rings, complexes, cohomology, flatness, quasi-isomorphism, and K-flatness they use.

For the small cases, the zero complex and empty scheme give zero quotients and kernels. A flat module concentrated at degree a gives P=K and L=0. At degree a the quotient cohomology is ker(d^a)/im(d^{a-1}); at a+1 the incoming image is unchanged. A bounded-above L ending in I is not assumed acyclic in the new statement; K-flatness follows from flatness and boundedness. The second new statement works with L=0 or P=0 and with arbitrarily unbounded complexes; exactness of the full total sums uses filtered colimits of finite sums in a small index set. No sectionwise surjectivity, enough-points assumption, or splitting is used.

Against B-E: new nodes are self-contained statements only, with source tags/labels, TeX and genuine logged searches; they are not restatements of the parent or of existing nodes. Every parent citation was opened and its hypotheses checked, with a verbatim quote recorded. No proof step takes an unrecorded non-elementary fact: the previously long tensor argument is now explicitly a cited task, as requested. The new nodes have no proof dependencies and neither depends on the parent, so the re-split adds no proof cycle. The assembly has no step over 2000 characters and its total length is recorded below. Prior maintainer metadata and upstream Lean remain untouched.

## Unfinished work

The two new tasks are intentionally unsplit and await their own stage-1 workers. No other requested repair remains.

Parent assembly length: 2169 characters (limit 3000).
