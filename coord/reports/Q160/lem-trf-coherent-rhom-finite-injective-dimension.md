# Q160 repair report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-coherent-rhom-finite-injective-dimension.json`: existing statement, re-split; statement and existing Lean metadata unchanged; parent proof is 2000 characters, under 3000.
- `dag/nodes/sec-trace-formula/lem-trf-bounded-injective-total-hom-exact.json`: new statement-only node, status `unsplit`; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-bounded-injective-rhom-model-support.json`: new statement-only node, status `unsplit`; no Mathlib match.
- `citations.json`: verbatim statement quotations for every use in each of the five parent steps.
- `searches.jsonl`: unedited search-command log; twelve new searches, six assigned to each new node.

## Attachments

None. Searched `lean/WeilConjectures/` by the exact blueprint id, finite-injective-dimension names, and coherent/RHom concepts. No completed project declaration states this item. The existing `DerivedCategory.coherent_rhom_finite_injective_dimension` in `lean/Sheaf/Algebra/Homology/CoherentRHomFiniteInjectiveDimension.lean` has `sorry` as its proof. Read that theorem and its six-step docstring. Its hypotheses retain unbounded K and match the node. No Lean was written and no compiler was run.

## WANTED

None; all sources used are present locally.

## Return repaired

The return requires work spreading, not a shortened paraphrase. The sandbox initially contained only dispatcher `.brief*` files: no retained node, report, citations or searches. I read the current repository node (including its review and Lean metadata), copied it into the sandbox and repaired that six-step version. Its step lengths and argument match the returned description. The parent statement is verbatim unchanged.

The new statements have 882 and 1006 characters and isolate two different arguments with their own hypotheses. Neither asserts finite generation, so neither restates any clause of the parent. Both work over any commutative ring, with arbitrary source complexes, and make no coherence assumption. Both are delivered with empty proof and proof dependencies and null proof origin, for future parallel splitting. The exactness node is the full chain-level contravariant construction, not a node merely saying that a finite product is exact. The model/support node includes a natural derived-category comparison of the recorded one-object-site internal Hom with the ordinary A-module Hom complex; it is not just the elementary inequality on degrees.

Coverage of every old argument:

1. Old Step 1 (605 characters): bounded-below injectives are K-injective; compute the recorded derived internal Hom using I; preserve its A-module structure. This becomes the model/support node's natural isomorphism in D(A), invoked in new Step 1. Its naturality explicitly includes the restriction map used later.
2. Old Step 2 (442 characters): the kernel-valued good truncation, its quotient and finite cohomology are kept in new Step 2, which cites the existing truncation-cohomology node. No replacement of the good truncation by a stupid truncation is made.
3. Old Step 3 (318 characters): the support calculation becomes the model/support node's upper-support clause, invoked in new Step 4 with C and n. In particular the conclusion includes the termwise vanishing needed by the parent.
4. Old Step 4 (769 characters): extension into the injective terms, quotient factorization, the finite diagonal product and chain-map compatibility become the exactness node, invoked in new Step 3.
5. Old Step 5 (453 characters): the four-term long-exact-sequence segment and its two zero endpoints remain new Step 4. The natural derived comparisons from Step 1 identify the middle modules with the desired derived Hom cohomology. This is the short assembly of the new constructions and the existing LES theorem.
6. Old Step 6 (525 characters): the bounded-above/bounded-below coherence application remains new Step 5, with u=n, v=a, and every finiteness hypothesis checked.

For precision, the complete old argument is preserved verbatim at the end of this report. The following argument allocation records what each future node worker must implement; these are report notes, not proof sketches inside statement-only nodes.

For the exactness node, in degree r use the short exact row on U^s,V^s,W^s. The extension property of I^(s+r) makes restriction surjective. Its kernel consists precisely of the maps descending to W^s; the descent is unique because V^s maps onto W^s. Only a-r <= s <= b-r contribute. Choose the finitely many lifts, with zero components elsewhere. Componentwise precomposition is A-linear and commutes with d_I z - (-1)^r z d_M because j and p are chain maps. This gives the asserted actual short exact sequence of module complexes.

For the model/support node, use the bounded-below-injectives K-injective theorem on I with lower bound a. The definition and independence-of-resolution property of the recorded derived internal Hom computes it using I. On the one-object identity-covered site, a module sheaf and its Hom are evaluated on the sole object, giving exactly the product of A-linear Hom modules and the same signed differential as the module total Hom. This produces an isomorphism in D(A), rather than just per-degree additive equivalences. Precomposition commutes with these comparisons since both are induced by the same chain map f. If M^p=0 for p<n and r>b-n, then every Hom factor is zero: for p<n the source is zero, and for p>=n the target degree p+r>b is zero. Thus the whole degree-r term is zero and so is its cohomology. No claim about the boundary degree r=b-n is made.

## Sources read

Read `dualizing.tex`, Tag 0G4H, `lemma-finite-ext-into-bounded-injective`, including its whole truncation proof. Read `more-algebra.tex`, Tag 0A5S, `definition-injective-dimension`, which defines finite injective dimension by a finite injective complex and allows support [a,b]. Read `derived.tex`, Tag 08J5, `remark-truncation-distinguished-triangle`, which explicitly uses P/(tau_le_n P). Read `more-algebra.tex`, Tag 0A8H, `section-hom-complexes`, for the product and signed differential, and its internal-Hom remark for the module-valued presentation. Read `perfect.tex`, Tag 0D0C, `lemma-coherent-internal-hom`, including the algebra problem and its two spectral sequences. The new node source fields point to 0G4H and name the proof component being expanded; the detailed complex-level expansion above is the author's allocation of that argument, as in the returned split.

The item carries no blueprint update. Read its chapter and unit records (`sec-trace-formula`, `sk-i-curve-zero`) and kept the existing complete-local coherent-duality auxiliary route beneath `lem-trf-local-term-locality`. Ran `blueprint_refs.py ancestor` and searches for bounded injective, Hom exact, total Hom, Hom complex, injective amplitude, and finite injective. No blueprint statement is either new theorem. `from.node` is the existing ancestor, `via` prepends the item, `place` names old Steps 4 or 1/3, and `same_as` is empty. No chapter or unit record changed; no SGA source used.

## Mathlib searches and candidates read

Each new node records exactly its six actual msearch queries: LeanSearch, Loogle, two LeanFinder phrasings, and two grep patterns. Read the results printed by all twelve commands and preserved their original log. No service was unavailable. For exactness, the candidates `HomologicalComplex.shortExact_of_degreewise_shortExact` and `shortExact_iff_degreewise_shortExact` only turn already established degreewise short exactness into short exactness of complexes; they do not construct it for total Hom. Read `Mathlib/Algebra/Homology/HomologicalComplexAbelian.lean` at those declarations. The HomComplex grep returned only unrelated proof uses of `exact` and `ofHom_injective`, not an exactness theorem.

For the model/support node, read `Mathlib/Algebra/Homology/HomotopyCategory/KInjective.lean` at `CochainComplex.isKInjective_of_injective`, which is already attached to the existing K-injective leaf. Read `Mathlib/Algebra/Homology/DerivedCategory/KInjective.lean` at `Qh_map_bijective`, `quasiIso_iff` and `CohomologyClass.bijective_toSmallShiftedHom_of_isKInjective`. These concern maps/shifted Hom groups and do not assert the natural A-module-valued derived internal Hom isomorphism together with the support bound. `DerivedCategory.isZero_of_isLE` and `isLE_iff` express the support predicate after a bound has been proved. A single injective target lemma does not treat a bounded multi-term target. Also read the project `WeilConjectures/Algebra/Homology/ModuleHomComplex.lean`: it supplies the definition and differential, not either new theorem. Neither new node is therefore a Mathlib leaf. The parent's historical Mathlib searches were retained verbatim, without being represented as fresh runs.

## Review by Q160

I checked B--E of delivery-errors against the actual statements and the source proof. Each new node introduces A, all complexes, integer bounds and maps independently, cites the definitions actually used and has no proof steps. The exactness node needs termwise injectivity, not just K-injectivity: I retained that hypothesis. The model node needs a lower bound to invoke K-injectivity and an upper bound for the Hom support estimate; both are termwise bounds and neither is silently replaced by a cohomology bound.

New Step 1 uses only the new model/support statement. I checked that it asserts a derived isomorphism, natural in the source and A-linear by being in D(A), not merely a bijection of underlying sets. Composing QI with the given isomorphism to L and QP with the chosen representative of K is functoriality. Step 2 uses the existing truncation-cohomology statement, which explicitly defines the kernel-valued subcomplex and identifies cohomology through n. The quotient C has zero terms strictly below n; no assertion that C is zero in degree n is made. Finite generation follows from the given finite H^q(K) and zero modules above n.

New Step 3 uses the exactness node with U=T, V=P, W=C and the same I. Every row of 0 to T to P to C to 0 is exact by the quotient construction, so no split-exactness assumption is imported. New Step 4 uses precisely the support clause of the model/support node for C and the existing complex-SES LES node. I opened both statements and checked their conclusions: the former gives zero Hom terms above b-n, the latter gives connecting maps and exactness at all four positions. Since b-n=i-1, H^i and H^(i+1) of the left term both vanish. This is the correct pair for an isomorphism on H^i. The comparison used for P and T is the derived-form comparison already cited in Step 1; applying H^i and the representative isomorphisms is ordinary functoriality, not a separately assumed comparison lemma.

New Step 5 uses the existing bounded-above coherent RHom statement, opened and read in full. It requires a Noetherian commutative ring, finite cohomology of both arguments, an upper cohomology bound u on the first, and a lower cohomology bound v on the second. These are respectively the item assumption, Step 2 and the L assumption, n, and a from I. The node does not require termwise finite generation, so no such hypothesis is added. Transferring module finiteness along the A-linear isomorphism is elementary. All cited statements, not their hidden proofs, are what the steps use; citations.json records them verbatim.

I tested zero ring and zero complexes: every construction and isomorphism is then zero and the short exact sequences remain valid. For a field k, take M=k in degree n and I=k in degree b: Hom has a nonzero term at b-n, so the strict inequality r>b-n is sharp. Taking a=b is allowed. For the exactness node, an empty active diagonal gives the zero exact row; a single active index reduces to injective extension of ordinary module maps. A nonsplit module short exact sequence causes no problem because injectivity, not source splitting, is used. Arbitrarily unbounded P is allowed: fixing r leaves only finitely many target degrees, and no convergence assertion is required. The parent example with K=k in every degree and L=k[0] confirms that K must not be given a hidden boundedness hypothesis.

The correction is structural only: I removed the lengthy implementation arguments from the parent by assigning them to two statement-only tasks, preserved the residual truncation and LES assembly, retained all existing metadata and statement dependencies, and introduced no statement dispute. No non-elementary proof step exceeds 2000 characters; the parent totals 2000. Existing definitions and the bounded-above coherence theorem are not recreated. The two new nodes share the item's unit; the other parent citations are existing Mathlib leaves. No new off-unit tool declaration is needed.

## Not duplicates

- lem-trf-bounded-injective-total-hom-exact vs lem-sf-dualizing-complex-bounded-duality: the existing theorem is bounded coherent biduality/anti-equivalence for a semidualizing target, not a chain-level exactness or injective model/support theorem.
- lem-trf-bounded-injective-total-hom-exact vs lem-trf-bounded-above-coherent-rhom: the existing theorem is finite cohomology and a LOWER bound for coherent bounded-above/bounded-below inputs; it asserts neither exactness nor the arbitrary-source bounded-injective model and UPPER bound.
- lem-trf-bounded-injective-total-hom-exact vs lem-trf-finite-map-dualizing-transfer: the existing theorem transfers dualizing data along a finite ring map and needs coherent Noetherian semidualizing hypotheses, absent here.
- lem-trf-bounded-injective-total-hom-exact vs lem-trf-complete-local-coherent-duality: the existing theorem constructs a dualizing complex and proves biduality over a complete local ring; it supplies neither of these arbitrary-ring complex constructions.
- lem-trf-bounded-injective-total-hom-exact vs lem-trf-source-hyperext-module-target: the existing theorem is a convergent source hyperext spectral sequence with a single module target and bounded-above cohomology source, not either bounded-injective-target assertion.
- lem-trf-bounded-injective-total-hom-exact vs lem-trf-coherent-rhom-finite-injective-dimension: the parent concludes finite generation for coherent inputs over a Noetherian ring; the new node concludes a complex construction over an arbitrary commutative ring and asserts no finite generation.
- lem-trf-bounded-injective-total-hom-exact vs lem-per-algebraic-local-duality: the existing theorem identifies completed Ext with local cohomology duals over a nonzero local ring; neither new construction is that identification.
- lem-trf-bounded-injective-total-hom-exact vs lem-per-algebraic-dualizing-ext-bounds: the existing theorem gives support-dimension bounds for Ext of a finite module into a normalized dualizing complex; the present support is a termwise degree bound, without that normalization or finiteness.
- lem-trf-bounded-injective-total-hom-exact vs lem-per-algebraic-dualizing-quotient: the existing theorem constructs a normalized dualizing complex for a quotient ring, with local and normalization hypotheses; neither new theorem changes rings.
- lem-trf-bounded-injective-rhom-model-support vs lem-sf-dualizing-complex-bounded-duality: the existing theorem is bounded coherent biduality/anti-equivalence for a semidualizing target, not a chain-level exactness or injective model/support theorem.
- lem-trf-bounded-injective-rhom-model-support vs lem-trf-bounded-above-coherent-rhom: the existing theorem is finite cohomology and a LOWER bound for coherent bounded-above/bounded-below inputs; it asserts neither exactness nor the arbitrary-source bounded-injective model and UPPER bound.
- lem-trf-bounded-injective-rhom-model-support vs lem-trf-finite-map-dualizing-transfer: the existing theorem transfers dualizing data along a finite ring map and needs coherent Noetherian semidualizing hypotheses, absent here.
- lem-trf-bounded-injective-rhom-model-support vs lem-trf-complete-local-coherent-duality: the existing theorem constructs a dualizing complex and proves biduality over a complete local ring; it supplies neither of these arbitrary-ring complex constructions.
- lem-trf-bounded-injective-rhom-model-support vs lem-trf-source-hyperext-module-target: the existing theorem is a convergent source hyperext spectral sequence with a single module target and bounded-above cohomology source, not either bounded-injective-target assertion.
- lem-trf-bounded-injective-rhom-model-support vs lem-trf-coherent-rhom-finite-injective-dimension: the parent concludes finite generation for coherent inputs over a Noetherian ring; the new node concludes a complex construction over an arbitrary commutative ring and asserts no finite generation.
- lem-trf-bounded-injective-rhom-model-support vs lem-per-algebraic-local-duality: the existing theorem identifies completed Ext with local cohomology duals over a nonzero local ring; neither new construction is that identification.
- lem-trf-bounded-injective-rhom-model-support vs lem-per-algebraic-dualizing-ext-bounds: the existing theorem gives support-dimension bounds for Ext of a finite module into a normalized dualizing complex; the present support is a termwise degree bound, without that normalization or finiteness.
- lem-trf-bounded-injective-rhom-model-support vs lem-per-algebraic-dualizing-quotient: the existing theorem constructs a normalized dualizing complex for a quotient ring, with local and normalization hypotheses; neither new theorem changes rings.
- lem-trf-bounded-injective-total-hom-exact vs lem-pc-stupid-tail-hom-short-exact: its sources are a degreewise split stupid-tail sequence and a fixed degree term; the new exactness theorem handles arbitrary, possibly nonsplit degreewise short exact rows.
- lem-trf-bounded-injective-total-hom-exact vs lem-pur-kinjective-homotopy-exact-injective-target: it only asserts exactness at the middle group of homotopy-category maps; it does not assert degreewise short exactness of A-module Hom complexes.
- lem-trf-bounded-injective-total-hom-exact vs lem-weil-pbc-module-hom-left-exact: it supplies left exactness for single modules and a finite-free evaluation formula, not total Hom short exactness.
- lem-trf-bounded-injective-total-hom-exact vs lem-sf-bifunctor-homotopy-exact: it is triangulated exactness of a signed bifunctor on the homotopy category, not termwise exactness for an arbitrary nonsplit sequence.
- lem-trf-bounded-injective-total-hom-exact vs lem-weil-pbc-ringed-internal-hom-exact-universes: it gives triangulated exactness in derived categories, which does not assert the actual degreewise short exact sequence of total complexes.
- lem-trf-bounded-injective-rhom-model-support vs lem-sfb-derived-internal-hom-sections-model: its general derived adjoint computation does not include the bounded-injective degree support bound, and its section comparison forgets to abelian groups.
- lem-trf-bounded-injective-rhom-model-support vs lem-sc-derived-hom-finite-free-model-aux: it requires a bounded-above finite-free source and a ringed space; the new model allows an arbitrary source and uses injectivity of the target.
- lem-trf-bounded-injective-rhom-model-support vs lem-weil-pbc-ringed-site-bounded-free-rhom-finite-support: it has source bounded above and target bounded below, the opposite inequalities to this upper bound, and does not compute derived Hom.
- lem-trf-bounded-injective-total-hom-exact vs lem-sc-bounded-hom-exact-columns: it proves acyclicity of exact columns with source bounded above and target bounded below, not short exactness nor the opposite support estimate.
- lem-trf-bounded-injective-total-hom-exact vs def-sc-module-total-hom-complex: it defines the complex but proves neither its contravariant exactness on arbitrary nonsplit rows nor its derived comparison with the support estimate.
- lem-trf-bounded-injective-rhom-model-support vs lem-pod-projective-hom-evaluation-model: it computes RHom using a bounded-above projective SOURCE and an arbitrary target; our source is arbitrary and the TARGET is bounded injective.

## Unfinished work

The two new nodes intentionally remain unsplit for other workers. No required stage-1 argument was omitted. Validation and delivery results are recorded below after the prescribed server dry run.

## Original six-step proof retained verbatim

### Old Step 1

Choose a bounded complex $I$ of injective $A$-modules representing $L$, and integers $a\leq b$ such that $I^q=0$ outside $[a,b]$. Choose any complex $P$ representing $K$. By [lem-weil-pbc-bounded-below-injectives-kinjective], $I$ is K-injective. Thus [def-pur-derived-internal-hom], specialized to the one-object ringed site, computes $R\operatorname{Hom}_A(QM,L)$ by $\operatorname{Hom}_A^\bullet(M,I)$ for every complex $M$, where $Q$ is localization. We use the $A$-module-valued total Hom complex of [def-sc-module-total-hom-complex], so all subsequent maps and cohomology isomorphisms are $A$-linear.

Uses: lem-weil-pbc-bounded-below-injectives-kinjective, def-pur-derived-internal-hom, def-sc-module-total-hom-complex

### Old Step 2

Fix $i\in\mathbf Z$ and put $n=b-i+1$. Let $T=\tau_{\leq n}P$ be the subcomplex with $T^q=P^q$ for $q<n$, $T^n=\ker(d_P^n)$, and zero terms above $n$; put $C=P/T$. By [lem-weil-pbc-truncation-cohomology], $H^q(T)\cong H^q(K)$ for $q\leq n$ and $H^q(T)=0$ for $q>n$. Hence all cohomology modules of $T$ are finitely generated. Directly from this quotient, $C^q=0$ for $q<n$. In particular $0\to T\to P\to C\to0$ is short exact in every degree.

Uses: lem-weil-pbc-truncation-cohomology

### Old Step 3

For $r>b-n$, every factor $\operatorname{Hom}_A(C^p,I^{p+r})$ is zero: if $p<n$ then $C^p=0$, while if $p\geq n$ then $p+r>b$ and $I^{p+r}=0$. The formula in [def-sc-module-total-hom-complex] therefore gives $\operatorname{Hom}_A^r(C,I)=0$ for $r>b-n$. Since $b-n=i-1$, its cohomology in degrees $i$ and $i+1$ is zero.

Uses: def-sc-module-total-hom-complex

### Old Step 4

Apply total Hom into $I$ to the short exact sequence of Step 2. For each $p,r$, restriction $\operatorname{Hom}_A(P^p,I^{p+r})\to\operatorname{Hom}_A(T^p,I^{p+r})$ is surjective by the extension property defining injectivity in [def-sp-injective-resolutions]; its kernel consists exactly of maps factoring through $C^p$. In a fixed degree $r$, only the finitely many indices $a-r\leq p\leq b-r$ can contribute. Taking their product preserves this exactness by choosing one lift per factor. Precomposition commutes with the Hom differential [def-sc-module-total-hom-complex]. Consequently $0\to\operatorname{Hom}_A^\bullet(C,I)\to\operatorname{Hom}_A^\bullet(P,I)\to\operatorname{Hom}_A^\bullet(T,I)\to0$ is a degreewise short exact sequence of complexes of $A$-modules.

Uses: def-sp-injective-resolutions, def-sc-module-total-hom-complex

### Old Step 5

The long exact cohomology sequence [lem-weil-pbc-complex-ses-homology-long-exact] applied to Step 4 has the segment $H^i\operatorname{Hom}_A^\bullet(C,I)\to H^i\operatorname{Hom}_A^\bullet(P,I)\to H^i\operatorname{Hom}_A^\bullet(T,I)\to H^{i+1}\operatorname{Hom}_A^\bullet(C,I)$. The two outer modules vanish by Step 3, so the middle map is an isomorphism. By Step 1 this identifies $H^iR\operatorname{Hom}_A(K,L)$ with $H^iR\operatorname{Hom}_A(QT,L)$.

Uses: lem-weil-pbc-complex-ses-homology-long-exact

### Old Step 6

Apply [lem-trf-bounded-above-coherent-rhom] to $QT$ and $L$, with upper bound $u=n$ and lower bound $v=a$. Step 2 verifies bounded-above finitely generated cohomology for $QT$. The chosen representative $I$ verifies $H^q(L)=0$ for $q<a$, and finite generation of all $H^q(L)$ is a hypothesis of the item. The cited lemma makes $H^iR\operatorname{Hom}_A(QT,L)$ finitely generated. Step 5 transfers finite generation to $H^iR\operatorname{Hom}_A(K,L)$. Since $i$ was arbitrary, this proves the assertion without a bound on $K$.

Uses: lem-trf-bounded-above-coherent-rhom

## Validation

The preliminary server `review_split` check passed. The full required `deliver.py Q160 lem-trf-coherent-rhom-finite-injective-dimension --no-push` exited 0 and printed `OK (not pushed)` with preflight passed at `78a1a542857`. Also read `sites-cohomology.tex`, Tag 08J7, `section-internal-hom`, where an arbitrary source representative and a K-injective target compute the derived internal Hom as an actual complex of module sheaves. Read `injectives.tex`, `lemma-characterize-K-injective`, at the successor step and its Hom-complex transition-map argument; it confirms why termwise injectivity supplies surjectivity, while the existing homotopy exactness node states less than the new short-exact-complex assertion. No JSON changed after the successful dry run.
