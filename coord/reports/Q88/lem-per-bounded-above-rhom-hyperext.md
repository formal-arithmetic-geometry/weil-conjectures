# Stage-1 delivery: lem-per-bounded-above-rhom-hyperext

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-bounded-above-rhom-hyperext.json`: existing statement, split into nine proof steps. Statement and statement dependencies unchanged. No new nodes and no new Mathlib leaves.
- `citations.json`: one record for every step/dependency pair, quoting the actual cited statement.
- `searches.jsonl`: genuine msearch.py output; the existing item's earlier searches were retained and the current searches appended to its record.

## Attachments

None. Searches of the project declarations under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint tag, hyper-Ext spellings, and bounded internal Hom/spectral-sequence terminology found no declaration asserting this item. The project's Grothendieck spectral sequence has two left exact functors of abelian categories and does not assert this internal-Hom spectral sequence for a complex first argument. Reference declarations in upstream master were not treated as finished proofs.

## Wanted literature

None. I read Stacks derived.tex Tag 015W (lemma-ss-filtered-derived) and Tag 08J5 (remark-truncation-distinguished-triangle), sites-cohomology.tex Tags 0A94/0A95 (local Hom and well-definedness) and 08JC (triangles), sites-modules.tex Tag 03EI (exact module sheafification), and homology.tex Tags 011Q/011R/011S/011T and 0BDU/0BDV. I also read the first proof paragraph of ILO XVII Proposition 10.1.1 on printed p. 325: its Ext-continuity-to-representable-direct-sums inference is the parent's use of this item. The Postnikov/exact-couple expansion here is agent-written, not falsely attributed to a direct specialization of 015W.

## Problems found and changes

The item was statement-only. Its hypotheses and conclusion are correct; there is no statement dispute. A tempting incorrect citation would have been `thm-sp-truncation-e2`: that theorem treats a derived left exact functor of the heart, whereas RHom from an arbitrary bounded-above complex need not be such a functor. Another tempting mismatch is `lem-sf-hom-triangulated`, which only states the etale constant-coefficient case. I use neither. Instead, the existing local K-injective Hom comparison plus exact module sheafification supplies the needed cohomological functors on the arbitrary ringed site. This avoids adding generalizations or restatements as new nodes.

The proof introduces the actual exact couple, shifts the first index by r to meet every hypothesis of the existing half-plane theorem, and identifies its initial abutment with the required one by an explicit tail calculation. In particular, it does not infer convergence merely from finite diagonal support, and does not require a completeness assumption on the site's derived category. No chapter/unit route, source statement, coefficient category or target was changed.

## Unfinished work

None in this one-level split. Dependencies are existing DAG nodes; their own proof states are preserved. No Lean was written and no compiler, Lake or build command was run.

## Not duplicates

No new nodes. The blueprint-wide searches for spectral sequences and internal Hom confirmed that the closest imported statement `thm-sp-truncation-e2` assumes a left exact functor between Grothendieck hearts, and `thm-sp-spectral-object-yields` assumes an actual bounded filtered complex. Neither is the present arbitrary bounded-above first-argument statement. I reused `thm-sp-half-plane-convergence`, `lem-sp-derived-couple-exact`, `lem-sp-couple-morphism`, `lem-weil-pbc-truncation-triangle`, `lem-sf-derived-truncation-triangle`, `lem-pur-rhom-into-kinjective-local`, `lem-pur-site-restriction-module-adjunction-exact`, `lem-weil-pbc-hom-into-triangle-exact`, `lem-weil-pbc-ringed-site-module-sheafification-exact` and the right-argument shift theorem instead of creating duplicates. Blueprint same_as remains empty.

## Review by Q88

I read the chapter and unit records before writing the proof and checked the inherited ancestry under `lem-per-artin-gabber-affine-curve`. This is a formal tool supporting the relative-duality coefficient chain, specifically the parent `lem-per-constructible-rhom-coproduct-continuity` Step 3, through ILO XVII 10.1.1. It leaves the unit's perverse/Fourier route in place. All off-unit theorem uses are declared in split_report.tool_uses as formal tools; definitions and Mathlib leaves are notions/tools in their own right.

I opened the statement of every one of the 17 proof dependencies, not just its title. For Step 1, `def-pur-derived-internal-hom` supplies the K-injective Hom-complex model, `lem-pur-rhom-into-kinjective-local` explicitly sends a cocycle f to Q_U(f), and exact module sheafification preserves the kernel/image quotient. Applying the local lemma to P[-n], not shifting both arguments, gives degree n. The resulting sheafification identification is just those statements plus the signed shift formula and definitions; it is written out, not made into a new node. This check also explains its naturality under restriction and postcomposition.

For Step 2, the cited restriction statement is about modules over an arbitrary sheaf of commutative rings, not just abelian or etale sheaves. Exactness preserves both support bounds. The standard t-structure definition identifies those bounds with D^{<=r} and D^{>=b-n}, and the cited t-structure orthogonality gives zero exactly when n<b-r. Thus the whole lower-bound argument is three applications of already cited statements; no flatness or finite Tor condition is hidden.

For Step 3, `lem-weil-pbc-hom-into-triangle-exact` really states covariant representable exactness in any pretriangulated category. Rotating and shifting gives all three exactness positions. Exact restriction commutes with the cone's finite direct sum, so it preserves the distinguished triangle in the local derived category. Exact sheafification gives the sequence of module sheaves. I wrote the boundary as postcomposition with w[n], and checked naturality by a[1]w=w'c, rather than claiming compatibility without an equation.

For Step 4, I checked `lem-weil-pbc-truncation-triangle` gives the successive truncations and cohomology term with the actual functorial boundary, and that `def-sp-exact-couple` uses alpha of degree (-1,1), f of degree (2,-1), g of degree (0,0). Each of its exactness equations is the appropriate segment of Step 3. `lem-sp-derived-couple-exact` explicitly supplies the iterated couples and d_s of degree (s,1-s), so no spectral-sequence existence lemma is being smuggled in from a definition alone.

For Step 5, `lem-pur-derived-internal-hom-shift-right` is for all small ringed sites and all derived objects, without extra bounds. It gives the E2 identification with Ext^p(K,H^qL); its shift [-q] changes cohomology p+q to p. I checked vanishing at both p<-r and q<c, and that all D terms vanish for q<c, since the standard truncation is then acyclic.

For Step 6, I substituted P=p+r, Q=q and N=n+r into the actual statement of `thm-sp-half-plane-convergence`. Its required D=0 for Q<c and E=0 for P<0 or Q<c were proved in Step 5. This substitution retains the structure-map degrees, gives the finite range c<=q<=n+r and the uniform stabilization bound s>max(q-c+1,p+r). The cited theorem really supplies the finite filtration and stable-page graded identification; I do not take those from a definition.

For Step 7, the standard truncation triangle supplied by `lem-sf-derived-truncation-triangle` has tail in D^{>=n+r+1}. Step 2 then kills T^{n-1} and T^n of that tail, giving the isomorphism induced by the actual truncation inclusion. I checked both neighboring degrees, not just degree n. For Step 8, I transported the half-plane theorem's image filtration along that natural isomorphism. Its terms are exactly the displayed images of T^n(tau_{<=n-p}L); when p+r<0, the same tail calculation identifies the bigger truncation. Thus the full and zero ends are F^{-r}=H^n and F^{n-c+1}=0, with the requested graded pieces.

For Step 9, `lem-sp-couple-morphism` explicitly includes the abutment-filtration and associated-graded compatibility for couples satisfying the half-plane hypotheses. It applies after the same index translation. The natural truncation maps make its conjugated abutment map T^n(u). Additivity is checked on the initial local Hom maps and then by the unique image/kernel/quotient factorizations at every page and filtration step; it is not silently inferred from mere functoriality.

I tested K=0, L=0, a sheaf in degree r against a sheaf in degree c, the regular sheaf K=O[0], and shifts K=F[t]. In the single-degree test, p>=-r and q=c imply the bottom degree c-r, with equality allowed. For K=F[t], r=-t and the bottom bound is c+t, consistent with RHom(F[t],L)=RHom(F,L)[-t]. Negative r,c work under the same index translation. If n+r<c, the diagonal and filtration have empty support and the abutment vanishes. No constructibility, cohomological-dimension or enough-points hypothesis enters the argument.

B1-B9 add no new-node obligations, since none is created; the existing searches and provenance were retained. The fresh searches were all run with msearch.py and their actual hits read. Generic Mathlib spectral-object and Ext results require additional construction and do not make the item a Mathlib leaf. C1/C4 were checked as above and citations.json quotes every used statement verbatim. I audited the dependency closure (225 existing nodes) and found no path back to the item. D1-D5 hold: all nine steps carry the proof, with nothing moved into a restatement node. E1-E7 were checked through the hypotheses, sign/index arithmetic, explicit boundaries and tail calculation above. Every step is below 2000 characters, and the short comparison and support arguments are direct consequences of the cited statements. There is no SGA citation and no change to the statement.
