## New nodes

None. The item reuses existing DAG statements only.

## Dependency modules

None. This is a stage-1 natural-language split with no Lean modules.

## Attachments

No sorry-free declaration in `WeilConjectures/` states this item exactly. The existing `lem-asd-ordinary-finite-p1-adjunction` is a stronger neighboring-route statement, but it is not an attachment and does not replace this item's prescribed diagonal-integral proof.

## WANTED

None. The archived blueprint source is available at `literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/thm-amb-p1-adjunction.md` in the reference checkout `/home/ubuntu/work-bp/sheaf`.

## Source error

The imported target statement was ill-typed as written: it used `A`, `S`, `P`, and `q` without introducing them, and it did not state the finite torsion and invertibility hypotheses needed by the cited trace and proper-base-change nodes. I corrected it by introducing `N`, finite commutative `A` with `NA=0`, Noetherian `S` with `N` invertible, `P=\mathbf P^1_S`, and `q`, while retaining the whole unbounded ordinary étale categories and the exact counit from `def-amb-p1-trace`. This is the context of the archived proof and of `lem-asd-ordinary-finite-p1-adjunction`.

## Not duplicates

`thm-amb-p1-adjunction` vs `lem-asd-ordinary-finite-p1-adjunction`: the latter is a broader ordinary-étale interface theorem that additionally proves the decomposition, trace normalization, and base-change compatibility for arbitrary finite coefficients; this item is the diagonal-kernel adjunction node and follows its own unit route through `lem-amb-p1-diagonal-integrals`.

## Review by NZ

I read the item’s archived blueprint source and the unit/chapter records, then opened every cited dependency statement. Step 1 uses the direct-image composition statement for the identity `p₂ ∘ Δ`, the diagonal-integral statement for the supported class `δ`, the proper projection formula for `Δ` and `p₂`, and the unbounded finite-torsion proper-base-change statement; these provide exactly the identifications used in the displayed construction of `η`. Step 2 uses the trace definition, whose statement gives `t_q` and the canonical projection-formula composite defining `ε`, together with the same projection formula for its source. Step 3 uses direct-image composition, proper projection, proper base change, and the exchange/tensor coherence statement to rewrite the first triangle, and uses the decomposition statement’s explicit arbitrary-base compatibility plus the trace definition to identify `t_{p₁}` with the pullback of `t_q`. Step 4 applies the `a=1` clause of the diagonal-integral statement verbatim. Steps 5–6 use the proper projection and exchange/tensor coherence statements to pull out the common coefficient and identify the second triangle with `t_{p₂} ∘ R(p₂)_*δ`; step 6 then applies the `a=2` clause verbatim. Step 7 is the elementary unit/counit triangle criterion.

I checked the hypotheses: `def-amb-p1-trace` supplies finite `A` killed by `N`, Noetherian `S`, `N` invertible, the ordinary étale derived categories, and the twist; projective-line and diagonal properness make the cited projection/base-change statements applicable. I tested the corrected context at `N=1` (the zero coefficient ring gives zero derived categories and the unique adjunction) and at a field base with `A=\mathbf Z/N`; no edge case changes the statement. I also ran the required LeanFinder, Loogle, Mathlib grep, and LeanSearch queries for the item; the first three found only generic sheaf/projective-spectrum adjunctions, and LeanSearch was unavailable. No new node was needed, so there are no new-node Mathlib records or additional source citations.

The only correction was the missing target context and the expansion of the imported five-paragraph proof into seven explicit steps with all non-elementary dependencies cited. Generic exchange/tensor coherence and unbounded proper base change are declared as tool uses because they are categorical tools outside the compact-support CBC unit route; they do not replace the diagonal-integral route.

## Second reading by NZ

- Item statement: checked against the archived blueprint node `thm-amb-p1-adjunction` and the full `def-amb-p1-trace` context; the introduced (N,A,S,P,q), finite torsion, Noetherian, and invertibility hypotheses are retained exactly, and the conclusion is the adjunction on the entire unbounded ordinary étale derived categories.
- Step 1: checked against the construction paragraph of `thm-amb-p1-adjunction.md` and the statements of direct-image composition, diagonal integrals, proper projection, torsion proper base change, projective-space properness, proper stability, proper-morphism definition, closed-immersion properness, and finite-type-over-Noetherian. The missing properness, separatedness, finite-type, and Noetherian checks are now explicit.
- Step 2: checked against the trace-definition paragraph and the projection-formula statement; it uses exactly the displayed inverse projection map and tensor-unit composite.
- Step 3: checked against the first-triangle paragraph and every cited statement, including decomposition base-change compatibility and the exchange/tensor coherence; the two coordinate identifications and the (p_1)-trace pullback are stated explicitly.
- Step 4: checked against the (a=1) clause of `lem-amb-p1-diagonal-integrals`; the reduction to that clause is direct.
- Step 5: checked against the second-triangle paragraph, proper projection, exchange/tensor coherence, and the trace definition; the common coefficient and the even-shift Koszul sign are accounted for.
- Step 6: checked against the (a=2) clause of `lem-amb-p1-diagonal-integrals`; it gives the second triangle identity.
- Step 7: checked against the standard unit/counit triangle criterion; it is an elementary categorical conclusion from the preceding two identities.
- New nodes: none; all dependencies were re-opened in `dag/nodes`, and no new statement is needed.
- Edge cases: (N=1) gives the zero coefficient ring and the unique adjunction; a field base with (A=\mathbf Z/N) has the stated projective-line trace; the empty base is harmless. The argument does not exclude zero objects or unbounded complexes.
- Changes made: expanded Step 1 with the properness/separatedness/Noetherian hypotheses needed by the cited projection and base-change results; added the corresponding exact citation quotes; retained the worker's corrected target context and seven-step diagonal proof.
