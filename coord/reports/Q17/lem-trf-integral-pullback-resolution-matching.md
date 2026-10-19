# Delivery report: lem-trf-integral-pullback-resolution-matching

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-integral-pullback-resolution-matching.json`: repair of returned head `732e5d1ff0`, replacing the incorrect three-step argument with seven steps. Existing project statement, not a Mathlib leaf. No new nodes; no Mathlib leaves created.
- `citations.json`: an exact statement excerpt for every node cited in every proof step.

Attachments: none. Searches in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` by the blueprint tag, inverse-image/pullback terminology, resolution-matching spellings and cone/counit terminology did not find a declaration proving this identity. The upstream master source is reference material, not evidence of a closed proof.

WANTED: none.

## What was wrong and what changed

The earlier split treated the comparison defining κ as though it were a strict cone on the original C_k tower. It is instead a cone on the pullback of the reduction tower of a separate K-flat resolution of M. The previous report's assertion that the blueprint proves the counit identity was also wrong: the main-20261015 Global powers paragraph, lines 35–47, supplies only the motivating naturality. This repair is explicitly an agent-written expansion using the normalized construction in the existing comparison node and the cited Stacks results.

I compared the retained sandbox item with the current shared-repository item: the current item remains unsplit, with the same mathematical statement and ancestry and no finished-proof audit. I retained the prior searches and their actual results, retained the blueprint ancestry and provenance, and replaced the defective proof and review. The delivery tool rebuilds the delivery on its current base; no git command was run in the shared repository. The original returned node and report are retained under sandbox `work/` for comparison. No `review.md` is present in this item's sandbox; the full return is in `coord/returns/Q17.md`, and I followed every mathematical repair instruction in that entry.

The one statement clarification is the return's B2 fix: explicitly fix the prime ℓ, the finite extension E, its valuation ring, uniformizer and all A_{E,n}, and add `def-weil-l-adic-coefficient-extension` to `stmt_deps`. This supplies the already intended coefficient data and changes no hypothesis or conclusion of the displayed identity. There is no statement dispute.

## Review by Q17

I read the current item, its parent's Step 4, the chapter and unit records, the three blueprint levels in SETUP.md, the Global powers paragraph in the current main-20261015 source, and delivery-errors B–E in full. For the repaired proof I opened the complete statement of every dependency, including definitions of the integral operations and inverse-image comparison. I read Stacks `derived.tex`, Tags 0FND/0DVC (the functorial derived-adjunction formula), and `sites-cohomology.tex`, Tags 0941 (K-injective tower limits and the normalized cone comparison), 06YY (K-flat derived change of rings), and 07A6 (derived adjunction). I also read `sites-modules.tex`, Tag 03CZ (sheaf extension/restriction adjunction); Tag 03D6 is used for the module inverse-image formula. There are no new-node sources to audit and no SGA source is used.

Step 1 uses `def-pur-integral-derived-operations` to choose the actual flat-term K-flat resolution P′ of M and its quotient tower B. Part (b) of `def-weil-inverse-image-pullback-comparison` states precisely that κ is its compatible cone lift, precomposed with the inverse class of H(q). I now keep C_h=h*B distinct from D=h*C_k. Nothing identifies H(P′) with H(lim I), and no iterated-pullback compositor occurs in the argument.

Step 2 uses `lem-weil-tower-category-levelwise-abelian` for the abelian category and exactness of Δ, `lem-weil-pbc-ringed-strict-tower-homotopy-limit` for the total derived limit on that category, and the characterizing formula and two-variable functoriality of `lem-pc-pre-derived-adjoint-functors-general`. Those statements supply derived counit naturality for an arbitrary derived tower arrow, not merely a strict map. The normalization of `lem-trf-integral-pullback-comparison-realization` identifies that counit with the one in the item. Exact Δ supplies its left derived functor; the cited tower theorem supplies the everywhere-defined right derived functor. These verify the derived-adjunction hypotheses.

Step 3 applies `lem-weil-pbc-diagram-site-realization` with the small index category N_{≥1}^op. The variable quotient ring is a sheaf on this same site because coverings stay at a fixed level. Thus `lem-pur-derived-change-of-rings`, which allows an arbitrary small ringed site and arbitrary ring-sheaf map, applies to ΔR→S_• on the entire diagram. The explicit acyclicity test using `def-pc-kflat-complex` and levelwise exactness proves that ΔP′ is K-flat, so its actual derived reduction is B. Restriction is exact from its unchanged underlying sheaves (`def-pc-sheaf-restrict-scalars`). I write the underived adjunction formulas and their inverse directly from `def-pur-sheaf-tensor-product`; these are compatible with sheafification and all transitions. The fraction formula of the general derived-adjunction node then identifies the unit with r:ΔP′→B. This proves the whole-diagram adjunct identity without assuming equality can be detected by evaluations.

Step 4 defines φ as the adjunct of ε_C∘Δ[q]. The statement of `lem-trf-integral-pullback-comparison-realization` expressly defines η by applying h* to this counit-derived change-of-rings/action arrow and realizing it. This gives η=Rlim(h*φ). The adjunct formula from Step 3 gives φ∘r=ε_C∘Δ[q]. The K-flat computation is supported by `lem-pur-derived-change-of-rings`; I do not attribute an adjunction theorem to that node alone. These are equalities of derived diagram morphisms; φ need not be a chain map on the given complexes.

Step 5 checks the exact-products hypothesis using `lem-weil-proetale-countable-products-exact`, then uses `lem-weil-strict-roos-comparison` to identify the concrete cone of part (b) of the comparison definition with the K-injective-computed derived limit under exactly the required normalization. Only now is `lem-trf-integral-cone-counit-realization` applied, and only to C_h and its strict compatible θ. It yields ε_{C_h} Δ(r_θ)=θ. The statement does not require finite Tor-amplitude, boundedness of these resolutions, or a common resolution with C_k.

Step 6 proves naturality of u by the actual finite formula x↦x⊗1 in part (a) of the comparison definition. Both strict composites send x to v(x)⊗1 and commute with all transitions. Exactness of H is in that definition; exact finite h* is in the integral-operations definition. Levelwise exactness then permits passage to the derived quotient diagram. I explicitly pass the strict naturality square through a roof, so its application to φ is justified. Composing with H(r) and using Step 4 yields the required equality with u_C H(ε_C) ΔH(q), without comparing arbitrary derived morphisms by their evaluations.

Step 7 is only substitution of the preceding equalities: use counit naturality for h*φ, then the cone identity on C_h, then naturality of u and the adjunct identity. Cancel the invertible class of ΔH(q), which is invertible because H is exact. This is a derived tower equality before realization or reduction. I inspected every step for hidden independent lemmas and long arguments: all seven are below 2000 characters. The local diagram-site and roof calculations are explicitly written, not delegated to unnamed standard comparisons.

I checked the small cases: if N=0, φ, θ and all asserted composites are zero. If h is the identity, u is the tensor-unit identification, and the calculation becomes the counit naturality/adjunct identity for an arbitrary resolution P′. A degree-zero constant coefficient complex and its actual quotient maps give the same tensor-unit calculation. None of these tests assumes the finite reductions are flat, and none uses faithful detection by reductions. The repaired proof works for the unbounded K-flat resolutions actually allowed by the definitions.

## Return points repaired

1. E4: κ is now defined on H(P′), with target the cone of C_h=h*B, and H(q) is retained until the final cancellation.
2. C4: removed `lem-weil-pbc-proetale-derived-pullback-composition` from every proof step and `proof_deps`. Its inherited statement reference merely specifies finite pullback terminology; it supplies no step of this proof.
3. E5: the missing compatibility is proved by the change-of-rings adjunct identity, derived counit naturality, and an explicit tensor-unit naturality square on roofs. No componentwise detection claim remains.
4. C3/C4: the cone-counit lemma is applied to r_θ into Rlim C_h. η is kept as Rlim(h*φ), and counit naturality accounts for it.
5. D3: the generic tools supplying derived adjunction, K-injective strict limits, diagram-site realization, K-flat change of rings, exact products and the normalized Roos comparison are explicitly cited and declared in `split_report.tool_uses`. These are tools for the existing Global powers route, not replacements of it.
6. B2: fixed all coefficient data explicitly and added its definition to statement dependencies.

## Searches and duplicates

No new node was introduced. I reused the existing generic tools after DAG/blueprint searches, including searches for change of rings and strict towers. No node duplicates a clause of this item. The original four recorded item searches and their logged results remain; I also made a second phrasing with LeanFinder, a valid Loogle counit-name query, and a grep for derived counits and counit naturality. Generic derived adjunction and counit declarations are tools, not a one-line specialization to the prescribed pro-etale whole-quotient-diagram comparison. Exact queries and outcomes are recorded in the node and `searches.jsonl`; unavailable services, if any, are marked unavailable.

Nothing remains mathematically unfinished in this one-level split. Independent maintainer review remains the delivery gate after the required server dry run.
