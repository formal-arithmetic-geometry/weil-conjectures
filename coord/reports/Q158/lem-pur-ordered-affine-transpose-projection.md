# Q158: lem-pur-ordered-affine-transpose-projection

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-ordered-affine-transpose-projection.json`: existing statement node, now split into six proof steps; no exact Mathlib match.
- `citations.json`: 31 verbatim statement excerpts, one for every step/node citation.
- `searches.jsonl`: actual searches run with the required msearch command.
- `report.md`: this report. `prepare.py` is a sandbox-only preparation script.

New nodes: 0. New Mathlib leaves: 0. All ingredients were already present in the DAG. There was no previous sandbox node or report to continue. The item statement, statement dependencies, source, creation provenance and blueprint ancestry are unchanged. The blueprint-wide searches for ordered affine and projection tensor found no exact replacement for the item.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag, ordered affine/tower comparisons, transpose/projection, affine-space trace/projection, and integration. No project declaration states the complete item. Mathlib's composite counit and mate-counit identities are useful tools already represented by existing DAG nodes; they do not state this geometric claim.

## WANTED

None.

## Problems found and changes

The original item was statement-only, with no proof. The ancestor blueprint proof's Steps 1-2 describe an ordered reassociation, while Steps 3-4 infer coordinate invariance from even shifts alone. This item needs no coordinate invariance; its statement explicitly excludes that assumption. I realized the ordered route and its extracted counit/projection obligation rather than using the permutation sentence. No statement correction or change of route was necessary.

A tempting proof would cite a general projection-coherence slogan without checking the actual transformation or coefficient domain. I replaced that with the existing `lem-pur-projection-formula-coefficient-coherence`, which explicitly uses the same two tensor symmetries, and `lem-sf-composition-projection-mate`, which explicitly identifies the geometric compact-support compositor and projection maps. The intermediate source is H = T_g tensor Rf_!T_f. Bounded constructibility of that source is explicitly justified by `prop-finite-compact-support-constructibility` and tensoring with a shifted rank-one line; its finite Tor amplitude is not assumed. The projection theorem requires the base coefficient K to have finite Tor amplitude, which is available.

The coefficient I_{m+1} is not chosen separately or identified by fibrewise normalization: the induction calculates J, then specialization at the coefficient unit identifies J with the defined transpose I_{m+1}. This avoids a uniqueness assertion for maps out of an arbitrary complex.

## Unfinished work

None at this stage. The item uses existing statement nodes as stage-1 dependencies, without claiming their Lean proofs are complete. No Lean was written and no compiler, Lake, build, or local DAG validation tool was run.

## Not duplicates

No new nodes were created, so there are no new/existing same-tag pairs to justify. I searched the full DAG and blueprint before considering a helper. The existing coefficient-associativity and composition-projection nodes already supply the needed helpers, so I reused them.

## Review by Q158

I read the item, its current parent `prop-pur-affine-space-composition-law`, the current blueprint proof at `main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-composition/prop-pur-affine-space-composition-law.proof.md`, and the chapter/unit records, especially `sk-prop-an` Step 6. The blueprint proof is agent-written, so I marked this proof's origin as agent. I also read Stacks `more-etale.tex`, Tag 0F7J (`lemma-shriek-composition`), including its compatible-compactification construction. It explains the geometric compositor used here; its ordinary-etale statement is not silently treated as an unrestricted pro-etale theorem. The class-restricted pro-etale assertion is the separately cited DAG statement. Mathlib `Adjunction/Basic.lean` lines 567-587 and `Adjunction/Mates.lean` lines 123-132 confirm the pasted counit and conjugate-counit formulas. There are no new nodes needing independent literature sources.

For step 1 I opened and read each of the nine cited node statements. The ordered-comparison definition gives the polynomial projections, Tate-line comparisons, and etale representatives. `lem-sf-pullback-tor-amplitude` preserves ctf under pullback, and the two clauses of `lem-sf-tensor-ctf` give the bounded and finite-Tor tensor assertions. `thm-sf-preservation-class` explicitly preserves ctf under exceptional pullback for the separated finite-type field-base morphisms here. `lem-sf-proetale-constructible-origin` supplies origin witnesses for bounded constructible complexes. `thm-sf-comp-composition` preserves the bounded-below origin class. The compact-support constructibility node applies over the field k with ell invertible. `thm-sf-ambient-adjoint-class` supplies only the natural bounded-below Hom bijection used. The finite compact projection theorem includes precisely the pro-etale realization clause and needs finite Tor amplitude only of the base coefficient. I checked its source and base roles separately, including H above.

For step 2 I read the two comparison definitions, the natural Hom bijection, the four-clause mate-pasting statement, the conjugate definition, and the inverse-transpose identity. The line comparison is natural because its defining projection/trace composite and the Hom bijection are natural; the ordered recursion preserves that naturality. Writing u = Gamma_g, the equality Gamma_f Rf^!(u) is used in its correctly typed form Gamma_{f,Rg^!K} F_f(u) = Rf^!(u) Gamma_{f,F_gK}. The composite counit is epsilon_g Rg_!(epsilon_f); naturality of epsilon_f moves Rf^!(u) through it. The resulting expression is exactly tau_g Rg_!(tau_f), not merely a map with those endpoints. The conjugate convention matches c:R(gf)^! -> Rf^!Rg^!. No general ambient pro-etale adjunction is used.

For step 3 I checked the coefficient-coherence lemma's explicit formula against the Pi formula in the line definition: both use symmetry inside Rf_!, inverse canonical PF, then symmetry outside. Its coefficient-associativity identity includes the pullback tensor comparison and associators. The composition-projection node gives the normalized actual PF equality and is valid on arbitrary ambient finite inputs; after restricting to the present inputs I may invert the required components. I also read the compatible-compactification triangle statement: the field schemes here are quasi-compact and quasi-separated and both arrows are separated finite type, so it applies. The compact-support composition theorem identifies the canonical comparisons and includes identity laws. These are tool uses, declared in split_report, not a replacement of the ordered-affine route.

For step 4 I checked the zero-length definition Gamma_0 = id and the identity-adjunction convention. The inverse-transpose identity recovers precisely a_M from its adjunct Gamma_1,M. The inverse-projection unit equation, rather than an assertion about abstract isomorphic sources, identifies I_1 with the specified normalized integration. This works over each intermediate base, so it is a valid base case for the induction.

For step 5 I used only the already proved block calculation, the line base case, the induction hypothesis for g, and the two explicit PF identities. With f a line, g of length m, U = Rf_!T_f, and d = 1_{T_g} tensor I_f, coefficient associativity at f first extracts Lg^*K and leaves the coefficient T_g. Naturality at g for d then moves the remaining coefficient map outside the inverse projection. The composition identity identifies the remaining two inverse projections with Pi_{m+1,K}. This gives J = I_g Rg_!(d pi_{f;T_g,T_f}) and the actual formula tau_{m+1,K} = (1_K tensor J) Pi_{m+1,K}. All source reassociations match the definition's last-coordinate recursion. No tensor symmetry of coordinate blocks is asserted.

For step 6 specialization at K = A and the explicit unit equation identify J with tau_{m+1,A}, namely I_{m+1}. This is a short elementary substitution, not a new theorem hidden as a node. Together with the independent two-block calculation it covers every clause.

I checked small cases: m = 0 has only unit constraints; m = 1 recovers the defined affine-line trace; m = 2 has the two counits in the order epsilon_g Rg_!(epsilon_f), not the opposite order; zero-length f or g removes the corresponding identity adjunction. K = 0 and the empty base give the unique relevant zero maps, while K = A gives exactly the coefficient-extraction equality used in the induction. No field assumption on the finite coefficient ring was used, so ramified E and n > 1 cause no change. All Tate shifts are even, but the argument does not infer geometric symmetry from that observation.

Against delivery-errors B-E: there are no new unsplit nodes, no unintroduced auxiliary objects, no fabricated searches, no clause moved into a new node, and no source tag used in lieu of a node citation. I checked every citation directly against the cited statement and stored a verbatim excerpt. The induction has its quantified hypothesis, base cases and successor written explicitly. I checked the full dependency reach for cycles back to this item, including the coherence and constructibility tools. Every proof step is under 2000 characters. No hidden comparison argument remains: the comparison assertions needed are precisely the existing coefficient-coherence and composition-projection statements.

The first dry run required citation excerpts to contain at least 40 characters. I expanded the short excerpts to their full surrounding statement paragraphs, preserving verbatim text; the cited nodes and proof arguments did not change.
