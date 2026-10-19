# Worker report — Q129

## Files written

- `dag/nodes/sec-six-functors/lem-coef-operadic-minimal-interval-reflection.json`: statement item, split in eight steps; not a Mathlib leaf. No new nodes and no Mathlib leaves created.
- `citations.json`: exact statement quotations for every cited node in each step.
- `report.md`: this report. `repair.py` is an item-local scratch transformation, not delivery content.

## Attachments

None. Searched both read-only `WeilConjectures/` trees by the exact blueprint tag and by operadic, minimal interval, interval reflection and reflection. The reflection hits concern Day reflection or Fourier inversion, not this item. No project declaration supplies all of this item's clauses. The upstream master sorry declarations were not treated as completed proofs.

## Wanted sources

WANTED: an archived copy of Gepner–Haugseng, *Enriched infinity-categories via nonsymmetric infinity-operads*, arXiv:1312.3178, Appendix A.6 and Erratum E.0.2, for lem-coef-operadic-minimal-interval-reflection.

WANTED: an archived copy of Lurie's *Higher Topos Theory*, 2.4.4.3 and 5.2.4.2 with their opposites, for the existing cocartesian mapping-square and pointwise adjoint inputs. These sources remain external, so the proof is attributed to the agent.

## Corrections and limitations

The existing sandbox split was retained and repaired after interruption. Its statement was identical to the repository's statement and remains so. Its provenance had incorrectly been overwritten to say the item created itself: restored the repository's Q104/active-lift-criterion `created` record. The repository's search history was retained, and the actual Q129 queries and second phrasing from `searches.jsonl` were reused; no search was invented or repeated. The ordinary `CategoryTheory.reflector` and `reflectorAdjunction` declarations at `Mathlib/CategoryTheory/Adjunction/Reflective.lean:38-54` require an existing ordinary `Reflective` structure. They do not construct this quasicategorical operadic reflector. The other logged hits concern nerves/coskeleta, ordinal factorizations, model-category factorizations, horn multicoforks or strict Segal extensions. None is an exact match or one-line specialization.

The old proof wrongly said that r=0 makes q an identity and makes R an identity on the relevant data. Counterexample to that proof assertion: n=1, k=0, phi(0)=0, and A with inert interval [0,1]. The restriction is the opposite of [0]→[1] selecting 0, not an identity. Step 8 corrects this without changing the item: r=0 is supported by the genuine inert lift axiom, including vertex selectors. This is a proof error, not a disputed statement. The earlier draft also treated the definition of a homotopy fiber as a theorem computing factorization mapping spaces; the repaired Step 4 derives that formula from existing slice/coslice/fibration theorems instead.

The cited arXiv source was opened online, specifically Definition A.6.1, Proposition A.6.3 and Erratum E.0.2. A.6.3 and E.0.2 state the weak-approximation criterion; they do not print this reflector theorem or its detailed proof. The source fields explicitly distinguish our expanded prerequisite from those stated propositions. No Stacks tag states this infinity-operadic assertion. No SGA source is used.

## Blueprint and duplicate searches

Read the chapter `sec-six-functors` and unit `sk-prop-sf-biduality-general` records, including their route and realized fields. This is a prerequisite under the finite-coefficient adjunction paragraph of `prop-coef-integral-exceptional-adjoint`, not a key-unit statement, so no unit file was written. The existing ancestor and via chain were preserved. `tools/blueprint_refs.py ancestor` identifies that same ancestor. Whole-blueprint searches for “operadic minimal interval reflection”, “minimal interval” and “cocartesian” found no imported blueprint node stating this item. DAG searches found the item, its active-lift user and related interval/operadic machinery; none replaces this statement. No new node was made, so there are no new-versus-existing duplicate pairs to list.

## Review by Q129

I read the source passages listed above and every statement named by the repaired proof, with the repository and sandbox item open together. The statement is retained word for word: g is an inert-preserving categorical fibration, M is generalized, O is an ordinary nonsymmetric infinity operad (not an ordinary 1-category), alpha is arbitrary, comparison edges are unrestricted, r=0 is allowed, and no weak-contractibility assumption enters. The discrete base used in the proof is N(Delta^op), not O. The four statement dependencies define the objects and adjunction data actually used. I did not change any target, unit, chapter, imported flag, blueprint ancestry or upstream source.

Step 1 uses the factorization definition's triangle and the operadic definition of an inert interval to obtain phi=J psi. Injectivity and the inequalities t≤a≤b≤t+m are direct ordinal calculations; no non-elementary fact is hidden there.

Step 2 uses the generalized-operad inert-lift clause, which explicitly supplies a cocartesian lift even for a singleton interval. The existing cocartesian mapping-square statement applies to the inner fibration p_M, with targets C and prescribed opposite base map psi_0. Because maps in N(Delta^op) are discrete, restricting its pullback square to this base component yields the asserted equivalence and contractible space of factorizations. Only this consequence of cocartesianness is used, not any lifting-category contractibility assumption about g.

Step 3 uses g's stipulated inert preservation and the existing cocartesian composition/cancellation statement to conclude that gamma_0 is inert. The factorization definition supplies exactly the coherent triangle and compatibility required for an object and edge of F. The identity J ell(v)=a+v verifies membership in A_0. Merely lying over an inert base arrow is never substituted for cocartesianness.

Step 4 uses `lem-coef-infinity-slice-right-fibration` for S and T and `lem-cbc-relative-coslice-left-fibration` for T_{alpha/}→T. Pullback of its left-horn lifting property is checked explicitly. `lem-coef-infinity-relative-cone-equivalence` supplies opposite-category mapping-space/slice duality, so the right-fibration morphism-space theorem gives the left-fibration mapping-fiber formula over S. That statement explicitly retains higher homotopies and compatibility with pullbacks. The cone mapping-fiber clause of `lem-cbc-enhanced-functor-cone-calculus`, specialized to a single-object diagram, computes the slice mapping spaces; `lem-coef-infinity-slice-arrow-equivalence` identifies its arrow-pullback slice with the join slice actually defined by the item. These statements supply the identifications the old draft had left unsupported. Fullness alone identifies F and A_0 mapping spaces with their ambient mapping spaces.

Step 5 explicitly proves the forced base map u=ell from Ju(v)=a+v, so it does not assume comparison h is inert. The two applications of the mapping-square statement use the same cocartesian q, with targets D_B and C. `lem-coef-kan-homotopy-pullback-invariance` states that weak equivalences on the three entries induce a weak equivalence on their path-pullback spaces; it therefore licenses the fibers at beta_0 and beta, after their chosen triangle identifies these basepoints. Composition homotopies are retained.

Step 6 takes the further fiber at gamma_B. Its two target spaces are literally the same Map_T(alpha,g beta_B), and the compatibility triangle from Step 3 identifies the maps into it. The same homotopy-pullback-invariance statement applies. Step 4's natural mapping-fiber formula ensures naturality in B and all higher simplices. Thus the result is a natural mapping-space equivalence, not an assertion about component sets.

Step 7 uses the dual clause of `lem-coef-infinity-pointwise-adjoint-criterion`. That statement explicitly assembles representing objects and universal arrows into a functor, unit/counit and coherent triangle identities, which match `def-coef-coherent-adjunction-data`; the latter is not cited as an existence theorem. When A is minimal, ell is the identity and we may take q=id, so fullness identifies the representative with B. The elementary inverse-comparison argument proves the counit is an equivalence. No new theorem restating this clause was created.

Step 8 checks the zero-length interval correctly, the n=0 case, the active-arrow case (the whole interval is forced), and the empty factorization category case. No extra hypotheses were introduced. The counterexample above was the correction made during this review. Every proof step is below 2000 characters; I nevertheless checked Step 4's two mapping-space identifications against their cited statements rather than treating its length as proof of adequacy.

The three off-unit proof inputs are declared in `split_report.tool_uses`: the general cone mapping-fiber theorem, relative coslice left-fibration theorem, and right-fibration mapping-space theorem. They are generic tools for the displayed model's mapping-space calculation. They do not replace the unit's adjunction route; no node of this unit states these same inputs. Every other statement input is in the item's unit. Definitions introduce notions only. I checked the B–E error list against these uses: no new unsplit proofs, no clause relabelled as a new node, no weak-contractibility assumption smuggled in, no citation used for a stronger assertion than its statement, and no source download or Lean/compiler work.

## Unfinished work

None in the stage-1 split. The cited prerequisite nodes retain their independent stage-1 status; this delivery does not assert that Lean proofs exist for them. Server validation and direct delivery are the final operational checks.
