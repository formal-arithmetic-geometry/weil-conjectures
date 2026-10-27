## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-strict-log-differentials-pushout.json`: statement item, now split into nine explicit steps; no Mathlib match.
- `citations.json`: 16 step/node entries, checked verbatim against the current cited statements.
- `report.md`: this report. Search-command records are retained in `searches.jsonl`.

No new nodes and no new Mathlib leaves. The sandbox initially contained no node, proof, report or search log; the live item was copied before editing. No repository or Lean source file was changed. The helper `write_split.py` is sandbox scratch work, not a delivery file.

## Attachments

None. Searched `lean/WeilConjectures/` for the item id, logarithmic differentials and log-structure names. The logarithmic hits concern power series, zeta functions and logarithmic derivatives, not this statement. No exact project declaration exists to attach. The item has no upstream declaration recorded.

## Wanted literature

WANTED: Kato (1988), *Logarithmic structures of Fontaine–Illusie*, sections 1 and 3, for lem-per-strict-log-differentials-pushout (associated logification and logarithmic differentials). No Kato file was found among the supplied literature. I did not download it. The proof is explicitly marked agent-written.

## Audit and corrections

The item statement is unchanged. There is no statement dispute. Its source already says that the pushout formula is agent-formulated, and that ILO does not state it verbatim. I read ILO VI 1.1, printed p.69 (PDF p.75), X proof of Proposition 1.2, printed p.138 (PDF p.144), and XVI Proposition 3.6.3, printed p.252 (PDF p.258). VI gives the etale-site and chart conventions; X uses a strict chart map to compare logarithmic differentials; XVI discusses a basis of logarithmic differentials and log-smooth charts. None is misrepresented as a proof of the present pushout formula. In particular ILO's usual locally Noetherian convention is not used to limit or justify our arbitrary-scheme assertion.

The latest blueprint ancestor `lem-per-artin-gabber-affine-curve.md` has a statement but no proof text. I read it and the latest unit file; the inherited `blueprint.from.place` records the older Step 3 duality/cosupport location and its downstream strict chart comparison. This split stays below that comparison and does not replace the unit route. Searches `blueprint_refs.py search logarithmic` and `search pushout`, and DAG searches for associated logification, logarithmic derivations and pushouts, found no other blueprint statement of this item. The item retains `same_as: []`.

The ordinary Mathlib candidates were read at `Mathlib/RingTheory/Kaehler/TensorProduct.lean:224-231` and `Mathlib/Algebra/Category/ModuleCat/Differentials/Presheaf.lean:190-215`. `KaehlerDifferential.isBaseChange` assumes a pushout of rings; it does not handle monoid log structures or their logarithmic differential symbols. The presheaf construction also treats ordinary differentials only. Logged searches include two distinct LeanFinder phrasings, LeanSearch, Loogle and source grep; all returned successfully. The broad grep was capped at ordinary analytic logarithmic hits, so a second grep specifically in AlgebraicGeometry was run and returned no hits. These are no-match verdicts, not unavailable-service verdicts; the preexisting search history in the live item was preserved.

I did not cite `lem-trf-associated-log-universal-stalks`: it assumes locally Noetherian schemes and only a global constant monoid input, whereas the present prelog input is the sheaf `c^{-1}M` on an arbitrary scheme. Steps 1–2 instead write out the associated-log construction using the general monoid-sheafification theorem. Nor did I assume that equality in the associated log sheaf is equality of chosen pairs before sheafification: Step 6 checks the extra local equality issue.

## Unfinished work

None in the mathematical split. Server validation results are recorded below.

## Not duplicates

No new nodes were created, so there are no new/existing-node pairs to distinguish. The generated-congruence and unit computations are steps rather than extra nodes. Existing monoid sheafification and local-representatives statements are cited directly.

## Review by Q131

I checked B–E with the item, all seven proof-cited node statements, and the source passages open. There are no new nodes requiring a source/statement comparison, no unsplit-node proofs, and no proof step over 2000 characters. Every mathematical TeX command uses one backslash after JSON decoding. The statement dependencies continue to introduce the ordinary differential sheaf, its etale realization, sheaf tensor product, module-sheaf quotient and the log/chart conventions that the statement explicitly names.

For Step 1, `def-weil-size-convention` supplies a small skeleton in a common enlarged universe. `lem-trf-commutative-monoid-sheafification` states both the monoid adjunction and agreement of underlying-set sheafification. This applies to Q because its restriction maps preserve the displayed generating congruence. I checked Stacks Tag 00YR, `section-sheaves-algebraic-structures`, especially (beta), (gamma), (epsilon), in sites.tex. This is an existing Mathlib leaf, so it supplies a generic tool without a new off-unit route.

For Step 2, `lem-weil-pbc-site-sheafification-sections-local` states local representatives and local equality, not merely full faithfulness. It supplies precisely the local representatives used to verify that a section of Q-sharp with unit image is the unique corresponding unit. I checked Tag 00WK, `lemma-sections-sheafification`, in sites.tex. The rest of the step explicitly proves the universal extension formula into any log structure K and then uses strictness. The cited monoid adjunction extends that formula; no global chart or Noetherian hypothesis enters. The local-representatives node is Lean-closed and the monoid node is Mathlib, so neither needs an off-unit declaration in split_report.tool_uses.

For Step 3, `def-weil-pbc-kahler-differentials` actually states the generators-and-relations construction and universal derivation, and `def-sc-relative-differential-sheaf` gives the restriction-compatible sheaf form. `def-pur-sheaf-tensor-product` gives the sheafified tensor presentation, and `def-weil-sheaf-of-modules-category` states cokernels are sheafifications of sectionwise cokernels, so quotient maps can be defined from the displayed annihilation of (u,-v). I checked its Tag 03DA, `lemma-abelian`, in sites-modules.tex. Preservation of the logarithmic structural relation and of base-vanishing follows directly from c being a morphism over (S,N); it is not imported from a definition node without calculation.

Step 4 uses only the tensor and ordinary differential definitions plus the quotient relation q_B u = q_C v. Its displayed equation establishes D(beta(h)) = beta(h) ell(h), with each map correctly typed. I corrected the notation from an implicit image inside q_B to q_B u explicitly. In particular it never assumes beta(h) invertible for general h, or injectivity of u or v. The additive and Leibniz identities and the base vanishings come from the given symbol relations.

Step 5 is elementary: multiplication of units and Leibniz give lambda(tt') = lambda(t) + lambda(t'), and inversion is used only for beta(e), e in E. The displayed equality then checks every generating relation (he,t) ~ (h,beta(e)t), hence their generated congruence. This argument is not moved into a new node duplicating a clause of the item.

For Step 6 I verified that the target (P,+) is a commutative-monoid sheaf because P is a module sheaf, as the cited module-sheaf statement says. The monoid-sheafification adjunction extends Q -> P, and the cited local-equality statement verifies independence after sheafification as well as before it. Restriction compatibility follows from the formula in existing sheaf maps; no claim about underlying global sections of a quotient is used.

Step 7 explicitly checks the structural relation by the Leibniz equation D(beta(h)t). Monoid additivity is supplied by Step 6, and the image of N is represented by (g-flat n,1), so it is killed. Together with Step 4, these verify every relation in the item definition of omega_gc; the induced module map is thus the elementary map from its presentation, not an application of an uncited log-differential theorem.

Step 8 checks both composites. The nontrivial ordinary generator from C is fixed because q_B d(c-sharp a) = q_C(1 tensor da), exactly the quotient relation. For a general log section I checked the local factorization into the image of H and a unit, and dt = t dlog t. The tensor and module-sheaf definitions cited here justify checking locally on these generating symbols. Step 9 writes the pushout universal property directly for an arbitrary target module sheaf, using the cited cokernel description; it does not assume a categorical pushout comparison theorem.

Small-case checks: for c = identity, A -> B is identity and the quotient is omega_g; for all log structures trivial, every dlog unit becomes its ordinary t^{-1}dt, giving B as required. For the strict reduction Spec(k) -> Spec(k[x]) at x = 0 with chart N -> k[x], 1 -> x, and trivial base, the relation dx = x dlog x restricts to zero on both sides and dlog x survives, exactly as the formula predicts; the proof therefore does not divide by a vanishing log parameter or tacitly require flatness. On the empty scheme every sheaf concerned is zero. These checks are consistent with retaining arbitrary schemes and making no smoothness, flatness, finite-presentation or Noetherian assumption.

All 16 citation quotes were checked as literal substrings of the current cited node statements. The server review_split check passed with zero new nodes before the final dry run.

## Validation and delivery

- Server `review_split`: PASS, zero new nodes, agent-written proof.
- Full dry run: `OK (not pushed)`, server preflight passed, receipt commit `f68db4f809d`. The final report update is checked again before pushing.
