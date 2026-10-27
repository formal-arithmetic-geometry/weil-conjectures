# Worker report: lem-sp-tower-reduction-transpose

## Files written

- `dag/nodes/sec-smooth-purity/lem-sp-tower-reduction-transpose.json`: statement, split into five steps; no exact Mathlib match.
- `citations.json`: eleven literal statement quotations, one for every step/node citation.
- `report.md`: this report. `searches.jsonl` is the search command's own log.

New nodes: 0. Mathlib leaves: 0. The item's statement and statement dependencies are unchanged. No Lean, compiler or git command was run; all worker writes are confined to this sandbox.

## Attachments

None. Searched the actual project `lean/WeilConjectures/` for the blueprint tag, tower reduction, transposition, coefficient counits and semilinear transitions. The source files found concern adic reconstruction, matrix towers or ordinary finite adjunction infrastructure; none states this item with its actual strict derived tower morphism, arbitrary finite extension and prescribed comparisons.

## WANTED

None: the proof is an agent argument following the newest blueprint Levels paragraph, using statements already in the DAG. No outside source or SGA reference is used.

## Findings and corrections

The imported item is mathematically consistent. The blueprint's final Levels sentence says coefficient maps agree by chart descriptions and uniqueness. That does not itself identify the global transpose of the actual tower reduction: equality of local derived maps need not detect equality globally. The split supplies the global naturality equation instead. It cites the already-existing normalized shriek transition theorem for the substantive compactification comparison. It does not repeat gluing or evaluated representability, which are assumptions of this item and would introduce a cycle through its ancestor.

The tower is not assumed normalized. The full uniform cohomological lower bound ensures it belongs to the bounded-below domain of the transition theorem: exact evaluations commute with cohomology and a tower of zero cohomology sheaves is zero. The coefficient quotient is not assumed flat. The finite scalar-extension theorem supplies the ctf test object needed to use the representing bijection.

## Not duplicates

No new node was created. Whole-DAG keyword searches and blueprint searches for `reduction transpose`, `semilinear direct image`, `reduction counit`, `transition comparison`, `counit transpose`, and `shriek normalized transition` found no same-statement blueprint node. `det-sp-tower-exceptional-bc`, the result returned for `counit transpose`, concerns an actual geometric base-change square and assumes the tower adjunction; it is neither this reduction argument nor an admissible replacement for it. Reused `lem-sp-shriek-normalized-transition-comparison`, rather than creating another compact-support transition node.

## Mathlib search reading

All new search records were imported from the actual command's searches.jsonl, retaining their exact tools and queries. Two LeanFinder phrasings returned condensed counits, site-level pushforward counits and exponentiable-morphism composition. Read the sheaf pushforward counit formula in `Mathlib/Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean:303`: it concerns a sheaf and a site adjunction, not the ordinary derived strict coefficient tower compactification comparison. LeanSearch returned Kan extension counits and `CategoryTheory.Adjunction.derivedε`; read the derived counit construction in `Mathlib/CategoryTheory/Functor/Derived/Adjunction.lean:118`, which constructs an abstract localized counit without the required tower transition theorem. Loogle's second query found `CategoryTheory.Adjunction.homEquiv_naturality_right`; read the Hom equivalence and inverse counit formula in `Mathlib/CategoryTheory/Adjunction/Basic.lean:161`. These explain the elementary uniqueness calculation, but the item also needs the actual reduction of compact support. Grep for tower/counit and exceptional/reduction combinations had no hits; grep for the Hom equivalence formulas confirmed the infrastructure. Consequently the item remains a split, rather than a Mathlib leaf. Older inherited search records were preserved.

## Review by Q90

Read SETUP's chapter/unit/node levels, GOAL, the worker/stage-1 instructions, and delivery-errors B through E in both the original and merged copies. Read the chapter and unit records. Read the current blueprint through `literature/blueprint/latest`, resolving to main-20261024 at ef6f9619fdbffa59e88528fb56483d76c70258c8, particularly det-sp-tower-gluing's full proof and its Levels paragraph. Also read the latest exceptional coefficient comparison proof, scalar-extension statement, coefficient-towers statement, direct-image coefficient statement and integral direct-image tower proof's paragraph (1). No new node needs an independent literature source. The proof_origin is correctly agent because the global naturality calculation fills in a justification omitted by the blueprint, itself agent-written.

Step 1 uses the explicit ell-to-uniformizer equality in det-sp-tower-shriek-levels and the finite quotient clause in def-weil-l-adic-coefficient-extension. These really give the equality of quotient ideals and finiteness needed; the unital quotient and common annihilator follow directly. The hypotheses are positive indices, finite E and prime ell. No unramifiedness is used.

Step 2 reads the statements of det-sp-coefficient-towers-abelian, lem-sp-shriek-normalized-transition-comparison, det-sp-scalar-extension-functor and det-sp-reduction-direct-image. The first gives exact evaluation and levelwise kernels/cokernels; the lower-bound argument is written explicitly. The transition theorem states precisely F_m(r_G) composed with the *specified* b, not merely an unspecified isomorphism. Its field, separated finite-type schemes, fixed compactification, bounded-below domain and constructible finite-Tor levels all hold here. Its dependency graph does not use this item or det-sp-tower-gluing. Scalar extension supplies preservation of ctf even for nonflat quotients, and direct-image reduction makes that b invertible. This is the single non-elementary step, with every substantive input cited.

Step 3 uses the naturality clause of det-sp-coefficient-towers-abelian on the actual derived tower morphism epsilon. The displayed square is ordinary naturality, and cancellation of the invertible b gives exactly the stated global equality. It needs neither joint faithfulness of evaluations nor equality detection by a cover. Both source and target are explicitly checked.

Step 4 reads the counit-transpose defining equation and uniqueness in det-sp-reduction-exceptional and the naturality of b in det-sp-reduction-direct-image. It writes the transported map with both iota factors, replaces evaluated counits using their counit-preserving property, and compares its transpose with the candidate H_m(r_K)c. Naturality of a counit is part of the stipulated adjunction; injectivity is part of its bijection. The domain T H_n K_n is ctf by Step 2 and iota_n, so this is a legitimate test object, even though its reduction to G_m need not be invertible. Smoothness and pure relative dimension are exactly the finite exceptional comparison's hypotheses. This is an elementary substitution into the cited equations, not a new lemma or a claim that the scalar comparison is an adjunction unit.

Step 5 reads the composition clause of det-sp-coefficient-towers-abelian and the natural associator/unitor clause of det-sp-scalar-extension-functor. It starts from the actual reduction cocycle and substitutes the already proved formula, so it does not apply det-sp-reduction-compatibilities, whose present field hypotheses are narrower. Equal indices give the ordinary identity transition and its tensor unitor. For triples the explicit equation includes the scalar associator, and the intervening iota factors cancel by naturality. This proves coherence for the actual reductions in question without a further coefficient-comparison theorem or an assumption that transitions are isomorphisms.

Checked small cases: X empty gives zero maps and the zero representing object; d=0 and f the identity reduce to naturality of r_K; m=n gives identities; repeated indices in a triple reduce to unit constraints. For E=Q_ell the rings are Z/ell^s; for ramified E the exponents are es, without changing the common annihilator. Non-normalized towers, including zero transition maps, satisfy the same square and injectivity argument. At no point is A_m treated as perfect over A_n. No new statement, duplicate, hollow definition or restated clause was introduced. All proof steps are under 2000 characters; none hides a new lemma. The eleven citation quotations were checked as literal substrings of the cited node *statements*. The off-unit compactification transition theorem is declared as a generic tool in split_report.tool_uses: it identifies the compact-support operation independently of the current unit's representing-pair construction.

## Unfinished work

None in the stage-1 split. Independent maintainer review and future formalization remain the project's subsequent stages.
