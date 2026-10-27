# Q36 stage-1 delivery: lem-pur-adic-trace-transpose-coefficient-calculus

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-adic-trace-transpose-coefficient-calculus.json`: statement, split; nine proof steps, seven existing dependencies, unchanged statement and statement dependencies. The full statement has no Mathlib match.
- `citations.json`: one verbatim statement extract for each step/dependency pair.
- `report.md`: this report. `searches.jsonl` is the unmodified search-command log; `prepare.py` is sandbox-only preparation code.

There are no new nodes and no new Mathlib leaves. Existing nodes suffice, so there is no statement-only auxiliary theorem to create. No unit or chapter record is changed: this item is not the unit's key statement.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint id and for trace/transpose terminology. The trace-transpose hits in ZetaLinearAlgebra and WeilSheaf concern ordinary linear algebra, while PoincareDuality concerns another adjunction pairing; none states every clause of this integral coefficient-calculus lemma. The affine-space purity source explicitly does not construct the trace-transpose family. No finished exact attachment was found. The current item contains no upstream Lean declaration record to attach.

## WANTED

None. This is explicitly agent-written auxiliary categorical reasoning, not a theorem attributed to an unavailable reference. Sources used are present locally.

## Problems found and repairs

The item had a statement and searches but no proof. Its assumptions already include the canonical projection-intertwining compact-support comparison, tensor-normalized source comparison, a compatible trace family and the two shift hypotheses. I retained the statement verbatim and supplied the calculations that these assumptions require. In particular, I did not infer equality of integral maps from equality of reductions, did not assume arbitrary mates of isomorphisms invertible, and did not introduce finite-level normalization of the traces.

The inherited search results were retained. Six additional searches ran through the prescribed `msearch.py`, and their exact tool/query pairs and actual logged answers were appended to the item. The initial trace phrasing mainly found linear-algebra trace lemmas; the second categorical phrasing found abstract mate calculus. I read `Mathlib/CategoryTheory/Adjunction/Mates.lean`, especially `mateEquiv_counit` at line 123 and `mateEquiv_vcomp` at line 170, `CategoryTheory/Shift/Adjunction.lean` around lines 75-120, and `CategoryTheory/Triangulated/Adjunction.lean` around lines 44-65. These are tools already represented in the DAG, not a one-line realization of the entire geometric statement.

## Not duplicates

No new-node/existing-node pairs arise. Whole-DAG keyword searches and whole-blueprint searches for adjunction mates, coefficient calculus, pasted mates, transpose coefficient and projection trace were read. In particular, I reused `lem-sfb-pasted-mates-counit-normalization`, `def-weil-pbc-adjunction-mate`, `lem-weil-pbc-adjunction-shift-compatibility-unique` and `lem-sf-triangulated-right-adjoint` instead of creating specialized copies. The existing `lem-sf-mate` only concerns geometric composition, and `lem-sfb-coherent-right-adjoint-comparisons` compares left adjoints between fixed categories; neither is misused for a coefficient square with distinct categories.

## Review by Q36

I read the chapter and unit records, the old transport sketch `literature/blueprint/master/blueprint/sec-smooth-purity/sk-thm-purity-transport/_section.md` Steps 2-3, and the main-20261015 transport sketch and `thm-pur-rational-and-qbar-purity.proof.md`, especially Step 2. They require finite-stage independence. The argument below supplies that missing formal compatibility rather than replacing diagonal purity by another geometric proof. I also read the scalar-naturality parent statement and its assembly proof, and the source `det-prop-scalar-six-direct-image.proof.md`, whose formal-properties paragraph motivates pasted mates. That paragraph alone would not prove this item, so the proof origin is agent. For exactness I read Stacks `derived.tex`, Tag 0A8D, label `lemma-adjoint-is-exact`, and the more precise Mathlib theorem with specified compatible shifts. No SGA source is used.

I opened and read the statement of each of the seven proof dependencies and checked the following applications against it:

1. The mate definition gives the natural transformation associated to the inverse compact-support square with exactly the required counit transpose. The projection theorem gives a natural isomorphism on constructible/finite-Tor inputs. These, with the stipulated exceptional adjunction, yield naturality of gamma and the counit identities; no purity inverse is used.
2. The compact-support coefficient-comparison statement explicitly intertwines projection transformations, not just underlying functors. I wrote the square using the tensor comparison v, the map r and the first-variable map q. Its source is C_Y(P_E T_E tensor K), and its target is P_F(T_F tensor L_F C_Y K). Naturality of the projection theorem allows q. Inverting the two projection maps is legitimate; inverting t is not needed. The stated trace equation gives the last equality.
3. The canonical normalization of a and j identifies r C_X(j) with j_F a; this uses precisely the assumed tensor associator, symmetry and unit equations. Naturality of the same c at j yields the displayed tilde-u equation. This is a short substitution, so it is an elementary step, not a new coherence node.
4. The two inverse adjunction transposes are explicitly computed. Naturality of c at gamma, then the counit identity from Step 1, reduces the left transpose to C_Y(tilde u)c^{-1}. Step 3 gives the right transpose. The mate definition provides the bijection, so equality is detected by this transpose. It is not detected by reductions.
5. The pasted-mates statement permits arbitrary categories, arbitrary functors and noninvertible mates. Its three adjunctions here are the supplied exceptional adjunctions, its two squares are c^{-1}, its input arrow is the identity, and its output arrow is the tensor associator on Y. I checked every source and target. The resulting transpose is written before cancellation. Inverting the existing c composition equation and using naturality of alpha at epsilon gives the transpose of the other side, exactly as displayed. This dependency is declared as a generic off-unit tool in split_report.tool_uses; it supplies no replacement geometric route.
6. The compact-support statement has an identity-extension clause. Hence the defining transpose is epsilon itself, whose adjunct is the identity. There is no assumption that the trace is the identity.
7. The item's explicit shift hypotheses imply the shift equation for the transpose of u. The reassociation j crosses the extra [1] past the even [2d], giving (-1)^(2d)=1. I did not cite the separately unproved projection-shift theorem, since those hypotheses are already assumed here.
8. The existing adjunction-shift leaf supplies coherent compatible shifts; its counit characterization agrees with the one specified in the item. The derived-change-of-rings statement supplies exact tensor functors and their shifts; the c statement explicitly commutes with shifts. Therefore h=C_Y(epsilon)c^{-1} shifts to h[1], and the two inverse transposes are equal. The displayed counit calculation proves the b shift clause without assuming b invertible.
9. When gamma is invertible, its square solves for b as a composite of gamma_F, a and C_X(gamma_E^{-1}), so b is invertible. The exact-right-adjoint leaf applies because P_E is the given exact functor and its adjunction shifts are compatible. Exactness of G_E actually follows independently of gamma's invertibility; this stronger observation changes no statement. Componentwise equality of the natural transformations from Step 1 gives equality as transformations; the previously proved equations and the assumed equations for a supply all requested coherences.

The domain checks use the item's supplied exceptional adjunction on the full finite-Tor categories. Thus G_EK is an allowed input of c when its counit mate is formed. The tensor unit twisted and shifted by (d)[2d] is in the same domain; K is finite-Tor, so the projection inverses in Steps 1-3 are typed. Finite extensions are always between fields inside the fixed closure; the existing c statement covers ramified extensions and its actual tensor associator, so no unramifiedness is silently added. The global base and separated finite-type assumptions are unchanged.

Small cases checked: K=0 and empty X give zero composites; d=0 gives the unit reassociation with sign +1; F=E gives b=1 even for zero trace. For three equal coefficient fields, Step 5 reduces to the identity equation. Arbitrary zero traces make gamma zero but leave the coefficient and shift equations valid, showing why invertibility is only used in the final clause. The three-field calculation allows noninvertible b throughout. No statement dispute was found.

I checked B1-B10, C1-C8, D1-D5 and E1-E7 of delivery-errors.md against the actual statements and sources. There are no new definitions, hidden elementary helper nodes, new clauses disguised as lemmas, circular dependencies introduced, unlogged searches or silently strengthened assumptions. Each non-elementary step cites the theorem it uses; citations.json records literal extracts. All nine steps are under 2000 characters; the longest is the explicit three-adjunction calculation, 1063 characters. No long hidden lemma is being retained.

## Unfinished work

None in this stage-1 item. This delivery proves the conditional calculus, not construction or invertibility of the geometric traces, which are tasks of the parent and its other dependencies.

## Validation

The required server dry run exited successfully: `OK (not pushed) deliver/Q36/lem-pur-adic-trace-transpose-coefficient-calculus at b7b7560a2cb: preflight passed`. Server preflight includes check_dag.py and review_split.py. No Lean was written or compiled. The final report update is revalidated before pushing.
