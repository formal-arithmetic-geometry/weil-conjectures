# Q41: lem-coef-infinity-iterated-slice-mapping

## Files written

- `dag/nodes/sec-six-functors/lem-coef-infinity-iterated-slice-mapping.json`: existing statement, now split in six steps; Mathlib verdict no match for the quasicategorical assertion. Statement unchanged. Statement dependencies now also include the existing coherent slice/arrow presentation.
- `citations.json`: one entry for every citation of every step, quoting the cited statement verbatim.
- No new nodes, no Mathlib leaves, no unit edits, no Lean edits, and no compilation.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint id and for iterated slices, quasicategories and homotopy fibers. The iteratedSlice occurrences in the presheaf internal-Hom file and MorphismProperty comma file concern ordinary categories. They do not state this item's higher mapping-space assertion. The upstream master source was also searched as read-only reference, not treated as proof evidence.

## WANTED

WANTED: archived Kerodon Proposition 7.7.3.19 (05V1), Corollary 4.6.4.20 (02VT), and Proposition 3.4.1.11 (0110), for lem-coef-infinity-iterated-slice-mapping. I read these online. These are Kerodon tags, not Stacks tags. The item remains agent-origin: its source already says 05V1 is contextual rather than a verbatim statement of the formula. No SGA source is used.

## Issues found and repaired

The inherited statement is valid; there is no STATEMENT-DISPUTED and no change of hypotheses or conclusion. The imported source is a contextual reference, not a proof: 05V1 characterizes local cartesian closure using pullback right adjoints, whereas this item assumes neither pullbacks nor adjoints. I did not import either hypothesis into the proof. The existing def-cbc-enhanced-diagrams-cones specifies mapping spaces, Kan path fibers and the coherent comma construction but does not itself state the slice mapping formula. The proof now cites the actual cone/comma mapping statements for that formula and the existing slice/arrow equivalence for the slice presentation.

The sandbox contained only searches.jsonl and brief markers after the interruptions. There was no draft split, report, delivery receipt, or active delivery process for this item. I retained and read the recorded search results and added the searches actually run in this continuation; no previous delivery mutation was repeated.

## Not duplicates

There are no new nodes. Searches over the whole DAG by the words homotopy fiber, slice mapping, fiber base change, and by Kerodon 0110/010S found the existing lem-coef-infinity-homotopy-pullback-pasting. It supplies exactly the required general cancellation/pasting result; a new composable-homotopy-fiber lemma would be unnecessary. Blueprint searches for homotopy fiber, homotopy pullback, iterated slice, slice, and 0110 found no blueprint assertion of the item. The inherited nearest blueprint ancestor is prop-coef-integral-exceptional-adjoint; its paragraph 2 is the finite mapping-complex adjunction before taking R lim. The six steps expand the inherited space-base-change foundation beneath that paragraph, without replacing a unit's route.

## Mathlib searches

The saved searches were exploratory searches for a generic fiber-base-change or fiber-of-fibers assertion; I read their recorded names. This continuation ran a second fiber-base-change phrasing through LeanFinder and LeanSearch, both of which returned ordinary fibrations and path-object composition results. A namespace-only Loogle query was rejected as an unknown identifier and is explicitly inconclusive, not evidence of absence. The later valid `"homotopy", "pullback"` Loogle query returned no hits; the AlgebraicTopology grep returned none.

For the item itself I ran the iterated-slice mapping-space phrasing through LeanFinder, Loogle for CategoryTheory.Over.iteratedSliceEquiv, and grep for iteratedSliceEquiv in CategoryTheory/Comma/Over. I read Mathlib/CategoryTheory/Comma/Over/Basic.lean:359-387, especially the declaration at line 382. It works with ordinary categories, hom sets and equality in triangles. It does not specialize in one line to arbitrary quasicategories with full higher compatibilities. All queries retained in the node are exact queries in the inherited item or in this sandbox's actual search log. No new leaf is claimed.

## Review by Q41

I read the item, the chapter and unit records, the ancestor's proof in the 2026-10-15 blueprint, and the full statements of every cited node. The unit is sk-prop-sf-biduality-general and this is a foundation under the integral-exceptional-adjoint ancestor; its unit statement and route are not changed. The generic cone calculus is in another unit, so its use is declared in split_report.tool_uses with the precise reason. The other statement dependencies belong to this item's unit.

For source checks I read online Kerodon 05V1, 02VT, 0110, and the supporting 010S fiber criterion. 02VT compares the join slice and arrow slice; 0110 gives right-square cancellation and pasting. The proof uses the existing DAG versions, including the specified-homotopy extension of pasting, rather than pretending Kerodon states every coherence clause verbatim. No new node needs a separate source check.

Step 1 uses def-cbc-enhanced-diagrams-cones only for the specified internal Fun and mapping/fiber conventions. lem-coef-infinity-slice-arrow-equivalence actually states an equivalence over the source category, with an explicit slice diagonal. lem-cbc-enhanced-functor-cone-calculus actually says that functor equivalences induce equivalences on mapping spaces, and states the natural cone mapping-space formula. At K=point its cone category is exactly the arrow slice: this is a degreewise substitution in the definition, not an appeal to an unquoted slice theorem. The containing universe can be enlarged; no assumption of finite limits is introduced.

Step 2 applies that same mapping formula inside the slice. The cone-calculus statement supplies that cone categories are quasicategories, so the iterated application has its hypothesis. The base point is the whole specified triangle tilde q, not merely its underlying arrow or its component.

Step 3 uses the actual formula of lem-coef-infinity-comma-mapping-pullback with the right-hand category equal to a point. The point's mapping space is a point, so the displayed homotopy pullback is the needed homotopy fiber. Its statement explicitly includes endpoint compatibility, naturality in cospans, and composition by pasting coherent squares; those are what identify the postcomposition map by tilde p with the induced fiber map. In particular the two chosen composition triangles are retained as paths and comparison homotopies. The source's ordinary comma-category formula would not have sufficed here, and no strict associative law for the chosen right-pinched representatives is asserted.

Step 4 gives the whole two-square diagram: top U_b to V_b to point, bottom U to V to W. Both the right square and outer rectangle are homotopy pullbacks by their path-fiber definitions. The specified left homotopy is the one whose paste is the outer universal path. The statement of lem-coef-infinity-homotopy-pullback-pasting includes precisely that specified-homotopy setting, so cancellation gives the left square. This is a citation of its statement, not the construction hidden inside its proof.

Step 5 applies the same node to top H to U_b to U and bottom point to V_b to V. The left square is the defining fiber square, the right square is Step 4, and the bottom composite picks q. Pasting makes the outer comparison to hofib_q(g) an equivalence. Thus the substance is the two explicit pasting applications; it has not been transferred to a new node restating the conclusion. Its underlying comparison keeps the arrow and A-compatibility and deletes the B-compatibility.

Step 6 checks that very comparison, not an arbitrary inverse to an equivalence. Restricting a simplex restricts each of its comma coordinates. The internal-Fun identity is checked by transposition out of K times Delta^n, so restriction in K also commutes. The comma node's naturality and composition-by-pasting clauses give coherence in objects and in chosen triangles. A coherent change of a composite is a coherent family of precisely these data, so is covered by the same restriction formula. Pasting was performed with those homotopies, not with arbitrary new paths. No claim that a noncanonical strict path concatenation commutes on the nose is needed.

For the B--E checklist: B's new-node requirements do not arise since there are no new nodes; every cited notion is defined in an existing node and every non-elementary inference cites a statement which gives it. All cited statements were opened and are quoted verbatim in citations.json (C1/C3/C4). Existing-node and blueprint searches prevented a duplicate auxiliary fiber lemma (C5). A dependency-closure inspection found no path back to this item from any proposed dependency (C6). The only off-unit tool is explicitly declared. There is no new clause-node, circular derivation, or assumed omitted source argument (D1--D5). No non-elementary step exceeds 2000 characters. The two actual cancellations and all hypotheses are explicit rather than hidden behind 'transport' (E5).

I tested the statements on point and discrete categories: one obtains the ordinary equation p*u=q and no extra condition after it. A fork poset with incomparable X and Y below A has empty U and both final mapping spaces empty; no nonemptiness has been assumed. In the infinity category of spaces, take X=Y=A=point and f a chosen point of a space B. Then U=V=point, W=B, U_b=V_b=Omega B, and g_b is the identity. Its homotopy fiber is a point even when Omega B is noncontractible. This checks the essential case where the redundant B-data cannot simply be deleted as a set or ignored before taking the second fiber. For f=id_A the same two fiber squares recover the original slice formula. Universes, specified basepoints, arbitrary empty fibers, and the lack of limit hypotheses on E have been checked throughout.

The main correction during self-review was to discard the planned generic fiber-of-fibers node after finding the existing pasting theorem, and to cite the cone and comma mapping statements rather than a definition or ordinary Mathlib iterated-slice equivalence. Nothing remains mathematically unfinished in this one-level split.

The first dry run flagged the TeX row separator immediately followed by the downarrow command as a doubled command escape. I separated diagram rows with actual newlines; this is a formatting repair, with the argument and citations unchanged.
