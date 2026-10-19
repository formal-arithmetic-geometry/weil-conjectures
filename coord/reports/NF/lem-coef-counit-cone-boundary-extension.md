# Stage-1 report: lem-coef-counit-cone-boundary-extension

## Files written

- \`dag/nodes/sec-six-functors/lem-coef-counit-cone-boundary-extension.json\`: repaired five-step statement split using the right-slice pullback.
- \`dag/nodes/sec-six-functors/lem-coef-homotopy-adjunction-coherent-witnesses.json\`: repaired statement-only supporting lemma; Mathlib searches found no match.
- \`citations.json\`: updated verbatim statement quotes for every cited node and step.

## Attachments

None. I found no declaration tagged \`(blueprint: lem-coef-counit-cone-boundary-extension)\` and no sorry-free declaration in the source checkouts stating this item or the supporting lemma.

## WANTED

- WANTED: an archival copy of Riehl--Verity, *Homotopy coherent adjunctions and the formal theory of monads*, especially Observation 4.3.4, Proposition 4.3.6, Theorems 4.3.9 and 4.3.11, and Remark 4.3.12, for the item and \`lem-coef-homotopy-adjunction-coherent-witnesses\`.

## What was wrong or incomplete

The returned version used the fat comma \(C_z\times_{D_z}\operatorname{Fun}(\Delta^1,D_z)\times\{a\}\). Its boundary identification was therefore only up to a diagonal comparison, and the fifth step incorrectly claimed that a fat-comma filler supplied a cone \((\Delta^m)^{\triangleright}\to D_z\) with the prescribed boundary. The repair uses \(E'_z=C_z\times_{D_z}(D_z)_{/a}\), where the right-slice component is literally a join map ending at \(a\). The supporting lemma now defines “one chosen witness fixed at the simplicial level” as a specified 2-simplex \(\beta_L\) in \(\mathscr K(c,d)\), says that the dual witness only needs to exist coherently, and asserts terminality in \(E'_z\) itself. The fifth step now extracts the cone map from the slice component and uses the pullback equation for strict composition and strict boundary agreement. The supporting node's blueprint ancestry now includes \`lem-coef-enriched-coherent-adjunction-extension\` after the item. The item proof origin is \`agent\`, because the cited online document is not archived locally.

## Not duplicates

- \`lem-coef-homotopy-adjunction-coherent-witnesses\` vs \`def-coef-coherent-adjunction-data\`: the latter assumes already coherent functors and states terminality in the fat comma; the repaired node starts from a homotopy-2-category adjunction, specifies a simplicial triangle witness, and proves terminality in the right-slice pullback.
- \`lem-coef-homotopy-adjunction-coherent-witnesses\` vs \`lem-coef-infinity-slice-right-fibration\`: the latter constructs general join slices and their right-fibration/Kan-fiber properties; the repaired node adds adjunction data and the terminal counit object after pulling back that slice.
- \`lem-coef-counit-cone-boundary-extension\` vs \`lem-coef-enriched-coherent-adjunction-extension\`: the former fills one prescribed boundary simplex by a right-slice terminality argument, while the latter performs the larger walking-adjunction cell induction that consumes this filler.

## What I could not finish

The supporting coherent-witness lemma remains statement-only by design; it is a genuine Riehl--Verity input for a later worker. No Lean files were written and no compiler, Lake, or build tool was run.

## Review by NF

I reread the returned item, the supporting node, the current shared versions of \`def-cbc-enhanced-diagrams-cones\`, \`def-coef-coherent-adjunction-data\`, \`lem-coef-infinity-slice-right-fibration\`, \`lem-coef-infinity-slice-arrow-equivalence\`, \`lem-coef-infinity-comma-mapping-pullback\`, \`lem-coef-infinity-adjunction-mapping-equivalence\`, \`lem-coef-infinity-relative-initial-boundary\`, and the consumer \`lem-coef-enriched-coherent-adjunction-extension\`. I also reread the Riehl--Verity places named in the sources and the Kerodon right-slice construction cited by the supporting statement.

Step 1 now uses the supporting statement's exact assertion that the degreewise pullback \(E'_z\) is a quasicategory with terminal object \((U_za,\epsilon_a)\), and uses the right-slice node only for the meaning of its source projection and literal slice simplices. I checked that the pullback is formed over \(L_z\) and the source projection, so its objects have the required type.

Step 2 uses the supporting statement's explicit definition of the fixed witness \(\beta_L\), the existing coherent mapping-equivalence statement, and the existing coherent-adjunction-data terminality clause only as the compatible coherent input. I checked that the repaired supporting conclusion is terminality in \(E'_z\), rather than silently transferring terminality from the fat comma.

Step 3 unpacks the 0-to-1 boundary simplex as \(x:\partial\Delta^m\to C_z\). The 0-to-2 boundary, including the apex and prescribed final edge, is a literal map \(\partial\Delta^m\star\Delta^0\to D_z\); by the right-slice definition it is exactly a map to \((D_z)_{/a}\). I checked the source restriction is \(L_zx\), the final vertex is \(a\), and the last slice edge is exactly \(\epsilon_a\), so \(a_T\) lands in \(E'_z\) and agrees on every face and degeneracy.

Step 4 applies the cited dual final-object boundary criterion to the terminal object in \(E'_z\), with \(m\ge1\). I checked the criterion's last-vertex condition and its requirement that the whole boundary be fixed.

Step 5 projects the filler to \(C_z\) and reads the other component as a map \(\Delta^m\star\Delta^0\to D_z\). The pullback equation gives the initial face \(L_z\bar x\) exactly, so this pair defines the 3-object simplicial functor and its strict composition law. Since the filler restricts to \(a_T\), both hom maps, the cone edge, and all degeneracies agree literally with \(T\). This directly repairs the returned m=1 diagonal counterexample.

I checked all five proof-dependency unions, the revised blueprint ancestry, the agent proof origin, the Mathlib search records for the repaired statement, and every quote in \`citations.json\` as a verbatim substring of its cited statement. I did not write Lean or run any compiler/build tool.
