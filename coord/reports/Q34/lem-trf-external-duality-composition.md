1. Files written

- `dag/nodes/sec-trace-formula/lem-trf-exceptional-internal-hom-composition.json`: retained statement-only composition-coherence lemma; Mathlib searches found no match.
- `dag/nodes/sec-trace-formula/lem-trf-external-duality-composition.json`: repaired item with an explicit formula for the canonical external-duality maps and a direct compositor-naturality proof.
- `citations.json`: verbatim witnesses for every cited node in every item step.
- `searches.jsonl`: retained search log for the item and helper.

2. Attachments

None. The source search found no sorry-free declaration of the item or the helper under `WeilConjectures/`.

3. WANTED:

None.

4. What was wrong and what changed

The returned split left the main calculation as an assertion about evaluation transposes, invoked `lem-trf-open-hom-mate` for a map out of an exceptional pullback where that node does not apply, and used an evaluation characterization that the Verdier-duality node does not state for `xi_c`. It also omitted the compositor associativity citation even though the `iota` identifications depend on it. I corrected the item statement by introducing `U=Lp_2^*K`, `V=Rp_1^!K`, the canonical external-duality map `delta:RHom(U,V) -> P`, the identifications `iota_h`, and the explicit formula `xi_h = Rh!(delta) o E_h o iota_h`. The proof now uses the naturality of the exceptional composition comparison at `delta`, the helper equality for the raw internal-Hom exchanges, naturality of those exchanges in both variables, and associativity of [thm-sf-comp-composition]. The open-mate and transpose argument was removed. `thm-sf-comp-composition` is declared as the generic tool use and is cited in the relevant steps. The helper remains statement-only and is not a restatement of the item.

## Not duplicates

`lem-trf-exceptional-internal-hom-composition` vs `lem-trf-exceptional-internal-hom-exchange`: the existing node gives one-map exchange; the helper gives coherence of exchanges for a composite and states the comparison square.

`lem-trf-exceptional-internal-hom-composition` vs `lem-trf-open-hom-mate`: the existing node treats the tensor-Hom mate of one morphism under an open restriction; the helper compares exchange isomorphisms for two composable exceptional maps and does not concern a chosen morphism.

## Review by Q34

I reread the item against Varshavsky, *Lefschetz–Verdier trace formula*, §0.3(a)-(b), equations (0.3)-(0.4), and §1.2.2(a), first arrow, and reread the current `thm-trf-verdier-duality` node and the helper's full statement. The hypotheses remain the finite coefficient stage, separated finite-type schemes, the correspondence, the open immersion, exceptional admissibility, and the ordered product `K boxtimes D_X K`. I checked that `U` and `V` live on `X x X`, while `iota_c` and `iota_cj` explicitly transport them to `C` and `W` through the pullback and exceptional compositors.

Step 1 uses the trace-source, external-product, dualizing-complex, admissibility, and Verdier-duality statements for exactly those constructions. It also cites [thm-sf-comp-composition] for the associativity that makes the `cj` compositor identification equal to the iterated `j` then `c` identification. This fixes the earlier uncited compatibility of the `iota` maps.

Step 2 applies the helper to `M=U` and `N=V`; its displayed coherence equality is exactly the raw exchange equality used in the calculation. The naturality of the composition comparison at `delta` is the naturality of the canonical composition isomorphism in [thm-sf-comp-composition], while the naturality of exchange in both variables identifies the raw exchange composite with the stated `E_j`. I checked the source and target of every composite before substituting the explicit formula for `xi_h`; no object on `X x X` is treated as though it were on `C` or `W`.

Step 3 records that the resulting identity is between the specified canonical maps, preserves the external-product order, and specializes to the empty, full, zero, and identity cases by the unit clause of [thm-sf-comp-composition]. Its citations cover the canonical isomorphisms and the ordered product. The helper is intentionally statement-only, and its Mathlib searches remain recorded in `searches.jsonl`. The proof has no transpose argument and no citation of `lem-trf-open-hom-mate`.

The repair addresses the returned C4/C3 and E5 points by making the map formula and all compositor equalities explicit, and addresses the missing tool citation by adding [thm-sf-comp-composition] to the uses, proof dependencies, tool uses, and citation witnesses.

5. What could not be finished

Nothing remains unfinished; the required dry run is the remaining delivery check.
