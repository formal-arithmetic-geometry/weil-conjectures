1. Files written:
- `dag/nodes/sec-smooth-purity/lem-pur-adic-purity-scalar-naturality.json` (repaired item; 17 proof steps).
- `dag/nodes/sec-smooth-purity/lem-pur-adic-scalar-extension-tor-bound.json` (statement-only prerequisite; Mathlib no match).
- `dag/nodes/sec-smooth-purity/lem-pur-adic-scalar-trace-coherence.json` (statement-only prerequisite; Mathlib no match).
- `dag/nodes/sec-smooth-purity/lem-pur-adic-projection-shift-coherence.json` (statement-only prerequisite; generic adjunction-shift results only, no exact match).
- `citations.json` (64 verbatim node quotes, one for every citation in every proof step).

2. Attachments:
- No sorry-free declaration under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` states the item or any retained new prerequisite. The item-id, blueprint-tag and purity/scalar searches found no declaration.

3. WANTED:
- None.

4. What was wrong in the returned split and what I corrected:
- `lem-pur-adic-compact-support-tor-bound` duplicated `lem-coef-integral-compact-support` and `prop-coef-integral-exceptional-adjoint`; I removed that node and Step 1 now cites those two existing statements directly.
- `lem-pur-adic-adjoint-transpose-linearity` was an elementary adjunction calculation; I removed it and wrote the naturality and linearity calculation directly in Step 8 using the existing adjunction and linear-construction nodes.
- The scalar-trace node was not self-contained. It now introduces the finite coefficient fields, schemes, smooth morphism, compact-support functors, base trace, scalar-extension comparisons, and the explicit formula defining each extended trace before stating the coherence identity.
- The projection-shift node was not self-contained. It now introduces the coefficient field, morphism, finite-Tor objects, an arbitrary degree-zero object `T`, a trace `t`, the projection map and the explicitly defined trace-valued map `u_K`; it states the proper/open constituent and adjunction shift compatibilities for these objects.
- Step 9 now cites `def-pur-smooth-purity-map` and `def-pur-co-smoothness` for the identification of the reduced transpose with the finite counit composite.
- The item records `det-sp-field-extension-towers` in `blueprint.same_as`. That node includes the same integral coefficient comparisons and purity intertwining, but additionally fixes a normalized tower implementation, finite-level realizations, units/counits, and rationalization; the present item instead gives the reconstructed adic family and its explicit finite-reduction route.
- All retained proof steps remain below 2000 characters. The route uses no SGA 4 or SGA 4½ source.

## Not duplicates

- `lem-pur-adic-scalar-extension-tor-bound` vs `lem-pur-derived-change-of-rings`: the new statement proves preservation of a common finite-Tor interval under ramified coefficient extension; the existing node only constructs/controls derived tensor via K-flat resolutions.
- `lem-pur-adic-scalar-trace-coherence` vs `det-sp-field-extension-towers`: the new statement gives the explicit trace reconstructed from one base trace and proves its scalar identity; the determinant node packages a broader normalized-tower comparison with units, counits, purity maps, and rationalization.
- `lem-pur-adic-projection-shift-coherence` vs `lem-weil-pbc-ringed-projection-mate-exact`: the new statement specializes projection and adjoint shift compatibility to the integral compact-support trace-valued map and its transpose, including the proper/open decomposition; the existing node is the generic ringed-topos mate-exactness tool.

5. What I could not finish:
- Nothing remains for stage 1; the server dry run and delivery are the remaining checks.

## Review by Q105

I reread the item against `dag/units/sk-thm-purity-transport.json`, the current `main-20261015` purity sources, and the returned review entry. I opened every statement cited by all 17 steps and regenerated `citations.json` from those exact statements. Step 1 now uses the existing compact-support interval `[a,b+2D_X]` and exceptional-adjoint interval `[a-2D_X,b+2D_Y]`, with the dimension bounds and empty-scheme convention verified in their statements. Steps 2–5 retain the operation, scalar-extension, strict-tower, projection and compact-support comparison hypotheses and their stated domains.

For Steps 6–8 I checked the base coefficient object, reconstructed trace, scalar extension formula, adjunction transpose, and linearity calculation. The removed transpose node contributed no independent theorem: the rewritten Step 8 derives naturality by applying the injective adjunction Hom bijection to the natural projection/counit square and derives linearity from additivity and scalar linearity of the cited functors and counit. For Step 9 I verified that the cofinal finite-level identification uses the definition of the smooth purity map through the tensor map `theta` and its counit-transpose construction; the step now cites both `def-pur-smooth-purity-map` and `def-pur-co-smoothness` in addition to the finite trace and reduction statements. The cone argument still cites the triangulated, derived-complete and distinguished-cone-zero statements.

I reread the exceptional coefficient transpose (Steps 10 and 13), scalar trace identity (Steps 11–12), mate-pasting coherence (Step 14), and shift argument (Steps 15–17). The two retained auxiliary nodes are self-contained: the scalar-trace statement explicitly defines `t_L` from `t_0`, `theta_L` and `c_{L/E_0}`, while the projection-shift statement explicitly defines `PF_{T,K}` and `u_K` for a degree-zero `T` and trace `t`. Their hypotheses cover finite-Tor objects, separated finite type, coefficient rings, and canonical proper/open and adjunction shifts. I checked the edge cases `F=E`, `d=0`, identity morphism, empty schemes, zero objects, and ramification index greater than one. The item’s blueprint counterpart is recorded with the precise difference described above.
