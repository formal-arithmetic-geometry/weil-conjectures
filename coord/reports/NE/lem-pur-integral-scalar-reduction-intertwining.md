# Worker report

Files written:

- `dag/nodes/sec-smooth-purity/lem-pur-integral-scalar-reduction-intertwining.json` — repaired item proof in four steps; no Mathlib match.
- `dag/nodes/sec-smooth-purity/lem-pur-scalar-reduction-transpose-normalization.json` — new statement-only supporting node; no Mathlib match.
- `citations.json` — verbatim quotations for every cited proof step.
- `report.md` — this report.

Attachments: none.

WANTED: none.

What was wrong in the returned delivery: the old step 2 only quoted the explicit comparison from `lem-pur-coefficient-extension-reduction-model`; it never identified the arbitrary normalized model `S_Y` with that model's quotient presentation. It also treated the target counit as though its system had already been identified, and step 3 consequently inherited the gap. The setting was delegated to the truncated primitive-model node. I added `lem-pur-scalar-reduction-transpose-normalization`, which states the coherent presentation equations and the double-transpose uniqueness argument, and I use the complete effective comparison-model statement to supply the normalized presentation and counit. The repaired proof first establishes effectivity, then proves whole-system equality by uniqueness of the two adjunction transposes, then derives the explicit same-index component and finally the tower-data name `gamma_A`. The report now records the actual blueprint source places used by each step. `citations.json` is present in the delivery sandbox and contains a verbatim quote for every entry in every step's `uses` list.

What I could not finish: nothing.

## Not duplicates

- `lem-pur-scalar-reduction-transpose-normalization` vs `lem-pur-coefficient-extension-reduction-model`: the existing node constructs the canonical coherent coefficient-extension comparison, while the new node proves that an arbitrary normalized scalar realization has the same double transpose and hence equals that comparison.
- `lem-pur-scalar-reduction-transpose-normalization` vs `def-pur-coefficient-reduction-presentation`: the existing definition only predicates the finite evaluation and transition equations for specified presentation data; the new node applies those equations to the scalar association presentation and adds the transpose uniqueness conclusion.
- `lem-pur-scalar-reduction-transpose-normalization` vs `def-trf-integral-comparison-realization-models`: the existing definition specifies normalization of realization models; the new node uses that normalization together with the counit and association map to identify two concrete coherent morphisms.
- `lem-pur-integral-scalar-reduction-intertwining` vs `lem-pur-coefficient-extension-reduction-model`: the existing node proves the canonical coefficient-extension reduction model for arbitrary derived inputs; the repaired item additionally handles every normalized primitive scalar model, names the tower comparison, and records the same-index component.
- `lem-pur-integral-scalar-reduction-intertwining` vs `lem-pur-scalar-reduction-transpose-normalization`: the new node is only the presentation/transpose uniqueness lemma; the item adds invertibility, the explicit quotient formula, and the identification with `gamma_A` under tower data.

## Review by NE

I reread the live item, the returned review, and the complete statements of `def-trf-integral-comparison-realization-models`, `lem-trf-effective-comparison-realization-models`, `def-pur-coefficient-reduction-presentation`, `lem-pur-scalar-reduction-transpose-normalization`, `lem-pur-coefficient-extension-reduction-model`, `def-pur-scalar-extension-tower-data`, `def-weil-integral-scalar-extension`, and `def-weil-integral-reduction-tower`. I also checked `lem-coef-derived-system-evaluation-calculus`, `lem-coef-normalized-dvr-effectivity`, and `def-coef-normalized-dvr-tower` while checking the target system and counit. The malformed primitive-model statement is no longer carrying the proof: step 1 takes the normalized scalar realization, its canonical coherent presentation, and the constructible effectivity isomorphism from the complete effective comparison-model node.

For step 1, the source is the finite-extension proof's paragraph on normalized tower reconstruction and coherent maps of towers. I verified that the item hypotheses give a constructible derived-complete input and that the target is the normalized `B`-system `C(P)`, so the cited counit is the whole-system effectivity counit. For step 2, I read the new node and the coefficient-reduction-presentation definition: its `a_m` maps satisfy both the finite evaluation equation and the actual-transition equation. I checked the realization-model definition's normalization sentence and the reduction-exceptional blueprint's uniqueness-of-transposes argument; these give equality before finite evaluation and retain every transition. This directly repairs the returned D3/E5/C3-C4 objection.

For step 3, I read the coefficient-extension model's displayed association formula and the scalar-extension definition's commuting maps `A_{E,m}->B_m`; I checked the reduction-tower definition supplies the actual transition maps. The resulting component uses `B_{n+1}` on both sides, so the ramified case changes the ring map but does not reindex by `e(L/E)n`. For step 4, I read the tower-data definition: scalar reduction is formed by coherent reduction followed by its counit. Combined with step 2's whole-system equality, this is exactly the named `gamma_A`, including transitions. I checked `E=L`, `n=0` after the item's `n+1` convention, the zero object, and the ramified quadratic example.

I copied every citation quote verbatim into `citations.json`, added the new node's eight required Mathlib searches (LeanFinder, Loogle, grep, and LeanSearch with a second phrasing), and recorded no Mathlib leaf. No SGA source is used.
