Files written:

- `dag/nodes/sec-deligne-laumon-a1/lem-per-regular-immersion-class-calculus.json` — the split statement node, with twelve proof steps and the coefficient, base-change, localization, and exceptional-transitivity clauses.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-modified-blowup-generalized-class.json` — statement-only supporting lemma; Mathlib searches found no match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-noetherian-etale-chern-identities.json` — statement-only supporting lemma; Mathlib searches found no match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-noetherian-supported-product-calculus.json` — statement-only supporting lemma; Mathlib searches found no match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-regular-flag-blowup-geometry.json` — statement-only supporting lemma; Mathlib searches found no match.
- `citations.json` — verbatim statement quotations for all 33 cited node uses.

Attachments: none. No sorry-free project declaration stating this item was found in the searched source.

WANTED: none.

The imported item was retained because its statement agrees with the ILO Exposé XVI regular-immersion construction. I expanded its proof into the global modified-blowup construction, the Cartier sign check, the codimension-one polynomial calculation, the general blowup reduction, the regular-sequence flag comparison, flat/open and localization compatibility, and coefficient reduction. The four new lemmas isolate the non-elementary modified-blowup, Chern, supported-product, and regular-flag facts; searches of the DAG and blueprint found no existing node with any of those statements. No statement was disputed or weakened. No Lean code was written or compiled, as required for this stage.

## Review by Q65

I read the item against `literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf`, Exposé XVI §§2.1–2.3 and §3.2, including Definition 2.3.1, Theorem 2.3.2, Lemma 2.3.3, Proposition 2.2.3.1, and the coefficient square in Proposition 3.3.1. I also read the four new node statements and their cited sources: the modified blowup statement uses Definition 2.2.1.1 and Propositions 2.2.1.3–2.2.1.5, 2.2.2.1, 2.2.3.1–2.2.3.2; the Chern statement uses Theorems 1.2–1.3 and Propositions 1.4 and 1.7; the supported-product statement uses §2.1, Lemma 2.2.2.4, Proposition 2.2.3.2, and the proof of Theorem 2.3.2; and the regular-flag statement uses the proof of Lemma 2.3.3 and Theorem 2.3.2.

For step 1, I checked that the conormal is locally free from `lem-per-regular-flag-blowup-geometry`, that the modified-blowup class and its global uniqueness come from `lem-per-modified-blowup-generalized-class`, and that `lem-amb-closed-support-hom` plus `thm-amb-etale-exceptional-adjoint` really identify supported cohomology with the required adjoint morphisms. Step 2 uses the modified-blowup formula, the ideal-normalized supported product, and the supported Cartier Kummer statement to fix the positive Chern-class sign. Step 3 uses the nested supported products and the independently stated right-adjoint composition lemma, and explicitly treats codimension zero before reducing to codimension one.

For steps 4–6 I checked every conormal, strict-transform, exceptional-divisor, and injectivity hypothesis against `lem-per-regular-flag-blowup-geometry` and `lem-per-modified-blowup-generalized-class`. The polynomial calculation in step 6 uses exactly the Chern/Whitney and line-duality clauses of `lem-per-noetherian-etale-chern-identities` and the additive/interchange clauses of `lem-per-noetherian-supported-product-calculus`; the displayed identity for (Q_H) has the required sign. Steps 7–8 use the excess formulas and (c_{n-1}(K^\vee)=(-1)^{n-1}c_{n-1}(K)), then apply the codimension-one case and the supported projection/associativity clauses.

Step 9 applies the proven composition to a regular sequence flag and uses the regular-sequence definition only to establish that each successive quotient is Cartier. Step 10 checks flat base change and conormal pullback with `lem-per-regular-lci-geometric-calculus`, then invokes the arbitrary-base-change clause of the modified-blowup lemma and the stated twist comparison. Step 11 uses the affine ind-etale closed-support base-change lemma, the etale cohomology continuity lemma, the supported-Hom cone identification, and the finite Tate-line pullback statement; I verified that only affine ind-etale localization maps are asserted. Step 12 checks coefficient reduction at the level of the defining polynomial, pseudo-divisor operator, and supported uniqueness, and separately records the root power map and dual negative twists. Every one of these 33 uses has a verbatim quotation in `citations.json`.

I ran the server `check_dag` preflight after writing the node files; it returned `OK: no finding introduced by the sandbox or on its nodes`. The split has no unresolved correction or unfinished subtask.
