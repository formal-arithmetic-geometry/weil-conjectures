# Worker report

1. Files written:

- `dag/nodes/sec-picard-framework/lem-sc-hilb-geometrically-integral.json`: repaired statement split with four proof steps; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-hilb-dominating-power.json`: repaired unsplit domination statement; no Mathlib match.

2. Attachments:

- `AlgebraicGeometry.isProper_and_geometricallyIntegral_of_representableBy_hilbertPresheaf_curve` belongs to `lem-sc-hilb-geometrically-integral`.
- `AlgebraicGeometry.exists_surjective_of_representableBy_hilbertPresheaf_curve` belongs to `lem-sc-hilb-dominating-power`.

3. WANTED:

None. The Stacks source `literature/stacks-project/pic.tex` is cited directly.

## Review by G1

I reread Stacks Tag 0B9I (proposition-hilb-d), including its smoothness/reducedness and power-of-the-curve irreducibility arguments, and reread `WeilConjectures/AlgebraicGeometry/Hilbert/Curve.lean` lines 1049--1105. I opened the statements of `thm-pc-hilb-curves`, `lem-pc-hilb-smooth`, `sbc-lem-smooth-geometrically-reduced`, `lem-weil-pbc-surjective-base-change`, `def-pc-geometrically-irreducible`, `def-pc-integral-scheme`, `def-pc-curve`, and `def-sbc-smooth-morphisms`.

Step 1 now cites `thm-pc-hilb-curves` clause (1) for representability of every Hilbert functor, identifies the supplied `H_d` with that representing scheme, then applies `lem-pc-hilb-smooth` and `sbc-lem-smooth-geometrically-reduced` directly to `H_d -> Spec k`; it no longer asserts uncited smoothness preservation under base change. Step 2 first derives geometric integrality of `X`: smoothness gives geometric reducedness, while geometric irreducibility, nonemptiness of the curve, and `def-pc-integral-scheme` give integrality after every field extension. It then applies `lem-sc-hilb-dominating-power`, identifies `Y_{k'} -> H_{d,k'}` as the base change of `pi`, and cites `lem-weil-pbc-surjective-base-change` for surjectivity. The geometric irreducibility statement gives irreducibility after base change, and the continuous-image argument gives irreducibility of `H_{d,k'}`. Step 3 combines reducedness and irreducibility through `def-pc-integral-scheme`; the conclusion is now geometric integrality over `k`, with nonemptiness of each `H_{d,k'}` stated explicitly.

For the new domination node, I checked that the statement is self-contained, cites `def-sbc-smooth-morphisms` after “smooth”, says that `Y` itself is geometrically irreducible, and includes the corresponding statement dependencies. I removed the unsupported construction sentence about an iterated fibre product and iterated addition. I searched the DAG and blueprint for duplicates before retaining this node. LeanSearch, LeanFinder/Loogle, and Mathlib source grep found no Hilbert-scheme declaration. Small cases `d=0` and `d=1` were checked: the claims reduce respectively to `Spec k` and to the given curve.

This repairs all returned C4/C1/C4/B1-B3/E points: the missing geometric-integrality derivation, base-change-surjectivity citation, all-degree representability citation, malformed domination statement, and conclusion/nonemptiness wording.

4. What was wrong or incomplete:

The returned version applied the domination lemma before deriving geometric integrality of `X`, omitted the all-degree representability and surjective-base-change citations, and left a proof sketch in the new node's statement. These have been repaired.

5. What I could not finish:

No Lean build was run because stage 1 forbids builds; delivery preflight remains.
