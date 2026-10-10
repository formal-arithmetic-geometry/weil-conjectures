Files written:

- `dag/nodes/sec-picard-framework/thm-sc-serre-duality-curve.json` — repaired six-step split; no new nodes and no Mathlib leaves.

Attachments:

- `AlgebraicGeometry.Scheme.serreDuality` covers relative dimension one with `p + q = 1`, so it is only a partial attachment. Its transitive sorry dependencies make it unclosed.
- `AlgebraicGeometry.Scheme.nonempty_dual_H_one_iso` covers the dimension-one top-degree case; `nonempty_dual_H_zero_iso` covers the dimension-one bidual reduction. Both are partial.

WANTED: none recorded for this repair. The imported blueprint proof is represented in the item's proof fields; the cited Stacks results are stated in the DAG nodes named below.

What was wrong:

- The prior split cited a coherence definition for both coherence and proper coherent cohomology, although it states neither theorem.
- It treated the dimension-zero case as substantive despite the project's definition of connected curve requiring dimension one, and cited the proof of another node for the transcendence-degree comparison.
- It omitted affine module and finite-projective citations for the pushforward. It also misstated its rank as `d`; for a rank-`r` bundle the rank is `rd`.
- The prior review marked the blueprint source `WANTED` and assigned 02O5 to `pqf-def-coherent`; those claims have been removed.

## Review by M1

I compared the repaired node with the imported blueprint proof, the unit `sk-thm-picard-duality`, and the statements and Stacks-tag places of every cited DAG node. The item retains the source's field, properness, smoothness, finite local freeness, duality, and vanishing hypotheses. The blueprint search on Serre duality and its statement returned the item and `lem-sc-finite-duality`; neither repeats the item's statement, so `blueprint.same_as=[]`. The slopmaster2 `serreDuality` statement still omits the item's all-integer and dimension-zero formulation, and its transitive sorry audit is `rests_on_sorry`.

Step 1 uses `lem-sc-canonical-sheaf` for the differential line bundle, `lem-weil-pbc-finite-type-over-noetherian` for Noetherianness of the finite-type curve over `Spec k`, `pqf-lem-coherent-ft-locnoeth` (01XZ) for coherence of its finite locally free sheaves, and `lem-pc-coherent-hi` (02O5) for finite cohomology of a coherent sheaf under the proper map to `Spec k`. Each hypothesis is explicit: `k` is a field, `C` is finite type and proper, and both sheaves are locally free of finite rank. Step 2 is bidual linear algebra on trivializing opens plus finite-dimensional duality from step 1; no additional geometric theorem is used.

Step 3 now cites `def-sc-curves`: its connected curve is nonempty of dimension one, so the dimension-zero branch is vacuous under the stated hypotheses. Step 4 cites `lem-sc-smooth-regular` for integrality of the connected smooth curve, `def-sc-function-field` for `Frac(A)=k(C)` on an affine chart, `lem-weil-pbc-finite-type-domain-dimension-trdeg` for `dim A=trdeg_k k(C)` and its maximal-localization clause, then `lem-sc-morphism-from-function` for the finite surjective flat map induced by a transcendental `t`. A nonempty affine open of an integral finite-type dimension-one curve has dimension one; the generic point and a closed point give a chain of length one. This replaces the old appeal to the proof of `lem-sc-deg-principal-zero`.

Step 5 uses `lem-weil-pbc-finite-proper`, `pqf-lem-finite-qf`, and `pqf-lem-qf-finitefibres` to check the proper finite-fibre hypotheses; `pqf-lem-coherent-ft-locnoeth` supplies coherence. Then `pqf-lem-fff-vanishing` and `pqf-lem-sheaf-zero-stalks` kill higher direct images; `pqf-lem-leray`, `pqf-lem-leray-lowdegree`, and `lem-sc-p1-hi-vanishing` transfer cohomology and give higher vanishing. For finite local freeness of the pushforward, `lem-weil-pbc-finitely-presented-flat-module-projective` applies to the finite flat affine algebra over Noetherian `R`; `lem-weil-pbc-affine-tilde-gamma-adjunction` and `lem-weil-pbc-quasi-coherent-finite-type-affine` identify the locally free sheaf with its finitely presented, locally flat section module on `Spec B`. The same finite-presented-flat lemma makes that module finite projective. `lem-weil-pbc-finite-projective-standard-free-cover` and `lem-weil-pbc-spec-tilde-free-module` turn the resulting finite projective `R`-module into a finite locally free sheaf. The generic rank is `rd`.

Step 6 cites `pqf-lem-coherent-ft-locnoeth` again before `thm-sc-p1-duality`, then `lem-sc-finite-duality` for the finite flat comparison and `lem-sc-invertible-dual` for the line-bundle specialization. I checked finite flatness of `f` in step 4 and local Noetherianness of `P^1_k` in step 5. I tested the edge cases: the stated connected curve cannot have dimension zero; negative and above-one cohomological degrees vanish by convention and step 5; a rank-zero bundle gives zero on both sides; and the skyscraper example confirms why local freeness matters. There are no new statements to test for duplicate nodes or Mathlib matches.

For this return I replaced the two unsupported step-1 claims with 01XZ and 02O5, cited the exact dimension/transcendence statement in step 4, cited the affine and finite-projective tools in step 5, added coherence in step 6, replaced the dimension-zero proof by the definition's one-line exclusion, set `blueprint.same_as=[]`, and corrected the source and citation account above. The new cross-unit citations are declared individually in `split_report.tool_uses`; they supply generic foundations while the unit's finite-map route remains the proof.
