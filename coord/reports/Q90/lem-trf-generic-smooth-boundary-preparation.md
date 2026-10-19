# Stage-1 report: lem-trf-generic-smooth-boundary-preparation

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-generic-smooth-boundary-preparation.json` — repaired item split into five proof steps; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-projective-inseparable-spread-normalization.json` — repaired existing new statement node; removed the unused `lem-trf-relative-curve-factorization` statement dependency; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-normalization-inseparable-base-change.json` — new statement node for normalization after the further purely inseparable field extension; no Mathlib match.
- `citations.json` — exact full statement quotes for every cited node in every proof step.

## Attachments

None. I searched the project declarations in `WeilConjectures/` for the item tag, its geometric notions, and the candidate normalization declarations. No sorry-free declaration states the item or either new node.

## WANTED

None. The source used is present at `literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf`, Exposé X, Theorem 3.5, Step 5, printed pages 163–164. The normalization comparison follows Stacks `varieties.tex`, Tags 0C3N and 07QT–07QW, which are present locally.

## Not duplicates

- `lem-trf-normalization-inseparable-base-change` vs `lem-weil-pbc-reduced-algebraic-normalization-field-change`: the existing node gives an isomorphism only for a separable field extension (and a universal homeomorphism in general); the new node gives an isomorphism for a further finite purely inseparable extension under the stronger hypothesis that the first normalization is geometrically normal, and records the reduced-boundary pullback.
- `lem-trf-normalization-inseparable-base-change` vs `lem-sbc-normalization-stalk-base-change`: the existing node concerns relative normalization after base change to a local scheme, while the new node concerns absolute normalization of a finite-type generic fibre after a finite purely inseparable field extension.
- `lem-trf-normalization-inseparable-base-change` vs `def-exc-excellent-ring`: the existing definition node defines excellence and does not state any normalization or field-extension comparison; the new node proves the normalization comparison under geometric normality.
- `lem-trf-normalization-inseparable-base-change` vs `lem-exc-field-algebra-strict-henselization-excellent`: the existing node concerns excellence of a strict-henselization field algebra; it has no normalization base-change conclusion, while the new node concerns finite purely inseparable base change of a normalized generic fibre.
- `lem-trf-normalization-inseparable-base-change` vs `lem-exc-fields-excellent`: the existing node states excellence properties for fields and their extensions; it does not compare normalizations or reduced boundaries, which are the content of the new node.
- `lem-trf-projective-inseparable-spread-normalization` vs `lem-trf-relative-curve-factorization`: the existing factorization node constructs the initial relative curve and the transcendence-degree-one extension; the repaired node starts with a prescribed finite purely inseparable generic-field extension and spreads it by a projective normalization, then records the generic fibre normalization.
- `lem-trf-generic-smooth-boundary-preparation` vs `lem-trf-alteration-relative-curve-preparation`: the parent node invokes this item after relative-curve factorization and asks for the two-stage inseparable preparation, projective spreading, and generic boundary conclusion; it does not state those clauses itself.

## What was wrong in the returned material

The returned review correctly identified a false inference in the former boundary step: a closed point of a smooth curve over an imperfect field can have an inseparable residue field (for example $x^p=t$ on $\mathbf A^1_{\mathbf F_p(t)}$). I removed that inference. The repaired proof first chooses $K_1/\kappa(Y)$ so the normalized generic curve is geometrically normal, then forms its finite reduced boundary and chooses a further finite purely inseparable $K/K_1$ using the existing finite-inseparable geometric-reduction lemma. The finite geometrically reduced boundary is finite etale by the finite-etale algebra criterion.

The former proof also used the normalization after the second field extension without identifying it with the first normalized model after base change. I added `lem-trf-normalization-inseparable-base-change`, sourced to Stacks Tag 0C3N together with the geometrically-normal field-extension lemmas, and cite it in the item before projective spreading. The dimension assertion is now explicit: the generic fibre has dimension one from the transcendence-degree node, finite purely inseparable field extension preserves that dimension, and finite birational normalization preserves it. The spreading node's unused `lem-trf-relative-curve-factorization` statement dependency was removed.

## What I could not finish

Nothing. This is a stage-1 statement split; no Lean code, compiler, Lake, or build invocation was used.

## Review by Q90

I reread the imported item, the returned spreading node, the parent `lem-trf-alteration-relative-curve-preparation`, the unit record `sk-i-curve-zero`, the blueprint proof for that unit, and Exposé X, Theorem 3.5 Step 5, pp. 163–164. I also read Stacks `varieties.tex` at Tags 04KT (finite purely inseparable geometric reduction), 0C3N (normalization and change of fields), and the geometrically-normal section around Tags 07QT–07QW. The mandated server `check_dag` check passed after the repair.

Step 1 uses `lem-sc-closed-irreducible-dimension-trdeg` exactly for the dimension-one generic fibre and `lem-weil-pbc-normalization-geonormal-insep` exactly for the first finite purely inseparable extension and geometrically normal normalization. I verified that the generic fibre is finite type over $\kappa(Y)$ and that the extension introduced here is named $K_1$, so it is not confused with the later boundary extension.

Step 2 defines the reduced generic boundary on the first normalization, checks that it is nowhere dense in the one-dimensional curve, and uses the cited dimension-zero and finiteness nodes before applying `lem-pur-finite-inseparable-geometric-reduction`. I checked that this node's hypotheses (finite type and finitely many irreducible components) follow from finiteness of the boundary. The finite-etale criterion is used only after geometric reducedness has been obtained; no residue-field separability is inferred from smoothness.

Step 3 cites the new normalization node, whose statement explicitly supplies the canonical isomorphism after $K/K_1$, geometric normality of the new normalization, and compatibility of reduced closed inverse images. I checked the dimension calculation against Step 1: a finite purely inseparable field extension is algebraic, and a finite birational normalization does not change the one-dimensional Krull dimension.

Step 4 applies the repaired spreading node with the final field $K$. I reread that node and verified that its hypotheses are exactly the excellent integral $Y$, excellent integral $X_0$, proper dominant $g$, finite purely inseparable generic extension, and the given proper dominant generically finite $a$. Its statement supplies all compatibility maps and the generic-fibre normalization used in the next step.

Step 5 applies the dimension-one geometrically-normal smoothness criterion to the identified generic fibre, uses its connected nonempty clause for irreducibility, and transports the finite-etale boundary from Step 2 through the normalization comparison. The empty boundary is vacuous. I checked the imperfect-field counterexample from the return against this route: it is handled by the second extension $K/K_1$, so the repaired proof does not assert that the original closed point residue field was separable.

I checked all five `uses` lists against the full statements copied into `citations.json`, checked that `proof_deps` is their union, reran all required Mathlib searches for the item and new normalization node, and ran the server `check_dag` precheck. No SGA 4 or SGA 4½ source is cited.
