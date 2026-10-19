1. Files written:

- `dag/nodes/sec-trace-formula/lem-trf-separable-closed-point-formal-presentation.json` — repaired split item; no Mathlib leaf.
- `dag/nodes/sec-trace-formula/lem-trf-separable-residue-coefficient-section.json` — new statement-only Tag 0C34 lemma; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-field-extension-completion-presentation.json` — retained statement-only Tag 0C54 lemma; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-completed-jacobian-differentials.json` — retained statement-only completed Jacobian lemma; Mathlib has only ordinary, uncompleted presentation APIs.

The earlier Cohen-presentation and local-field-change auxiliaries were removed because the return identified them as duplicates of existing DAG nodes.

2. Attachments: none.

3. WANTED: none.

4. Corrections made:

The returned D1/D2/C5 issue was repaired by citing the existing completion-local-ring and Cohen presentation nodes for the local, residue, and power-series facts, and by citing the existing field-extension faithful-flatness, localization, and local-flat-faithful-flat nodes for the field change. Only the genuinely separate Tag 0C34 coefficient section, Tag 0C54 completion-limit comparison, and completed continuous Jacobian comparison remain as auxiliaries. The Jacobian statement now defines the map by the continuous differential extension and sends the basis class `e_i` to `d̂(t_i)`. The completion statement now says explicitly that `F ↪ K` is a `k`-embedding. Every retained auxiliary has the item followed by the full ancestor `via` chain in `blueprint.from.via`.

## Not duplicates

- `lem-trf-separable-residue-coefficient-section` vs `lem-weil-pbc-coefficient-residue-section`: the existing node only treats characteristic-zero residue sections, while the new node is the finite-separable extension section in every characteristic (Tag 0C34).
- `lem-trf-separable-residue-coefficient-section` vs `lem-weil-pbc-cohen-power-series-presentation`: the Cohen node gives an abstract coefficient presentation and does not assert a prescribed `k`-algebra section for a separable residue extension.
- `lem-trf-field-extension-completion-presentation` vs `lem-weil-pbc-flat-local-completion-iso`: the existing node compares completions when a flat local map has the same residue field; the new node computes the completion after changing from `F` to an arbitrary field `K` and transports a chosen power-series presentation.
- `lem-trf-completed-jacobian-differentials` vs `lem-trf-rational-node-quadratic-completion`: the existing node is a one-dimensional nodal quadratic classification; the new node gives the differential cokernel for any finite power-series presentation at a separable closed point.
- `lem-trf-completed-jacobian-differentials` vs `lem-trf-nodal-point-local-criterion`: the existing node uses this calculation inside a nodal characterization and does not state the completed Jacobian comparison independently.

5. What I checked.

## Review by Q35

I reread the item and the three retained auxiliaries, the statements of every existing node cited by the repaired proof, and Stacks Varieties Tags 0C52, 0C54, 0C4Y, 0C50, More Algebra Tag 0C34, and Curves Tag 0C4D. Step 1 uses finite-type Noetherianity and the existing completion-local-ring statement for the local ring, maximal ideal, and residue field. Step 2 uses the exact Tag 0C34 section statement and the two existing Cohen presentation statements; I checked that the section is a `k`-algebra map and that the coefficient field is the prescribed residue field `F`. Step 3 is the elementary dummy-variable padding argument. Step 4 uses every hypothesis of the corrected Jacobian node, including finite separability, the chosen section, the kernel generators, and the explicitly defined continuous differential map. Step 5 factors the field change through `S → S ⊗ₖ K`, uses the existing faithfully-flat base-change node, then localization and the local-flat-to-faithfully-flat node; the direct evaluation calculation gives `q`, `mB`, and residue field `K`. Step 6 applies the retained 0C54 completion-limit statement to the chosen presentation. Step 7 applies the Jacobian statement over `K` with residue extension `K/K`, whose identity map is finite separable, and with the structural section `K → B̂`.

I checked the edge cases `S=F`, a smooth polynomial local algebra, and `k[[u,v]]/(uv)`. I also checked the purely inseparable example `k=F_p(a), S=k[x]/(x^p-a)`, which explains why the finite-separable hypothesis in the Jacobian and section nodes is required. I reran the mandated Mathlib searches for the new Tag 0C34 node and retained the prior search logs for the 0C54 and Jacobian nodes; the results contain only general unramified, adic, power-series, and ordinary differential APIs. No SGA source is used.

## Not duplicates

- `lem-trf-completed-jacobian-differentials` vs `lem-trf-separable-closed-point-formal-presentation`: the auxiliary isolates the completed Jacobian differential map and its continuous extension; the item combines it with Cohen structure, field change, and completion transport.
- `lem-trf-completed-jacobian-differentials` vs `lem-trf-geometric-field-stalk-descent`: geometric-field-stalk-descent concerns geometric points and residue embeddings, not a completed Jacobian presentation.
- `lem-trf-completed-jacobian-differentials` vs `lem-trf-nodal-curve-lci-criterion`: nodal-curve-lci-criterion is a global curve equivalence and only uses the Jacobian calculation as an ingredient.
- `lem-trf-completed-jacobian-differentials` vs `lem-trf-nodal-normalization-adjunction`: nodal-normalization-adjunction concerns normalization and adjunction at a node, not completed Kähler differentials.
- `lem-trf-field-extension-completion-presentation` vs `lem-trf-separable-closed-point-formal-presentation`: the auxiliary isolates the arbitrary chosen presentation after a `k`-embedded residue-field extension; the item also asserts the original presentation, Jacobian comparison, and local field-change properties.
- `lem-trf-field-extension-completion-presentation` vs `lem-sc-etale-base-change-geometric`: the existing node concerns geometric étale base change, not completion of a tensor-localized finite-type algebra.
- `lem-trf-field-extension-completion-presentation` vs `lem-sc-etale-faithfully-flat-local`: the existing node states faithful flatness for an étale local map, not transport of a completed power-series quotient.
- `lem-trf-field-extension-completion-presentation` vs `lem-sc-etale-local-ring-faithfully-flat-descent`: the existing node is a descent criterion for étale local rings, not a completion presentation.
- `lem-trf-field-extension-completion-presentation` vs `lem-sc-etale-local-ring-stalk-faithfully-flat`: the existing node concerns stalkwise étale flatness, not coefficient extension of completed local rings.
- `lem-trf-field-extension-completion-presentation` vs `lem-sc-lfp-field-extension-pointwise-descent`: the existing node gives pointwise descent for locally finite-presentation morphisms, not an explicit completed power-series isomorphism.
