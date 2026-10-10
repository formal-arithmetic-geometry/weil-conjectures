1. Files written

- `dag/nodes/sec-picard-framework/thm-pc-f-representable.json`: split statement; Mathlib search found no exact match.
- `lem-pc-sections-higher-direct-image-H`: unsplit helper; no Mathlib match.
- `lem-pc-finite-free-complex-higher-direct-image`: unsplit helper; no Mathlib match.
- `lem-pc-finite-sections-higher-direct-image`: unsplit helper; no Mathlib match.
- `lem-pc-h-pullback-linear-equivalence`: unsplit helper; no Mathlib match.
- `lem-pc-higher-direct-image-restrict`: unsplit helper; no Mathlib match.
- `lem-pc-h-vanishing-topological-dimension`: unsplit helper; no Mathlib match.
- `lem-pc-arrow-iso-pullback-counit`: unsplit helper; no Mathlib match.
- `citations.json`: 28 verbatim step-to-node citations.

2. Attachments

- `AlgebraicGeometry.isRepresentable_picardFunctorInvertibleDirectImage` belongs to `thm-pc-f-representable`, but its transitive sorry audit remains open.
- `AlgebraicGeometry.Scheme.Modules.exists_addEquiv_sections_higherDirectImage_H` is represented by `lem-pc-sections-higher-direct-image-H`.
- `AlgebraicGeometry.Scheme.Modules.exists_isFiniteFreeComplex_higherDirectImage` is represented by `lem-pc-finite-free-complex-higher-direct-image`.
- `AlgebraicGeometry.Scheme.Modules.finite_sections_higherDirectImage` is represented by `lem-pc-finite-sections-higher-direct-image`.
- `AlgebraicGeometry.Scheme.Modules.nonempty_H_pullback_linearEquiv` is represented by `lem-pc-h-pullback-linear-equivalence`.
- `AlgebraicGeometry.Scheme.Modules.nonempty_higherDirectImage_iso_restrict` is represented by `lem-pc-higher-direct-image-restrict`.
- `AlgebraicGeometry.Scheme.Modules.subsingleton_H_of_topologicalKrullDim_lt` is represented by `lem-pc-h-vanishing-topological-dimension`.
- `AlgebraicGeometry.nonempty_arrowIso_pullback_directImageCounit` is represented by `lem-pc-arrow-iso-pullback-counit`.

3. WANTED

- WANTED: none; the source Lean docstrings and imported blueprint statement were available.

4. What was wrong or incomplete

- The imported theorem declaration has an open transitive sorry audit. I retained the statement and split its proof, and recorded the five missing helper declarations as statement-only nodes rather than treating the theorem as closed.
- Two initially proposed helper nodes were removed as duplicates: field-extension cohomology is already stated by `lem-pc-flat-base-change-cohom`, and dimension vanishing by `lem-sc-noetherian-cohomology-above-dimension`.
- Existing statements outside this unit's one-step sketch remain recorded as tool uses in `split_report.tool_uses`; they are the black-box construction inputs used by the imported Lean theorem.
- The source blueprint gives one compressed proof step; the DAG item had already expanded it into three arguments. I checked those arguments against `ZeroScheme.lean` lines 617-746 and kept the route through the normalized universal module, open perfect locus, zero-scheme dictionary, and Yoneda inverse.
- Mathlib searches found only generic representability, restriction, and linear-equivalence infrastructure, not the project-specific cohomology or Picard statements.

## Review by H1

I read the item source in `WeilConjectures/AlgebraicGeometry/Picard/ZeroScheme.lean`, including the theorem docstring and body at lines 617-746, and the unit route in `dag/units/sk-thm-picard-f-representable.json`. The statement agrees with the Stacks Lemma 44.6.4 / Tag 0B9X formulation: a separably closed base field, smooth projective genus-$g$ curve with rational point, and the open subfunctor $F$ represented by an open of the degree-$g$ Hilbert scheme.

For step 1 I checked the cited existing nodes for Hilbert representability, normalization, the open subfunctor, perfect locus, projection formula, and flat base change. The six cohomology helper nodes are sourced from the exact slopmaster2 declarations and are cited as the infrastructure they provide; their hypotheses (properness, finite presentation, flatness, affine/Noetherian bases, and injective resolutions) were copied from the declarations. Step 2 uses the zero-scheme reconstruction, Hilbert functor, universal divisor, and curve Hilbert representability statements. Step 3 uses divisor pullback, the open-locus characterization, normalization, Cartier classification, universal adjoint section, and the direct-image counit base-change statement; these are exactly the facts used in the two inverse composites. Every citation in `citations.json` is a verbatim prefix of its node statement.

I tested the helper statements on the relevant edge cases in their declarations (degree $q=0$, open-immersion restriction, and a field-extension pullback) and did not alter their hypotheses. The theorem is split, while its five transitive helper declarations remain unsplit statement nodes.

5. What I could not finish

- No Lean proof was written, as required for stage 1. The helper nodes remain unsplit for later workers.

## Second reading by H1

- Item statement: checked against Stacks Tag 0B9X (Lemma 44.6.4, `pic.tex`, `pic-lemma-open-representable`) and the blueprint ancestor; verdict: hypotheses and open Hilbert representative agree.
- Step 1: checked all cited Hilbert, normalization, open-locus, perfect-locus, projection-formula, base-change, restriction, and dimension-vanishing statements; verdict: each supplies the fact used and the displayed normalization is valid.
- Step 2: checked the zero-scheme reconstruction, Hilbert functor, Hilbert representability, and universal-divisor statements; verdict: the divisor gives the claimed degree-$g$ Hilbert classifying map.
- Step 3: checked divisor pullback, open-locus characterization, Cartier criterion, universal adjoint section, zero-scheme reconstruction, and counit base change; verdict: both inverse composites are explicitly computed and the normalization twist cancels.
- New node `lem-pc-sections-higher-direct-image-H`: checked against `DirectImage.lean` lines 307--324 and recorded searches; verdict: hypotheses and naturality match.
- New node `lem-pc-finite-free-complex-higher-direct-image`: checked against `DirectImage.lean` lines 574--615; verdict: local finite-free complex and base-change quantifiers match.
- New node `lem-pc-finite-sections-higher-direct-image`: checked against `DirectImage.lean` lines 617--632; verdict: properness, affine Noetherian base, quasi-coherence, and finiteness match.
- New node `lem-pc-higher-direct-image-restrict`: checked against `DirectImage.lean` lines 421--440; verdict: open-immersion restriction and injective-resolution hypotheses match.
- New node `lem-pc-arrow-iso-pullback-counit`: checked against `ZeroScheme.lean` lines 156--175; verdict: repaired to introduce the base field, rational point, resolution family, and normalized Picard object through its definition nodes.
- Edge cases: checked $q=0$, a field-valued base, the empty base, and degree $g=0$; verdict: no statement changes are forced.

Changes: repaired the arrow helper's self-contained statement and dependencies; corrected the stale report wording about import status and helper count; retained the five helper nodes because their facts are used and not duplicated in the DAG.
