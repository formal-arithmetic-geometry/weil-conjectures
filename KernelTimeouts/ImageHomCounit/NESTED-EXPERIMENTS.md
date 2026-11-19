# ImageHomCounit: nested representation audit

Source: `212f97dd22a`, `AlgebraicGeometry/IndEtaleMapping/IndEtaleDerivedImageHomCounit`,
`imageHomIso_counit`; Lean/Mathlib 4.35.0, 200,000 heartbeats. Timings
are reused from `WORKPLAN-EXPERIMENTS.md`; unchanged fixture links are in
`probes/nd/`. Kernel-only time/heartbeats and synthesis time are unavailable.

## Original context and A records

The expensive site is `exact h`, comparing the unchanged
`conjugateEquiv_counit` result with the declared equality. Both outer
propositions are `Eq` over `CategoryStruct.comp`. The first difference in
the morphism type and both sides is inferred raw `DerivedCategory (Sheaf ...)`
versus declared `DerivedCategoryModule A X`. The latter abbrev exposes raw
`DerivedCategory`, but an inner wrapper/raw difference remains after the
first expansion. The helper application alone is cheap.
Section-10 fields shared by the rows: instance depth and field count are
the unchanged original adjunction/functor structure; the final equality
uses the morphism type and both composition sides. Source elaboration
reruns in each variant. Explicit instance terms, synthesis time,
Kernel-only time/heartbeats, and same-term instance replay are unavailable.
Prior diagnostics counted extensive `Functor.obj`/`Add.add` unfolding
downstream, without isolating a particular inner argument.

| Record | Target representation | Elaborated first difference | Kernel result | Wall s | CPU user+sys s | RSS KB | Same proof/site/obligation | Confidence |
|---|---|---|---|---:|---:|---:|---|---|
| A-IHC-0 | original declared equality | outer raw/wrapper | ok, expensive | 54.94 | 53.90+1.08 | 7,487,640 | yes | confirmed site |
| A-IHC-W | delta-expand original declared wrappers once | later inner wrapper/raw after proof arguments | ok, more expensive | 83.45 | 82.29+1.18 | 9,865,804 | yes | confirmed negative one-stage alignment |
| A-IHC-I | exact inferred `type_of%` of the original term | no difference in equality type and sides | ok | 2.60 | 1.73+0.90 | 2,816,600 | same `h`, final `exact`, DefEq obligation | confirmed full alignment control |

The `UnfoldWrapperHead` and `UniformInferredHead` probes verify that the
elaborated pair changes. All three normally Kernel check and the fast row
keeps the original proof term. `UniformInferred` aligns the entire target,
not one wrapper occurrence, so it cannot attribute the cost to the first
visible wrapper. It is a strong within-case fast control and not an
independent nearby declaration. A/B provider symmetry is unavailable:
the imported `conjugateEquiv_counit` result is already elaborated, and a
local source spelling change left its stored pair unchanged in prior
negative probes. Explicit-instance replay and separate synthesis timing
were not performed.

## D: representation provenance

| Role | Inferred proof type | Declared goal |
|---|---|---|
| Original declaration | imported `conjugateEquiv_counit` instantiated locally | local `imageHomIso_counit` equality |
| Data | raw derived category, compositions, functor objects, counits | same mathematical maps via `DerivedCategoryModule` wrapper |
| Wrapper path | raw `DerivedCategory (Sheaf ...)` | outer and inner `DerivedCategoryModule` abbrevs |
| Instance/proof path | concrete category and `HasDerivedCategory` terms | wrapper-generated category/proof terms, including `_proof_n` deeper in the pair |
| Construction | generic adjunction theorem instantiated concretely | concrete source statement |

First divergence is the derived-category type argument under
`Quiver.Hom`; after one wrapper expansion, a deeper data wrapper remains.
A differing `HasSheafify` proof argument occurs before that inner data
divergence in raw traversal but is not established as a cost source.
Changing local variable type spelling did not rewrite the stored result.
D confidence: confirmed for the wrapper provenance and nested difference,
unresolved for the dominant inner conversion.

**Evidence level:** section-12 Level 1 for full target representation
alignment at the exact final conversion, with the qualification that the
control changes several nested occurrences. No Level 2/3 or strict
four-quadrant symmetry result.
