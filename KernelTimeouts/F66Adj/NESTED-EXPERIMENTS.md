# F66Adj: nested representation audit

Source: `f66ad18a9ed`, `AlgebraicGeometry/IndEtaleMapping/IndEtaleDerivedImageHomComp`,
`imageHomIso_naturality`; Lean/Mathlib 4.35.0, 400,000 heartbeats. Timings
are retained from `WORKPLAN-EXPERIMENTS.md`; measured fixtures were linked
unchanged to `probes/nd/`. Kernel-only time/heartbeats and separate instance
synthesis time were not recorded.

## Original context and A records

The cost site is argument 39 (`hR`) of `homIso_naturality_of_counit` after
38 actual category, functor, adjunction, isomorphism, object, morphism, and
proof arguments. The proof proposition is an `Eq` over nested
`CategoryStruct.comp`/`Functor.map`/`NatTrans.app` data. At its morphism type
and both equation sides, the first difference is a `DerivedCategoryModule`
scheme argument: `Over.left (Over.mk f.left)` in the supplied proof versus
the helper's local scheme variable. The accessor can reduce to that scheme,
as checked by the `OverLeftShape` `rfl` fixture; that isolated equality is
not a timing control for argument 39.
Section-10 fields shared by the rows: instance depth and field count are
the original, unvaried helper hierarchy; both sides of the instantiated
counit equality use the scheme and derived-functor data. Source elaboration
runs for each variant. Explicit instance terms, synthesis time, Kernel-only
time/heartbeats, and same-term Kernel replay are unavailable. Prior
diagnostics do not isolate downstream unfold activity for this accessor.

| Record | Proof argument or changed factor | First divergence | Kernel result | Wall s | CPU user+sys s | RSS KB | Same site and obligation | Confidence |
|---|---|---|---|---:|---:|---:|---|---|
| A-F66-0 | `imageRestriction_counit ... (Over.mk f.left)` | accessor/local scheme | ok, expensive | 34.72 | 34.03+1.01 | 5,667,344 | yes | confirmed site |
| A-F66-R | `restriction_counit A f.left _ _` at argument 39 | monoidal instance path | ok | 3.40 | 2.79+0.92 | 2,854,984 | yes | confirmed one-argument control |
| A-F66-Q | replace only preceding tensor isomorphism | accessor/local scheme | ok, expensive | 35.12 | 34.08+0.99 | 5,631,848 | yes | negative preceding-argument control |

The same application and mathematical counit square are retained. Each
diagnostic example ends in `sorry` after the application; the full
`After.lean` theorem is checked independently. `ReplaceHRHead.lean` verifies
the changed proposition and its later, cheap monoidal-instance difference.
The replacement also changes the proof-producing interface, so the
accessor is not varied alone. A four-quadrant DefEq symmetry matrix and
explicit-instance replay were not obtained. The replacement is the matched
within-case fast control, not an independent fast declaration.

## B status

No instance-depth matrix was measured. The earlier 38 arguments and the
instantiated proof domain must remain fixed while a single scheme-provider
path is placed under successively deeper data-bearing instance layers.
`OverLeftShape` loses that original context and cannot stand in for B.

## D: representation provenance

| Role | Supplied `hR` | Expected helper binder |
|---|---|---|
| Original declaration | concrete `imageRestriction_counit` | local generic `homIso_naturality_of_counit` instantiated by 38 arguments |
| Data | restriction square through over-object and derived functors | same square through local scheme and abstract functors |
| Accessor path | `Over.left (Over.mk f.left)` then `Comma.left` | scheme local variable |
| Instance path | concrete derived-category/monoidal instances | generic-derived functor instantiation; a monoidal instance differs after replacement |
| Proof abstraction | no evidence at first divergence | no evidence at first divergence |

First divergence is below `Quiver.Hom` and `DerivedCategoryModule`, then
repeats in both equality sides. The concrete over-object producer stores
the accessor path; helper instantiation stores the local scheme. The
remaining monoidal difference is observed but cheap in the checked
replacement. D confidence: strongly supported for provenance, not for the
isolated cost of the accessor leaf.

**Evidence level:** the one-argument replacement is locally causal but
changes proof construction. Strict A symmetry and explicit replay are
missing; below section-12 Level 1. No Level 2/3.
