# ImageHomCounit: exact Kernel site

**Declaration:** `AlgebraicGeometry.Etale.IndEtaleMapping.imageHomIso_counit`,
origin `212f97dd22a`.

## Phase gate and bisect

With `-DElab.async=false`, Before takes 54.53 s with Kernel and 2.90 s with
`-Ddebug.skipKernelTC=true`; peak RSS is 7,458,644 KB versus 2,785,800 KB.
The type-only probe `probes/TypeOnly.lean` is 2.70 s with Kernel on. The full
Before is 55.53 s; After is 2.60 s.

`probes/HaveApplication.lean` binds the old `conjugateEquiv_counit` result as
`h` and then uses `sorry`: 2.70 s. `probes/FinalExact.lean` changes only the
last line to `exact h`: 54.83 s, 7,459,004 KB. Therefore the exact site is
the final inferred-type-to-declared-type conversion, not construction of
`h` or checking the theorem type.

## Expressions and diagnostics

`probes/PrintConversion.lean` prints both expressions with
`pp.explicit`, `pp.proofs`, and `pp.universes`. The inferred equality is over
`DerivedCategory (Sheaf T.left.Etale (ModuleCat A))`; the declaration is over
the wrapper `DerivedCategoryModule A T.left`. The two sides contain distinct
`instCategoryDerivedCategory`, `HasDerivedCategory.ofIsGrothendieckAbelian`,
and generated `DerivedCategoryModule._proof_1/_proof_2` arguments. The
pretty-printed mathematical morphisms look the same, but the wrapper and
concrete derived-category instance paths differ under `Eq`.

The diagnostic run
`-Ddiagnostics=true -Ddiagnostics.threshold=1` on `FinalExact.lean` reports
842,612 Kernel unfolds of `Add.add`, 604,585 of `Functor.obj`, and 423,893 of
`DFunLike.coe`. These are the reduction chain triggered by the conversion;
they are not independent root causes.

## Classification

Primary mechanism: **E (representation/instance/interface mismatch)**.
Contributing mechanisms: **A** and **C** because the mismatched derived
category paths are compared beneath dependent morphism domains. Evidence:
**confirmed** for the final conversion and **strongly supported** for E/A/C.
The fixed theorem uses `imageHomIso_counit` directly, while the old proof asks
Kernel to reconcile the concrete adjunction expression with the wrapper type.
