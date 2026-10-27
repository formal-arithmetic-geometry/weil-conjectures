# AlgebraicGeometry.Proj.commonDegreeTwistInvertible

## Reason

The proof introduces private helpers, namespace openings, and a private local monoidal
instance. Preflight conservatively classifies these commands as a visible-scope change.
The theorem signature and all public imports stay verbatim. The local instance selects
the existing scheme-module monoidal structure, definitionally the same structure used by
`Scheme.Modules.tensorObj`, `tensorPow`, and `tmulSection`. It adds no exported instance.
No existing definition or target meaning changes.

## Old

After the existing variables, there were no additional scope commands:

```lean
variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]
```

## New

The same variables are followed by these commands and a private abbreviation:

```lean
open ProjectiveSpectrum.Twist HomogeneousLocalization Opposite MonoidalCategory
open Scheme.Modules

private abbrev schemeMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf

attribute [local instance] schemeMonoidal
```

All other added declarations are private proof helpers. The original public theorem
statement is textually identical, and the file compiles cleanly in 46.7 seconds.

## Users

`tools/downstream.py Sheaf.TraceFormula.ProjCommonDegreeTwistInvertible --uses
AlgebraicGeometry.Proj.commonDegreeTwistInvertible` lists these declaration users.
The consumer's existing call uses the identical theorem signature. No adaptation is needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.TraceFormula.ProjCommonDegreeTwistInvertible | H9 | Its original theorem is proved. |
| Sheaf.TraceFormula.ProjQcOpenTwistAmple | unclaimed | No signature or behavior change. |

## Status

landed 20261023T231542-L-3616386 2026-10-23 (merge of deliver/H9/Sheaf.TraceFormula.ProjCommonDegreeTwistInvertible)
