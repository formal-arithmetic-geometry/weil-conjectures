# FieldTheory.algebraic_separable_extension_is_filtered_colimit_smooth

## Reason

The proof uses private helpers for the finite-subset diagram and its colimit.
These helpers share the field and algebra variables declared by a new `variable`
command. Preflight conservatively treats this command as a change to what
importers see and requests this record. It creates no declaration or instance.
Every helper is private; the existing public theorem's signature, visibility and
public imports stay identical. There is no forced consumer adaptation.

## Old

The scope commands before the public theorem, verbatim:

```lean
universe u v

open CategoryTheory

namespace FieldTheory
```

The existing public signature, verbatim:

```lean
theorem algebraic_separable_extension_is_filtered_colimit_smooth
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] [Algebra.IsSeparable K L] :
    CategoryTheory.ObjectProperty.ind.{v}
      (fun B : CommAlgCat.{v} K ↦
        IsField B ∧ Module.Finite K B ∧ Algebra.IsSeparable K B ∧ Algebra.Smooth K B)
      (CommAlgCat.of K L)
```

## New

The scope commands before the private helpers, verbatim:

```lean
universe u v

open CategoryTheory

namespace FieldTheory

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
```

The public theorem keeps exactly the Old signature. Its explicit binders shadow
these helper variables; no extra assumption or universe is introduced. The new
private definitions construct the actual diagram, cocone and universal map, and
all their proof fields are proved. No data is chosen from an unproved theorem.

The scheme-level proof import
`Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres` is replaced by the
Mathlib algebra-level smoothness instance, already available through the retained
etale-field import. The three added Mathlib imports are proof-only. The node's
proof and proof dependencies are updated accordingly.

## Users

The source import closure contains the following thirteen consumers. The only
direct importer is `FiniteEtaleFieldLimitDescent`; no consumer mentions the proved
theorem in Lean code yet. The table includes every transitive importer. Existing
statements and target meanings remain identical, so no target review reopens.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.FieldTheory.AlgebraicSeparableSmooth | M8 | Prove the existing theorem; add private helpers and their shared variables. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.AlgebraicFieldLimit | unclaimed | Same imported public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.ArithmeticLiftFibrePath | V9 | Same imported public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiniteEtaleFieldLimitDescent | T9 | Same imported public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiniteEtaleWeilTransport | unclaimed | Same imported public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.PadicCharactersH1 | unclaimed | Same imported public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.RankOneFiniteGeometricImageCurve | unclaimed | Same imported public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.WeilTwistedPaths | unclaimed | Same imported public interface; no adaptation. |
| Sheaf.Paper.DenseOpenPiOneSurjective | E3 | Same imported public interface; no adaptation. |
| Sheaf.Paper.FiniteConstantH1Pi1 | unclaimed | Same imported public interface; no adaptation. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed | Same imported public interface; no adaptation. |
| Sheaf.Paper.RealBoundaryLocalConstants | unclaimed | Same imported public interface; no adaptation. |
| Sheaf.Paper.RealBoundaryPathIndependence | unclaimed | Same imported public interface; no adaptation. |
| Sheaf.Paper.RealSheafSections | unclaimed | Same imported public interface; no adaptation. |

## Status

landed 20261019T231243-L-566294 2026-10-19 (merge of deliver/M8/Sheaf.FieldTheory.AlgebraicSeparableSmooth)
