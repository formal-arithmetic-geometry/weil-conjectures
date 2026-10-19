# WeilConjectures.sfScalarExtension_exact_triangulated

## Reason

Document the proof-local commands flagged by the stage-3 interface checker. The retained
proof adds two private helpers comparing raw tensor-Hom scalar localization with Verdier
rationalization, and proves the existing exactness theorem. The helpers need extra universe
names and tensor notation. Local irreducibility keeps the chosen triangulation datum folded
while elaborating its localization API. Backward elaboration options match the published
coefficient interfaces. All four original public imports stay identical. Added dependencies
are proof-only imports. No public declaration, definition, target meaning or instance changes.

## Old

The existing public signature is:

```lean
theorem sfScalarExtension_exact_triangulated
    (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u}) :
    ∃ h : (sfRationalScalarExtension l E Y D.p hl L ι).CommShift ℤ,
      (fun [commShift : (sfRationalScalarExtension l E Y D.p hl L ι).CommShift ℤ] ↦
        (sfRationalScalarExtension l E Y D.p hl L ι).IsTriangulated) (commShift := h)
```

The file-level commands after `public section` were:

```lean
set_option autoImplicit false
universe d u
open CategoryTheory
```

The theorem's proof was `by sorry`, with no private localization helpers.

## New

The public signature above is identical, and its proof is complete. The two new helpers
`rawComparison` and `rawLocalization` are private and proved without holes. Additional
commands used solely to elaborate these proofs are:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe d u r v
open scoped TensorProduct
open TensorProduct
attribute [local irreducible] sfRationalTriangulationDatum
```

The last attribute is inside `namespace WeilConjectures` and is local. The existing theorem
also has `set_option linter.unusedVariables false in` to suppress proof-local unused-variable
warnings. The options, open commands, universe declarations and local attribute do not alter
importers' elaboration environments. There is no added exported notation or attribute.

## Users

Ran `tools/downstream.py Sheaf.Paper.ScalarExtensionExactIntrinsic --uses
sfScalarExtension_exact_triangulated`: 993 transitively downstream modules; the only textual
use of the declaration is its own declaration. The four direct importers were also checked
with `--direct --uses`. Their statements keep the same meaning because every public
signature and definition, and all public imports, remain identical. Their private access to
proof dependencies is unchanged. No consumer adaptation is needed. The table lists the
item and all direct importers; the 993 transitive importers inherit this unchanged API.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ScalarExtensionExactIntrinsic | D4 | Public signatures and definitions unchanged; no adaptation |
| Sheaf.Paper.BasicOperationsCoefficientReduction | K2 | Public signatures and definitions unchanged; no adaptation |
| Sheaf.Paper.ConstructibleTruncations | Z8 | Public signatures and definitions unchanged; no adaptation |
| Sheaf.Paper.SfAlgebraicallyClosedCoefficients | unclaimed | Public signatures and definitions unchanged; no adaptation |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Public signatures and definitions unchanged; no adaptation |

## Status

landed 20261019T002523-L-2146945 2026-10-19 (merge of deliver/D4/Sheaf.Paper.ScalarExtensionExactIntrinsic)
