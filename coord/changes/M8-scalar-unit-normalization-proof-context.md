# AlgebraicGeometry.Scheme.proEtaleInverseImage_scalarUnit_normalization

## Reason

Stage-3 preflight requests a change record for added proof-context commands
(variable, namespace, local attribute and elaboration option commands). They
support private proved helpers only. All existing public declaration signatures,
definition bodies, docstrings, visibility and public imports remain unchanged.
There is no semantic definition repair or new public declaration.

## Old

The file began its generic public context with:

```lean
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules MonoidalCategory
open scoped ChangeOfRings
open CanonicalRingedTensorComparisonOnSmallSites
namespace SheafOfModules
universe c v d z w
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] monoidalCategory
```

The original theorem was:

```lean
theorem proEtaleInverseImage_scalarUnit_normalization
    {X Y : Scheme.{u}} (h : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    Nonempty (ProEtaleScalarUnitNormalization h R) := by
  sorry
```

## New

The same public context and theorem signature are retained verbatim. The theorem
body is a complete proof. Two proof-only imports expose existing private proved
helpers from ProEtaleAlgebraicInverseImage and CochainInverseComparison.

Private named canonical sheafification/compose instances are proved and registered
with `attribute [local instance]` only. Closed IdentityScalars, PureSections and
NormalizationFormula sections introduce parameters used solely in private helpers.
Their elaboration transparency options are local to their sections. The named
ringedComparisonPure construction is kept locally irreducible in the last section;
the comparison field type aliases are locally reducible to avoid unfolding entire
section constructions during rewriting. The specified inverse-image abbreviation
is locally reducible for the private algebraic-presentation construction and is
restored to the original local irreducible status afterwards. All these attributes
are local and introduce no exported instance or declaration attribute.

The identity scalar extension is constructed sectionwise using the existing
ModuleCat.extendScalarsId, followed by module sheafification and its invertible
counit. The given comparison is evaluated on the unit of a product test sheaf.
Existing pure-section restriction/naturality proofs are reused from the library.
The module compiles under the original compile and heartbeat limits.

## Users

`python3 tools/downstream.py
Sheaf.AlgebraicGeometry.ProEtaleInverseImageScalarUnitNormalization` reports zero
current Lean importers. DAG parents are retained, including the held pro-etale
tensor-comparison parent, and every existing public signature and definition is
unchanged. No consumer adaptation is needed. Future parent imports have the same
public interface. The target statements retain their meaning.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ProEtaleInverseImageScalarUnitNormalization | M8 | Complete proof; unchanged public interface and data definitions |
| Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison | F1; not edited | DAG precursor attachments separated; no Lean source change or adaptation |
| Sheaf.AlgebraicGeometry.ProEtaleAlgebraicInverseImage | unclaimed; not edited | DAG dependency corrected to underlying-unit precursor node; no Lean source change |

## Status

landed 20261021T173338-L-3588944 2026-10-21 (merge of deliver/M8/Sheaf.AlgebraicGeometry.ProEtaleInverseImageScalarUnitNormalization)
