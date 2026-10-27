# WeilConjectures.completedWeakSheafify

## Reason

Preflight requests a change record for the added private instance and the command
removing its instance attribute. The private helper fixes typeclass search for
ring-sheafification in two private constant-section proofs. It is declared after
all pre-existing definitions preceding those proofs, and its instance attribute is
removed immediately after the private proofs. No public signature or pre-existing
definition body changes. The additional category namespace opening is used only
for proof equations. Public imports are unchanged.

## Old

No declaration named `WeilConjectures.completedWeakSheafify` existed.
The namespace opening was:

```lean
open CategoryTheory CategoryTheory.Limits Opposite
```

## New

```lean
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits Opposite

private instance completedWeakSheafify (W : Scheme.{t}) :
    (sheafToPresheaf (ProEt.topology W) CommRingCat.{max u (t + 1)}).IsRightAdjoint :=
  (integralCoefficientRingSheafify.{t, u} W).isRightAdjoint

attribute [-instance] completedWeakSheafify
```

The instance is active only between its declaration and the displayed attribute
command, covering the two proved private helpers `completedDirect_unit` and
`completedConstant_naturality`. Its data comes from the existing sheafification
instance, with no new existence choice. The helper cannot occur in a public
signature or definition, and is disabled before the remaining declarations.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompletedCoefficientRingedCoherence | K5 | Three theorem holes closed; private proof helper added; public API unchanged. |

`tools/downstream.py` and textual searches find no current Lean importer or external
user of this module. The parent DAG dependencies remain; the slice theorem is not
withdrawn. No consumer needs adaptation because public statements and definitions
are preserved.

## Status

landed 20261023T103015-L-3033774 2026-10-23 (merge of deliver/K5/Sheaf.Paper.CompletedCoefficientRingedCoherence)
