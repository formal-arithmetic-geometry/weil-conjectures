# AlgebraicGeometry.Etale.openScalarRestrictionMap_isIso

## Reason

The coefficient normalization statements must use the fixed canonical open and
scalar functors independently of the complete comparison package. Extracting their
definitions avoids an import cycle. The qualified names and defining data of the
18 moved declarations are preserved; the original module publicly imports the new
module. No target statement or source-library declaration changes.

The original `EtaleOpenTensorComparisons` structure is preserved verbatim. Its
projection, flatness, restriction-unit, counit and tensor-associativity fields are
proved from published constructions. The scalar inverse mate is proved invertible
from the sectionwise coefficient square and the published scalar/pullback mate.
The independent coefficient coherence and K-flat assertions receive separate modules.

## Old

The declarations below, and the canonical definitions listed in the Lean attachment
of `lem-coef-etale-open-comparison-data`, lived in
`Sheaf.SixFunctors.EtaleOpenTensor`.

```lean
@[instance] theorem openScalarRestrictionMap_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (openScalarRestrictionMap φ j)
```

```lean
theorem etaleOpenTensorComparisons
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    EtaleOpenTensorComparisons φ j
```

## New

The first declaration and the 17 associated canonical definitions live in
`Sheaf.SixFunctors.EtaleOpenTensorDefs`, with the same qualified names, signatures,
attributes and defining data. Only their blueprint references change. The original
module reexports them through:

```lean
public import Sheaf.SixFunctors.EtaleOpenTensorDefs
```

```lean
@[instance] theorem openScalarRestrictionMap_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (openScalarRestrictionMap φ j)
```

The original structure and main signature remain:

```lean
theorem etaleOpenTensorComparisons
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    EtaleOpenTensorComparisons φ j
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.EtaleOpenTensor | K3 | Same public interface; complete assembly of the comparison fields. |
| Sheaf.Paper.EtaleLocallyClosedShriek | unclaimed | Uses the same canonical declarations through the public reexport. |
| Sheaf.Paper.InternalAdjunctionPairingChange | unclaimed | Same comparison structure and theorem. |
| Sheaf.Paper.FiniteCoefficientHomChange | unclaimed | Same comparison structure and theorem. |
| Sheaf.Paper.ProperOpenCoefficientMate | V3 | Same comparison structure and theorem; no edits to this held module. |
| Sheaf.Paper.OpenRestrictionScalarExchange | unclaimed | Uses the moved open restriction/scalar comparison declarations through their public interface; no edits to this module. |
| Sheaf.SixFunctors.EtaleOpenScalarCoherence | new, K3 | States only the coefficient normalization and coherence subproblem. |
| Sheaf.SixFunctors.EtaleOpenKFlat | new, K3 | States only preservation of acyclic tensor tests. |

These are all direct importers and all existing modules using the moved public names,
as checked by the import graph and `tools/downstream.py --uses`. The change preserves
mathematical meaning; it does not reopen a target statement by changing a definition.
Compilation evidence is recorded in the report.

## Status

landed 20261020T233153-L-902140 2026-10-20 (merge of deliver/K3/Sheaf.SixFunctors.EtaleOpenTensor)
