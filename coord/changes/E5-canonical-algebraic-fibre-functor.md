# lisseAlgebraicFiberFunctor

## Reason

The old definition chooses a witness from a mere existence theorem. Its prescribed object
values and restrictions to separate coefficient models do not determine the coefficient
comparison maps: arbitrary coherent comparisons may be twisted by fibre automorphisms.
Consequently this choice neither satisfies the project's construction rule nor supplies
the scalar comparison normalization needed for transport between geometric points.

Construct the coefficient-pair functor from the unique coherent comparison family whose
restriction from the least coefficient field has the prescribed raw-comparison formula.
The existing endomorphism restriction theorem makes that normalized family unique.
Only then lift this concrete functor through the explicit coefficient localization.
The choice in the normalization definition is backed by a proved ExistsUnique statement;
it is not a choice of arbitrary data from an unproved mere existence statement.

The integral and rational functor definitions, all existing public signatures, the
fixed-model functor, the object formulas and the algebraic existence interface are retained.
The existence theorem now uses the concrete construction and its restriction isomorphism.
No WeilConjectures file is changed. The existing private general Grothendieck functor,
inversion and restriction helpers are replaced by the normalized categorical API.

## Old

```lean
noncomputable def lisseAlgebraicFiberFunctor :
    LisseAlgebraicSheaf l Y K ⥤ ModuleCat.{d + 1} K :=
  (lisseAlgebraicFiberFunctor_exists l Y y K).choose
```

## New

```lean
noncomputable def lisseAlgebraicFiberFunctor :
    LisseAlgebraicSheaf l Y K ⥤ ModuleCat.{d + 1} K :=
  Localization.Construction.lift (lisseCanonicalCoefficientFiberFunctor l Y y K)
    (lisseCanonicalCoefficientFiberFunctor_inverts l Y y K)
```

The new public helpers in this module describe the rational map specification, concrete
coefficient-model fibre functors, raw comparisons, endomorphism detection, and the concrete
coefficient-pair functor and its inversion property. They are attached to the existing
node def-pod-lisse-adic-fibre-functors. Generic unique normalization and its path and
restriction theorems are proved in Sheaf.Paper.NormalizedFibreComparisons.

## Users

`tools/downstream.py Sheaf.Paper.LisseAdicFiberFunctors --uses
lisseAlgebraicFiberFunctor` lists six existing modules (92 transitive downstream
modules in total). The table also records the two new modules in this delivery that use
the repaired functor or its construction helpers.
No downstream module unfolds the chosen witness or calls the algebraic
existence theorem to calculate maps. The functor retains its category, codomain and exact
object formula. Its meaning is the normalized geometric fibre functor specified by the
existing node. Every target depending on this definition requires the statement/definition
review to be reopened under stages/2-statements.md §4; no target signature is changed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed | Same functor type and object theorem; unchanged source compiled against the repair. |
| Sheaf.Paper.AlgebraicFibrePathConstruction | E5, new | Constructs the path on coefficient models, proves compatibility with the normalized comparisons, and descends it through localization. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | Same functor type and object theorem; unchanged source compiled against the repair. |
| Sheaf.Paper.EtaleWeilFundamentalRepresentation | unclaimed | Uses the same algebraic functor and object formula; unchanged source compiled against the repair. |
| Sheaf.Paper.FibreFunctorBasepointTransport | E5 | Proved using the concrete coefficient-pair path and localization descent. |
| Sheaf.Paper.FibreFunctorBasepointTransportData | E5, new | Retains the original algebraic fibre-path interface with the same functor type and object formula. |
| Sheaf.Paper.GaloisLisseCorrespondenceData | unclaimed | Same declarations and bodies; compiled after the local transparency adjustments recorded in E5-galois-fibre-transparency.md. |
| Sheaf.Paper.LisseAdicFiberFunctors | unclaimed | Construction repaired; all existing public signatures retained and all proofs complete. |

Holder check: coordination records read on 2026-10-21. LisseAdicSheaves is held by H6
and is not modified. There are no forced adaptations of another group's module.

## Status

landed 20261020T230733-L-606316 2026-10-20 (merge of deliver/E5/Sheaf.Paper.FibreFunctorBasepointTransport)
