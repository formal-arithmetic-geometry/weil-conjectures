# CochainComplex.exists_functorial_bounded_injective_resolution

## Reason

The completed proof adds private helper namespaces, scoped variables, namespace openings,
and private instances. The preflight classifies the changed nondeclaration commands as an
interface change and requires this record. No existing declaration signature, visibility,
public import, or definition is changed. Only the item module is edited. The draft
object-resolution proof is withheld because E1 now holds that dependency; no adaptation
of it is delivered. No target meaning changes.

## Old

The item had the following namespace opening before its public theorems:

```lean
open CategoryTheory CategoryTheory.Limits ZeroObject

namespace CochainComplex
```

There were no private helper namespaces or instances. The totalization construction theorem
had a `by sorry` proof, while the assembly theorem already had its complete proof.

## New

The totalization module opens:

```lean
open CategoryTheory CategoryTheory.Limits ZeroObject ComplexShape
open HomologicalComplex₂
```

Its private comparison lemmas are in `HomologicalComplex₂`, with scoped variables
`{C : Type u} [Category.{v} C] [Abelian C]`. Its private totalization construction is in
`CochainComplex.FunctorialInjectiveTotal`, with those variables and:

```lean
variable (E : C ⥤ CochainComplex C ℕ)
variable (ε : single₀ C ⟶ E)
variable [E.PreservesZeroMorphisms]
```

The private `hasTotal` instance supplies the canonical totalization with the finite-diagonal
existence proof. It applies only to the private bicomplex construction.

The public theorem signatures and visibility remain verbatim unchanged. The totalization
proof constructs the existential data without new holes; the assembly proof is unchanged.
All new helpers are private, and all public imports are unchanged.

## Users

`tools/downstream.py` was run on both draft modules with their public theorem names. The two
actual public callers are the item itself and
`Sheaf.Paper.CondensedOpenClosedRecollement`. The table includes the item, the withheld dependency, and
all modules in the downstream import closure reported by those commands. No downstream
statement or definition changes its meaning, and no downstream edit is necessary.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.FunctorialObjectResolution | E1 | Unchanged; draft proof withheld. |
| Sheaf.Algebra.Homology.FunctorialBoundedInjectiveResolution | D4 | Proof completed; public signatures unchanged. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | Not affected: public signatures and public imports unchanged. |
| Sheaf.Paper.CondensedConstructibleExtensionTower | unclaimed | Not affected: public signatures and public imports unchanged. |
| Sheaf.Paper.CondensedConstructibleOneStep | J1 | Not affected: public signatures and public imports unchanged. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | Not affected: public signatures and public imports unchanged. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | G2 | Not affected: public signatures and public imports unchanged. |
| Sheaf.Paper.CondensedLocalPieceHomContinuity | H3 | Not affected: public signatures and public imports unchanged. |
| Sheaf.Paper.CondensedOpenClosedRecollement | unclaimed | Not affected: public signatures and public imports unchanged. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | Not affected: public signatures and public imports unchanged. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | Not affected: public signatures and public imports unchanged. |
| Sheaf.Paper.CondensedQbarExchangeEquality | A3 | Not affected: public signatures and public imports unchanged. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | Not affected: public signatures and public imports unchanged. |
| Sheaf.Paper.CondensedStratumModelAssembly | A4 | Not affected: public signatures and public imports unchanged. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | A2 | Not affected: public signatures and public imports unchanged. |
| TargetsCheck | unclaimed | Not affected: public signatures and public imports unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Not affected: public signatures and public imports unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Not affected: public signatures and public imports unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | Not affected: public signatures and public imports unchanged. |

## Status

landed 20261015T202026-L-1475709 2026-10-15 (merge of deliver/D4/Sheaf.Algebra.Homology.FunctorialBoundedInjectiveResolution)
