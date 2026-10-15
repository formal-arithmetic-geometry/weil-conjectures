# AlgebraicGeometry.ProEtale.CondensedRing coefficient-flatness and finite-pushforward instances

## Reason

Discharge two flatness obligations and finite-extension pushforward compatibility in the
item module. The delivery checker classifies changed public instance proof bodies and section
commands as interface changes, so this record documents their effect. No public statement,
non-proof definition body, visibility, priority, or public import changes.

## Old

The following declarations had proof `sorry` (verbatim signatures):

```lean
instance preservesFiniteLimits_extendScalars_padicSubfieldRingObjMap
    {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    PreservesFiniteLimits
      (Mod.extendScalars (padicSubfieldRingObjMap X ℓ h))

instance preservesFiniteLimits_extendScalars_padicSubfieldRingObjToPadicAlgCl
    (E : FiniteIntermediateField ℓ) :
    PreservesFiniteLimits
      (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E))

instance isIso_derivedPushHom_padicSubfieldRingObjMap {E F : FiniteIntermediateField ℓ}
    (h : E ≤ F) : IsIso (derivedPushHom (Profinite.padicSubfieldRingObjMap ℓ h) f)
```

## New

The signatures above are byte for byte identical. The three proofs now construct finite-free
modules, a filtered colimit of flat modules, and a compatible finite-basis decomposition of
scalar-extension units on derived categories. H10 is repaired by compacting the definitionally equal source and target functors in the
comparison definitions themselves; see `E4-compact-derived-comparison-signatures.md`.
No proof or module is split and no limit is increased. The proper algebraic-closure comparison stays
unchanged with its original `sorry`. All added helpers are private and proved; the private
basis-data structure is explicitly constructed and contains no postponed data. Opens,
attributes and elaborator options are local to sections or namespaces. No private helper occurs
in a public signature or public non-proof definition body; proof-only imports are not exported.
The second reading removed two redundant proof imports and corrected three private `omit`
clauses to retain assumptions required by the current compiled dependencies. The current
second reader also removes the duplicate private `reflectsDerived` declaration and performs
the conservative exact-functor homology test directly at its sole use. The existing upstream
instance cannot be imported here because its old coefficient notation clashes with the
finite-coefficient notation already loaded; this is documented in the report. No additional
proof import, public declaration, or hole is introduced.

## Users

Checked the source-only downstream listing and all three declaration-name usage listings.
Only the item mentions these exact instance names; downstream users infer the instances.
Every downstream module is listed below, including those relying only on other declarations.
Holders are from the local claims snapshot; no downstream file is edited.

| module | group holding it | effect |
| --- | --- | --- |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility` | E4 | Three instance proofs completed; propositions and visibility identical. |
| `Sheaf.AlgebraicGeometry.CondensedConstructibleSerre` | B3 | Same public API and instance propositions; no adaptation. |
| `Sheaf.Paper.CondensedCoefficientComparisons` | unclaimed | Same public API and instance propositions; no adaptation. |
| `Sheaf.Paper.CondensedFinitePresentationDescent` | B3 | Same public API and instance propositions; no adaptation. |
| `Sheaf.Paper.CondensedFlatCoefficientCalculus` | A4 | Same public API and instance propositions; no adaptation. |
| `Sheaf.Paper.CondensedQbarBaseChangeCompatibility` | unclaimed | Same public API and instance propositions; no adaptation. |
| `Sheaf.Paper.CondensedQbarComparisons` | unclaimed | Same public API and instance propositions; no adaptation. |
| `Sheaf.Paper.CondensedQbarExchangeEquality` | A3 | Same public API and instance propositions; no adaptation. |
| `Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp` | A2 | Same public API and instance propositions; no adaptation. |
| `TargetsCheck` | unclaimed | Same public API and instance propositions; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport` | unclaimed | Same public API and instance propositions; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper` | unclaimed | Same public API and instance propositions; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` | B2 | Same public API and instance propositions; no adaptation. |

## Status

landed 20261015T184346-L-858739 2026-10-15 (merge of deliver/E4/WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility)
