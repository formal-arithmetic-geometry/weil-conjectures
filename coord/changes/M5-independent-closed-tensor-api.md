# SheafOfModules.nonempty_monoidalClosed_independentCoefficients

## Reason

The assigned bounded flat model theorem needs the existing generic closed-monoidal
flat-model result at independent site universes. The canonical small internal-Hom
construction is already proved but private in KFlatResolutionIndependentCoefficients.
Expose its existence as a proposition. No data is chosen by a new definition and no
existing instance, signature, or visibility changes. The private construction receives
`@[no_expose, irreducible]` in place of `@[instance_reducible]`, so importing its
propositional API does not expose or reduce the adjunction implementation. This
repairs the item's repeated 60-second compile timeouts; the changed set compiled
in 24.8 and 12.4 seconds without profiling or increased limits.

## Old

No public existence theorem. The existing construction body stays verbatim:

```lean
@[instance_reducible]
private noncomputable def monoidalClosed_kfi : MonoidalClosed (SheafOfModules.{r} 𝓡) where
  closed A :=
    { rightAdj := Adjunction.rightAdjointOfEquiv (F := tensorLeft A)
        (G_obj := homObjSmall_kfi A) (tensorHomEquiv_kfi A)
        (fun _ _ _ f g ↦ tensorHomEquiv_whiskerLeft_comp_kfi A f g)
      adj := Adjunction.adjunctionOfEquivRight (F := tensorLeft A)
        (G_obj := homObjSmall_kfi A) (tensorHomEquiv_kfi A)
        (fun _ _ _ f g ↦ tensorHomEquiv_whiskerLeft_comp_kfi A f g) }
```

## New

Add `public import Mathlib.CategoryTheory.Monoidal.Closed.Basic` and the proved theorem
under the existing independent-universe site and sheafification variables:

```lean
theorem nonempty_monoidalClosed_independentCoefficients :
    Nonempty (MonoidalClosed (SheafOfModules.{r} 𝓡)) :=
  ⟨monoidalClosed_kfi⟩
```

Replace `@[instance_reducible]` by `@[no_expose, irreducible]` on the existing
private `monoidalClosed_kfi`. Its type and body, and all other existing declarations, are unchanged.
The public theorem
returns `Nonempty`, and its witness is the real adjunction construction above. Consumers
can use it locally without any global instance change. Zero rings and empty sites use
the same adjunction; no nontriviality or points are assumed.

## Users

The declaration is new, so existing consumers have no references to it. The defining
module is unclaimed. All existing downstream expressions retain the same meaning and
retain the same mathematical signatures under the additive API export. No target statement uses a changed definition,
and no target review is reopened. The required `tools/downstream.py` check found 2740 transitive downstream modules
and zero existing references to the new theorem. The three modules mentioning
`monoidalClosed_kfi` are listed below; its type, body, and name are unchanged, so
no downstream signature or mathematical data changes. Consumer checks found a
pre-existing duplicate `IsFlat` import in `DiagramKFlatReplacements` against both
baseline and overlay. `RingedInternalHomExactRestriction` timed out against the
overlay and also timed out against the published baseline. No consumer is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients | unclaimed | Added proved public existence API and its public type import; concealed the private construction body. |
| Sheaf.Algebra.Homology.RingedSiteTorFlatModel | M5 | Uses the existence theorem locally to apply the existing generic flat-model proof. |
| Sheaf.Algebra.Homology.DiagramKFlatReplacements | unclaimed | Mentions the existing private construction; its type and body are unchanged. |
| Sheaf.Algebra.Homology.RingedInternalHomExactRestriction | Q1 (not adapted) | Mentions the existing private construction; its type and body are unchanged. |

## Status

landed 20261019T231238-L-565380 2026-10-19 (merge of deliver/M5/Sheaf.Algebra.Homology.RingedSiteTorFlatModel)
