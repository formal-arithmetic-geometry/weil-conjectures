# Brown structural witnesses and target-side exceptional-adjoint dependency

## Reason

The arbitrary-field `CategoryTheory.brownHypotheses` assertion is disputed and remains
unproved. Its caller `exists_brownExceptionalAdjoints` already assumes source compact
generators and uses the theorem at Y only to obtain local smallness, triangulation,
repleteness and coproducts. The proved, coefficient-independent
`CategoryTheory.brownHypotheses_structural` supplies precisely those conclusions.
There is no need to assume target compactness in this proof.

The item's reverse formal criterion also unnecessarily rebuilt the localizing
intersection's structural witnesses using two private helpers. Reuse the structural
theorem's actual witnesses, then assemble objectwise compactness and the existing
generation theorem directly. This removes 84 lines of redundant private declarations.

## Old

In `Sheaf.Paper.BrownExceptionalAdjoint`:

```lean
import Sheaf.SixFunctorsBasics.BrownHypotheses
```

```lean
  obtain ⟨hsmallY, hY, hrepY, _, _, _, _, _, hsumY, _⟩ :=
    brownHypotheses ℓ p _hp _hpℓ (Y ↘ Spec (.of k)) Λ _hΛ
```

In the item's reverse `brownHypothesesFor_iff` proof:

```lean
    obtain ⟨hsmall, _, _, hid, _⟩ := brownHypotheses_structural Λ X
    let _ := hsmall
    let _ := hid
    let _ := hcop
    exact brownHypothesesFor_of_compact Λ X ⟨hS, hSiso, hret, hess⟩ hc
```

The private `brownHypothesesFor_of_compact` rebuilt the triangulation and repleteness
with `localizingClosure_isLocalizing`, then applied `localizingClosure_generatingFamily`.
Neither removed helper had an external user or its own independent DAG attachment.

## New

In `Sheaf.Paper.BrownExceptionalAdjoint`:

```lean
import Sheaf.SixFunctorsBasics.BrownHypothesesStructural
```

```lean
  obtain ⟨hsmallY, hY, hrepY, _, hsumY, _⟩ := brownHypotheses_structural Λ Y
```

The item uses the structural witnesses directly:

```lean
    obtain ⟨hsmall, htri, hiso, hid, _⟩ := brownHypotheses_structural Λ X
    let _ := hsmall
    let _ := htri
    let _ : (localizingClosure S).IsTriangulated := htri
    let _ : HasCoproducts.{u + 1} (localizingClosure S).FullSubcategory := hcop
    let _ := hid
    let _ := hcop
    refine ⟨hsmall, htri, hiso, hS, hSiso, hret, hess, hid, hcop, ?_⟩
    intro G _ e hL
    refine ⟨fun g ↦ hc _ (e.functor.obj g).property, ?_⟩
    have hsum : HasCoproduct (fun g : G ↦
        (⟨(e.functor.obj g).obj, hL g⟩ : L.FullSubcategory)) := inferInstance
    let _ := hsum
    apply localizingClosure_generatingFamily (E := fun g : G ↦
      (⟨(e.functor.obj g).obj, hL g⟩ : L.FullSubcategory)) S
    intro Y hY
    let B : S.FullSubcategory := ⟨Y, hY⟩
    exact ⟨e.inverse.obj B, ⟨(S.ι.mapIso (e.counitIso.app B)).symm⟩⟩
```

Delete the now-unused private helpers `localizingClosure_isLocalizing` and
`brownHypothesesFor_of_compact`. All public signatures, definition bodies, visibility,
public imports and target statements are unchanged. No source-library module changes.
The structural theorem fixes the canonical inherited shift, exactly as the old proof did.

## Users

The direct-use census (`tools/downstream.py` with `--uses brownHypotheses`) found the
item and three external callers. Only BrownExceptionalAdjoint uses no compactness
conclusion, so only it is changed. No claim for that adapted module is present in
`coord/claims/` in the shared checkout. It is adapted under the unclaimed-module rule;
this is not a forced adaptation to an interface change. Neither removed private helper
occurs in another Lean file. No consumer statement changes or requires adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctorsBasics.BrownHypotheses | M1 (assignment) | Reuse structural witnesses in the proved criterion; remove two redundant private helpers. |
| Sheaf.Paper.BrownExceptionalAdjoint | unclaimed in shared checkout | Replace the disputed target-side Brown call with the proved structural theorem; unchanged signature. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | not adapted | Both original Brown calls need compactness; preserve them and their dependencies. |
| Sheaf.Paper.ExceptionalInverseImageExistence | not adapted | Original Brown call needs compactness; preserve it and its dependencies. |

The consumer's unchanged public imports still reach LocalizingExceptionalAdjoint,
which itself uses the disputed theorem. Therefore this removes a direct proof use,
not the entire BrownHypotheses module from the import closure. The parent node's
statement citation to the source compact-generation assumption stays; only its
proof dependency on target Brown compactness is replaced by the structural theorem.

## Status

landed 20261025T123308-L-1852964 2026-10-25 (merge of deliver/M1/Sheaf.SixFunctorsBasics.BrownHypotheses)
