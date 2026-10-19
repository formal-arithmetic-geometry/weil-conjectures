# SheafOfModules.isFlat_iff_local_equationalCriterion

## Reason

Restore the current DAG interface, replacing an obsolete private proof chain
and commented-out theorem left after the upstream sync. The recorded theorem
uses the general sheaf tensor and the actual covering axioms. Its proof follows
from the existing independent-universe covering-sieve criterion. The new private
helper is fully proved. No target statement or definition is changed.

## Old

No active public theorem of this name exists in the baseline source. The
commented theorem had the following signature:

```lean
theorem isFlat_iff_local_equationalCriterion
    {C : Type u} [SmallCategory C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (A : Sheaf J.toGrothendieck CommRingCat.{u})
    (M : ringedSiteModules.{u}
      ((sheafCompose J.toGrothendieck (forget₂ CommRingCat.{u} RingCat.{u})).obj A)) :
    IsFlat M ↔
      ∀ (U : C) (n : ℕ) (a : Fin n → A.obj.obj (op U))
        (s : Fin n → M.val.obj (op U)),
        (∑ p : Fin n, a p • s p) = 0 →
        ∃ S : Presieve U, S ∈ J U ∧
          ∀ (V : C) (f : V ⟶ U), S f →
            ∃ (l : ℕ) (b : Fin n → Fin l → A.obj.obj (op V))
              (t : Fin l → M.val.obj (op V)),
              (∀ p : Fin n, M.val.map f.op (s p) = ∑ q : Fin l, b p q • t q) ∧
              (∀ q : Fin l, (∑ p : Fin n, A.obj.map f.op (a p) * b p q) = 0)
```

The active private helper `finite_tensor_relation` contained the sole hole;
its entire private argument is no longer needed and is pruned.

## New

```lean
theorem isFlat_iff_local_equationalCriterion
    {C : Type u} [SmallCategory C]
    (J : Precoverage C) (_hJ : J.IsSiteForCoverings)
    (A : Sheaf J.toGrothendieck CommRingCat.{u})
    (M : ringedSiteModules.{u}
      ((sheafCompose J.toGrothendieck (forget₂ CommRingCat.{u} RingCat.{u})).obj A)) :
    IsFlatOnSite (J := J.toGrothendieck) (R := A) M ↔
      ∀ (U : C) (n : ℕ) (a : Fin n → A.obj.obj (op U))
        (s : Fin n → M.val.obj (op U)),
        (∑ p : Fin n, a p • s p) = 0 →
        ∃ S : Presieve U, S ∈ J U ∧
          ∀ (V : C) (f : V ⟶ U), S f →
            ∃ (l : ℕ) (b : Fin n → Fin l → A.obj.obj (op V))
              (t : Fin l → M.val.obj (op V)),
              (∀ p : Fin n, M.val.map f.op (s p) = ∑ q : Fin l, b p q • t q) ∧
              (∀ q : Fin l, (∑ p : Fin n, A.obj.map f.op (a p) * b p q) = 0)
```

This is the existing node's recorded statement, restored unchanged. The new
public statement imports are `SiteCoveringAxioms`, `RingedSiteModules`, and
`FlatOnSite`; the proof-only import is `FlatEquationalCriterionOfUniverses`.
The obsolete `Flat` public import is removed; `Grp.FilteredColimits` is
retained for the small-site sheafification instances.

## Users

`tools/downstream.py --uses` reports 200 transitive importers and zero active
uses of `isFlat_iff_local_equationalCriterion`. The three direct importers are
listed below; each already imports the statement APIs it uses. No declaration
or proof in a consumer is changed, so no forced adaptation is needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterion | M5 | Restore its recorded theorem; remove unused private helpers and imports. |
| Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatFinitePresentationRetract | not adapted | No active use of the theorem; original source checked unchanged. |
| Sheaf.Algebra.Category.ModuleCat.Sheaf.SmallFlatSubextension | not adapted | No active use of the theorem; original source checked unchanged. |
| Sheaf.Algebra.Category.ModuleCat.Sheaf.SmallFlatSubsheaf | not adapted | No active use of the theorem; original source checked unchanged. |

## Status

landed 20261019T112456-L-3943727 2026-10-19 (merge of deliver/M5/Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterion)
