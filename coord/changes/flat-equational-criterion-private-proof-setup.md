# SheafOfModules.isFlat_iff_local_equationalCriterion

## Reason

The new proof needs finite tensor calculations, the monoidal namespace, section variables,
and private local monoidal instances. The static interface checker conservatively treats
added `universe`, `open`, `variable`, `omit`, and `set_option` commands as an interface change.
This record documents those commands. They support private, proved helpers; no existing
signature, public import, definition, or global instance is changed. The existing theorem
is proved with exactly its original statement. No dependent file needs adaptation.

## Old

The original setup was `universe u`, `open CategoryTheory Opposite`, and the namespace
`SheafOfModules`. The theorem signature was:

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

## New

The setup adds universe parameters `v w x` for the private algebraic helper, opens
`CategoryTheory.Limits`, `MonoidalCategory`, and `TensorProduct`, and sets
`backward.isDefEq.respectTransparency` to `false` within this module. Named sections
`Algebra`, `Forward`, and `Converse` introduce helper variables. `omit` commands avoid
unneeded instance parameters in private helpers. The monoidal, symmetric, and closed
instances in `Forward` are explicitly private and local. Every new theorem and definition
is private. The theorem's new signature is identical:

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

## Users

The source-only downstream scan completed: 504 transitive downstream modules, but
`--uses SheafOfModules.isFlat_iff_local_equationalCriterion` finds only the declaring
module itself. A source search finds one direct importer, listed below.
No public declaration or public import changes, and local proof setup does not propagate
to importing modules. No adaptation is required.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterion | P2 | Own statement and public imports unchanged. |
| Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback | M2 | Sole direct importer; no signature or instance change visible, so no adaptation. |

## Status

landed 20261016T054837-L-157797 2026-10-16 (merge of deliver/P2/Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterion)
