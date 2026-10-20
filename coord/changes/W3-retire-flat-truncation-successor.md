# CochainComplex.exists_flat_truncation_successor

## Reason

Retire the duplicate Sheaf module as listed in coord/retire-items.tsv and authorized
by coord/changes/retire-sheaf-twins-20261020.md. The upstream theorem has exactly the
same conclusion and omits three redundant hypotheses: hcover, hquasi, and hepi.
Its proof already constructs flat covers internally, resolves the bounded cone,
applies relative flat extension, and adds contractible flat disks. No upstream
file, definition, or target statement changes.

## Old

From Sheaf.Algebra.Homology.FlatTruncationSuccessor:

```lean
theorem exists_flat_truncation_successor
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{u}}
    (hcover : ∀ M : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      ∃ (P : SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (p : P ⟶ M),
        SheafOfModules.IsFlat P ∧ Epi p)
    (G : CochainComplex
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (n : ℕ)
    (E : CochainComplex
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (q : E ⟶ G.truncLE (n : ℤ))
    (hbounded : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (E.X i))
    (hflat : ∀ i : ℤ, SheafOfModules.IsFlat (E.X i))
    (hquasi : QuasiIso q) (hepi : ∀ i : ℤ, Epi (q.f i)) :
    ∃ (E' : CochainComplex
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
      (t : E ⟶ E') (q' : E' ⟶ G.truncLE ((n + 1 : ℕ) : ℤ)),
      (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (E'.X i)) ∧
      (∀ i : ℤ, SheafOfModules.IsFlat (E'.X i)) ∧ QuasiIso q' ∧
      (∀ i : ℤ, Epi (q'.f i)) ∧
      t ≫ q' ≫ G.ιTruncLE ((n + 1 : ℕ) : ℤ) = q ≫ G.ιTruncLE (n : ℤ)
```

## New

Withdraw lean/Sheaf/Algebra/Homology/FlatTruncationSuccessor.lean and attach the
existing DAG node to WeilConjectures.Algebra.Homology.FlatTruncationSuccessor.
The original conditional node statement specializes the following existing theorem:

```lean
theorem exists_flat_truncation_successor
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{u}}
    (G : CochainComplex
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (n : ℕ)
    (E : CochainComplex
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (q : E ⟶ G.truncLE (n : ℤ))
    (hbounded : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (E.X i))
    (hflat : ∀ i : ℤ, SheafOfModules.IsFlat (E.X i)) :
    ∃ (E' : CochainComplex
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
      (t : E ⟶ E') (q' : E' ⟶ G.truncLE ((n + 1 : ℕ) : ℤ)),
      (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (E'.X i)) ∧
      (∀ i : ℤ, SheafOfModules.IsFlat (E'.X i)) ∧ QuasiIso q' ∧
      (∀ i : ℤ, Epi (q'.f i)) ∧
      t ≫ q' ≫ G.ιTruncLE ((n + 1 : ℕ) : ℤ) = q ≫ G.ιTruncLE (n : ℤ)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.FlatTruncationSuccessor | W3 | Retire the duplicate. |
| WeilConjectures.Algebra.Homology.FlatTruncationTower | unclaimed | Already imports and applies the upstream theorem; no edit required. |

A full search of lean/ finds no importer of the Sheaf duplicate. The retirement
inventory's former consumer Sheaf.Algebra.Homology.FlatTruncationTower has already
been retired; its node points to the upstream tower. Its proof still uses the
successor node, whose attachment is preserved by this delivery. No quarantined
rework row names the successor or the former tower. The unit realization is
unchanged. All three proof dependencies remain used by the upstream proof.

The sandbox scratch verification states the original signature verbatim under a
fresh test name and proves it by applying the upstream theorem to G, n, E, q,
hbounded, and hflat. This tests the equality, both bounds, flatness, epimorphy, and
quasi-isomorphy without adapting or weakening the original conclusion.

## Status

landed 20261020T154940-L-3175803 2026-10-20 (merge of deliver/W3/Sheaf.Algebra.Homology.FlatTruncationSuccessor)
