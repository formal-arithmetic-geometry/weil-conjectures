# SheafOfModules.isFlatOnSite_of_local_equationalCriterion

## Reason

The existing equivalence requires the module universe to contain the coefficient universe.
The assigned constant-field cohomology statement has independent universes and cannot
instantiate that equivalence. Only the forward local-relation argument needs free modules
on the coefficient ring; the implication to flatness works in any module universe.
Expose that implication using the existing proof, generalizing only its private helpers.
The adapted module is unclaimed. No existing public signature or visibility changes.
No target statement or definition changes.

## Old

The only public theorem in this module was, verbatim:

```lean
theorem isFlatOnSite_iff_local_equationalCriterion
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max r m}] [HasWeakSheafify J AddCommGrpCat.{max r m}]
    (R : Sheaf J CommRingCat.{r})
    (M : ringedSiteModules.{max r m}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :
    IsFlatOnSite M ↔
      ∀ (U : C) (n : ℕ) (a : Fin n → R.obj.obj (op U))
        (s : Fin n → M.val.obj (op U)),
        (∑ p : Fin n, a p • s p) = 0 →
        ∃ S : Sieve U, S ∈ J U ∧
          ∀ (V : C) (f : V ⟶ U), S f →
            ∃ (l : ℕ) (b : Fin n → Fin l → R.obj.obj (op V))
              (t : Fin l → M.val.obj (op V)),
              (∀ p : Fin n, M.val.map f.op (s p) = ∑ q : Fin l, b p q • t q) ∧
              (∀ q : Fin l, (∑ p : Fin n, R.obj.map f.op (a p) * b p q) = 0)
```

The private RowCriterion/matrix/tensor-injectivity section used
`SheafOfModules.{max r m}` and `PresheafOfModules.{max r m}`, with the abelian
sheafification instances at `max r m` as well.

## New

The old public theorem is retained verbatim. Its private helpers are generalized from
`max r m` to the independent universe `m`; their proofs are unchanged.
The following proved API theorem is added:

```lean
theorem isFlatOnSite_of_local_equationalCriterion
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}]
    (R : Sheaf J CommRingCat.{r})
    (M : ringedSiteModules.{m}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
    (hM : ∀ (U : C) (n : ℕ) (a : Fin n → R.obj.obj (op U))
        (s : Fin n → M.val.obj (op U)),
        (∑ p : Fin n, a p • s p) = 0 →
        ∃ S : Sieve U, S ∈ J U ∧
          ∀ (V : C) (f : V ⟶ U), S f →
            ∃ (l : ℕ) (b : Fin n → Fin l → R.obj.obj (op V))
              (t : Fin l → M.val.obj (op V)),
              (∀ p : Fin n, M.val.map f.op (s p) = ∑ q : Fin l, b p q • t q) ∧
              (∀ q : Fin l, (∑ p : Fin n, R.obj.map f.op (a p) * b p q) = 0)) :
    IsFlatOnSite M
```

Its proof reuses tensorSheaf_mono and finite-colimit preservation. The existing theorem
still elaborates using the specialization m := max r m. All four delivered modules compile.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses | unclaimed | Generalize private helpers; add proved implication; original public theorem unchanged. |
| Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses | unclaimed | Uses the identical original equivalence; no adaptation. |
| Sheaf.Paper.InverseImageModuleFlat | unclaimed | Uses the identical original equivalence; no adaptation. |
| Sheaf.Algebra.Category.ModuleCat.Sheaf.ConstantFieldFlat | U4 (new) | Uses the new implication at independent universes. |

The old consumers do not refer to any changed private helper. Their mathematical statements
and elaborated public inputs therefore remain identical. Both unchanged consumer modules
were compiled with lcompile.py against this delivery: FlatAlgebraicInverseImageOfUniverses
in 12.6 seconds and InverseImageModuleFlat in 5.2 seconds, with no warnings. The new theorem is an additional
proved implication, not a replacement or a weakened statement.

## Status

landed 20261019T034309-L-418700 2026-10-19 (merge of deliver/U4/Sheaf.Algebra.Category.ModuleCat.Sheaf.ConstantFieldTensorCohomology)
