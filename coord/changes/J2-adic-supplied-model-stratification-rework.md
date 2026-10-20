# AlgebraicGeometry.Scheme.pbc_adic_flat_iff_supplied_model_flat

## Reason

Restore the assigned quarantined module recorded in coord/rework.tsv (quarantined at
5f7b33eac on 2026-10-20). Compiling the preserved source against the current library
reports an unknown identifier `LocallyClosedStratification` at line 56. It also reports
a subsequent elaboration heartbeat error at line 69. Replacing the obsolete type name
with `Scheme.Stratification` resolves both errors, without increasing any resource limit.
The complete restored file compiles cleanly through lcompile.py in 4.4 seconds.

The adopted WeilConjectures.AlgebraicGeometry.LocallyClosedStratification module now
publicly imports WeilConjectures.ConstructibleSheaf.Defs, which provides
AlgebraicGeometry.Scheme.Stratification. It records the finite locally closed partition,
the stratum schemes, their immersions and images, and constructibility of the strata.
On the Noetherian scheme T already assumed here, every locally closed subset is
constructible. The existing Stratification.ofNoetherianSpace constructor explicitly
supplies this clause from locally closed strata, preserving the domains and immersions.
Thus the quantifier still ranges over the same mathematical supplied-model systems;
empty schemes, empty strata, zero complexes and all bounds remain allowed as before.

No target declaration or definition changes. All public imports, the entire proof
plan and the one existing named theorem hole are preserved. The node's lean.statement
is updated to agree with the restored source; its attachment and all dependencies stay.
This is a restoration/interface repair, not a completed proof of the criterion.

## Old

```lean
theorem pbc_adic_flat_iff_supplied_model_flat
    (T : Scheme.{u}) [IsNoetherian T]
    (_hdim : ∃ n : ℕ, topologicalKrullDim T ≤ n)
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (_hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t))
    (K : PbcBoundedConstructibleComplete T (pbcPadicCoefficientDatum l E)) :
    (∀ q : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology T)
        (R := pbcAdicCompletion T (pbcPadicCoefficientDatum l E))
        ((DerivedCategory.homologyFunctor _ q).obj K.obj)) ↔
    ∀ (d₀ d₁ : ℤ), d₀ ≤ d₁ → ∀ (S : LocallyClosedStratification T)
        (V : ∀ α : Fin S.n, Sieve (⊤_ (S.domain α).ProEt)),
        (∀ α : Fin S.n, V α ∈ ProEt.topology (S.domain α) (⊤_ (S.domain α).ProEt)) →
        ∀ L : ∀ (α : Fin S.n) (U : (S.domain α).ProEt)
            (f : U ⟶ ⊤_ (S.domain α).ProEt),
            V α f → AdicTowerLocalModel (pbcPadicCoefficientDatum l E) (U.hom ≫ S.immersion α)
              (pbcReductionAdicTower T (pbcPadicCoefficientDatum l E) K.obj) d₀ d₁,
          ∀ (α : Fin S.n) (U : (S.domain α).ProEt)
            (f : U ⟶ ⊤_ (S.domain α).ProEt) (hf : V α f) (q : ℤ),
            SheafOfModules.IsFlatOnSite (J := ProEt.topology U.left)
              (R := (adicTowerInverseImage (U.hom ≫ S.immersion α)).obj
                (pbcAdicCompletion T (pbcPadicCoefficientDatum l E)))
              ((DerivedCategory.homologyFunctor _ q).obj
                (DerivedCategory.Q.obj (L α U f hf).complex))
```

## New

```lean
theorem pbc_adic_flat_iff_supplied_model_flat
    (T : Scheme.{u}) [IsNoetherian T]
    (_hdim : ∃ n : ℕ, topologicalKrullDim T ≤ n)
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (_hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t))
    (K : PbcBoundedConstructibleComplete T (pbcPadicCoefficientDatum l E)) :
    (∀ q : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology T)
        (R := pbcAdicCompletion T (pbcPadicCoefficientDatum l E))
        ((DerivedCategory.homologyFunctor _ q).obj K.obj)) ↔
    ∀ (d₀ d₁ : ℤ), d₀ ≤ d₁ → ∀ (S : Stratification T)
        (V : ∀ α : Fin S.n, Sieve (⊤_ (S.domain α).ProEt)),
        (∀ α : Fin S.n, V α ∈ ProEt.topology (S.domain α) (⊤_ (S.domain α).ProEt)) →
        ∀ L : ∀ (α : Fin S.n) (U : (S.domain α).ProEt)
            (f : U ⟶ ⊤_ (S.domain α).ProEt),
            V α f → AdicTowerLocalModel (pbcPadicCoefficientDatum l E) (U.hom ≫ S.immersion α)
              (pbcReductionAdicTower T (pbcPadicCoefficientDatum l E) K.obj) d₀ d₁,
          ∀ (α : Fin S.n) (U : (S.domain α).ProEt)
            (f : U ⟶ ⊤_ (S.domain α).ProEt) (hf : V α f) (q : ℤ),
            SheafOfModules.IsFlatOnSite (J := ProEt.topology U.left)
              (R := (adicTowerInverseImage (U.hom ≫ S.immersion α)).obj
                (pbcAdicCompletion T (pbcPadicCoefficientDatum l E)))
              ((DerivedCategory.homologyFunctor _ q).obj
                (DerivedCategory.Q.obj (L α U f hf).complex))
```

## Users

The source-only downstream tool reports `unknown module(s)` because the item is
quarantined and absent from the live library. Searching lean/ and quarantine/ for
its module and declaration names finds no live direct consumer and one archived
consumer:

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.AdicTorFlatCohomology (quarantined) | no live adaptation | Its final exact application uses the same declaration name and arguments. Its own PbcSuppliedModelCohomologyFlat still contains the obsolete stratification name and already fails against the current source before this repair. Its separate restoration must update that occurrence consistently. |

The archived consumer is not restored or withdrawn by this packet. Its pre-existing
failure is not forced by this repair. All parent DAG references and the quarantined
archive remain intact. No source-library module or another group's module is edited.
The unit sk-rem-rest has no realized statement or proof step bypassed by this repair.

## Status

landed 20261020T230752-L-610588 2026-10-20 (merge of deliver/J2/Sheaf.Paper.AdicSuppliedModelFlatCriterion)
