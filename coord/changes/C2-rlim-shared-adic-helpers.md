# DerivedCategory.adic_quotient_limit and shared quotient-tower helpers

## Reason

The return of delivery 792f0bb85 identifies duplicate proofs of `adic_quotient_limit` and
`adic_step_nilpotent` in RlimPerfectComplete. Their existing declarations in
PseudoCoherentNormalizedAlgebraTower are private, so an import cannot use them. Expose
those proved declarations in place and import that module. Also reuse its existing,
more general `restrictScalarsComp_derived_factors`, removing the local specialization.
Only visibility and documentation change in the unclaimed dependency; no hypothesis,
universe, conclusion, proof body, definition or existing public declaration changes.

## Old

```lean
private theorem adic_quotient_limit {C : Type u} [CommRing C]
    (J : Ideal C) [IsAdicComplete J C]
    (x : ∀ n : ℕ, C ⧸ J ^ (n + 1))
    (hx : ∀ n : ℕ, Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (I := J) (Nat.le_succ (n + 1))) (x (n + 1)) = x n) :
    ∃! a : C, ∀ n, Ideal.Quotient.mk (J ^ (n + 1)) a = x n

private theorem adic_step_nilpotent {C : Type u} [CommRing C] (J : Ideal C) (n : ℕ) :
    IsNilpotent (RingHom.ker (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (I := J) (Nat.le_succ (n + 1)))))

private theorem restrictScalarsComp_derived_factors
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} S)]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} T)]
    (f : R →+* S) (g : S →+* T) (gf : R →+* T) (hgf : gf = g.comp f)
    (P : CochainComplex (ModuleCat.{max u v} T) ℤ) :
    ((Functor.mapDerivedCategoryNatIso (ModuleCat.restrictScalarsComp' f g gf hgf)) ≪≫
      Functor.mapDerivedCategoryCompIso (ModuleCat.restrictScalars g)
        (ModuleCat.restrictScalars f)).hom.app (Q.obj P) ≫
      (ModuleCat.restrictScalars f).mapDerivedCategory.map
        ((ModuleCat.restrictScalars g).mapDerivedCategoryFactors.hom.app P) ≫
      (ModuleCat.restrictScalars f).mapDerivedCategoryFactors.hom.app
        (((ModuleCat.restrictScalars g).mapHomologicalComplex (.up ℤ)).obj P) =
    (ModuleCat.restrictScalars gf).mapDerivedCategoryFactors.hom.app P ≫
      Q.map ((NatIso.mapHomologicalComplex
        (ModuleCat.restrictScalarsComp' f g gf hgf) (.up ℤ)).hom.app P)
```

## New

```lean
theorem adic_quotient_limit {C : Type u} [CommRing C]
    (J : Ideal C) [IsAdicComplete J C]
    (x : ∀ n : ℕ, C ⧸ J ^ (n + 1))
    (hx : ∀ n : ℕ, Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (I := J) (Nat.le_succ (n + 1))) (x (n + 1)) = x n) :
    ∃! a : C, ∀ n, Ideal.Quotient.mk (J ^ (n + 1)) a = x n

theorem adic_step_nilpotent {C : Type u} [CommRing C] (J : Ideal C) (n : ℕ) :
    IsNilpotent (RingHom.ker (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (I := J) (Nat.le_succ (n + 1)))))

theorem restrictScalarsComp_derived_factors
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} S)]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} T)]
    (f : R →+* S) (g : S →+* T) (gf : R →+* T) (hgf : gf = g.comp f)
    (P : CochainComplex (ModuleCat.{max u v} T) ℤ) :
    ((Functor.mapDerivedCategoryNatIso (ModuleCat.restrictScalarsComp' f g gf hgf)) ≪≫
      Functor.mapDerivedCategoryCompIso (ModuleCat.restrictScalars g)
        (ModuleCat.restrictScalars f)).hom.app (Q.obj P) ≫
      (ModuleCat.restrictScalars f).mapDerivedCategory.map
        ((ModuleCat.restrictScalars g).mapDerivedCategoryFactors.hom.app P) ≫
      (ModuleCat.restrictScalars f).mapDerivedCategoryFactors.hom.app
        (((ModuleCat.restrictScalars g).mapHomologicalComplex (.up ℤ)).obj P) =
    (ModuleCat.restrictScalars gf).mapDerivedCategoryFactors.hom.app P ≫
      Q.map ((NatIso.mapHomologicalComplex
        (ModuleCat.restrictScalarsComp' f g gf hgf) (.up ℤ)).hom.app P)
```

The surrounding `@[expose] public section` makes these existing theorems public. Added
source and proof docstrings, and listed the helpers in the existing node's Lean attachment.
RlimPerfectComplete imports their module without `public` and uses all three declarations.
It no longer declares any of these helpers itself.

## Users

`python3 tools/downstream.py Sheaf.RingTheory.PseudoCoherentNormalizedAlgebraTower`
and the same command for `Sheaf.RingTheory.RlimPerfectComplete` each report zero downstream
modules in the current shared tree on 2026-10-18. The former has no claim file and is
unclaimed. Its existing main theorem still uses the same helper types and proofs.
The only new consumer is the assigned C2 module. No target or consumer signature changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.PseudoCoherentNormalizedAlgebraTower | unclaimed | Expose three proved helpers. |
| Sheaf.RingTheory.RlimPerfectComplete | C2 | Import and use the helpers; remove duplicates. |

## Status

landed 20261018T101336-L-3972165 2026-10-18 (merge of deliver/C2/Sheaf.RingTheory.RlimPerfectComplete)
