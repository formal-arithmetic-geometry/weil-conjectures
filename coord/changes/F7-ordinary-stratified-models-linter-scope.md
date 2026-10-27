# WeilConjectures.OrdinaryStratifiedModels.ordinaryPullbackStratifiedModels

## Reason

Filling the theorem's proof activates the unused-variable linter on its existing type.
The parameter `L` has a function type whose index binder `a : A i` is not used in the
constant cochain-complex codomain. Preserve that binder and the whole public type
verbatim, and suppress this linter for this declaration only. No instance, transparency,
mathematical option or exported interface changes. This is the only added option command.

## Old

```lean
theorem ordinaryPullbackStratifiedModels
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y)
    (K : DerivedCategory (integralTowerModules l E Y))
    (s : FiniteLocallyClosedStratification Y)
    (_hs : ∀ i : Fin s.n, Topology.IsConstructible (s.stratum i))
    (A : Fin s.n → Type v) (U : ∀ i : Fin s.n, A i → (s.domain i).ProEt)
    (_hcover : ∀ i : Fin s.n,
      Sieve.generate (Presieve.ofArrows (U i) (fun a ↦ terminal.from (U i a))) ∈
        ProEt.topology (s.domain i) (⊤_ (s.domain i).ProEt))
    (L : ∀ (i : Fin s.n) (a : A i),
      CochainComplex (ModuleCat.{u + 1} (PbcIntegralRing l E)) ℤ)
    (_hfinite : ∀ (i : Fin s.n) (a : A i) (q : ℤ),
      Module.Finite (PbcIntegralRing l E) ((L i a).X q))
    (_hprojective : ∀ (i : Fin s.n) (a : A i) (q : ℤ),
      Module.Projective (PbcIntegralRing l E) ((L i a).X q))
    (_hbounded : ∀ (i : Fin s.n) (a : A i),
      ∃ b c : ℤ, ∀ q : ℤ, q < b ∨ c < q → IsZero ((L i a).X q))
    (e : ∀ (i : Fin s.n) (a : A i),
      (ordinaryIntegralDerivedPull l E (U i a).hom).obj
          ((ordinaryIntegralDerivedPull l E (s.immersion i)).obj K) ≅
        DerivedCategory.Q.obj ((modelComplex l E (U i a).left).obj (L i a))) :
    (∃ sX : FiniteLocallyClosedStratification X,
      ∃ b : Fin sX.n ≃ {i : Fin s.n // Nonempty (pullback f (s.immersion i) : Scheme.{u})},
        (∀ k : Fin sX.n, Topology.IsConstructible (sX.stratum k)) ∧
        (∀ k : Fin sX.n, sX.stratum k = f.base ⁻¹' s.stratum (b k).val) ∧
        ∀ k : Fin sX.n,
          ∃ α : sX.domain k ≅ pullback f (s.immersion (b k).val),
            α.hom ≫ pullback.fst f (s.immersion (b k).val) = sX.immersion k) ∧
      ∀ i : Fin s.n, Nonempty (pullback f (s.immersion i) : Scheme.{u}) →
        (Sieve.generate (Presieve.ofArrows
          (fun a : A i ↦ (proEtaleBaseChange (pullback.snd f (s.immersion i))).obj (U i a))
          (fun a : A i ↦ terminal.from
            ((proEtaleBaseChange (pullback.snd f (s.immersion i))).obj (U i a)))) ∈
          ProEt.topology (pullback f (s.immersion i)) (⊤_ (pullback f (s.immersion i)).ProEt)) ∧
        ∀ a : A i, IsIso (localComparison l E f (s.immersion i) (U i a) K (L i a) (e i a))
```

## New

```lean
set_option linter.unusedVariables false in
theorem ordinaryPullbackStratifiedModels
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y)
    (K : DerivedCategory (integralTowerModules l E Y))
    (s : FiniteLocallyClosedStratification Y)
    (_hs : ∀ i : Fin s.n, Topology.IsConstructible (s.stratum i))
    (A : Fin s.n → Type v) (U : ∀ i : Fin s.n, A i → (s.domain i).ProEt)
    (_hcover : ∀ i : Fin s.n,
      Sieve.generate (Presieve.ofArrows (U i) (fun a ↦ terminal.from (U i a))) ∈
        ProEt.topology (s.domain i) (⊤_ (s.domain i).ProEt))
    (L : ∀ (i : Fin s.n) (a : A i),
      CochainComplex (ModuleCat.{u + 1} (PbcIntegralRing l E)) ℤ)
    (_hfinite : ∀ (i : Fin s.n) (a : A i) (q : ℤ),
      Module.Finite (PbcIntegralRing l E) ((L i a).X q))
    (_hprojective : ∀ (i : Fin s.n) (a : A i) (q : ℤ),
      Module.Projective (PbcIntegralRing l E) ((L i a).X q))
    (_hbounded : ∀ (i : Fin s.n) (a : A i),
      ∃ b c : ℤ, ∀ q : ℤ, q < b ∨ c < q → IsZero ((L i a).X q))
    (e : ∀ (i : Fin s.n) (a : A i),
      (ordinaryIntegralDerivedPull l E (U i a).hom).obj
          ((ordinaryIntegralDerivedPull l E (s.immersion i)).obj K) ≅
        DerivedCategory.Q.obj ((modelComplex l E (U i a).left).obj (L i a))) :
    (∃ sX : FiniteLocallyClosedStratification X,
      ∃ b : Fin sX.n ≃ {i : Fin s.n // Nonempty (pullback f (s.immersion i) : Scheme.{u})},
        (∀ k : Fin sX.n, Topology.IsConstructible (sX.stratum k)) ∧
        (∀ k : Fin sX.n, sX.stratum k = f.base ⁻¹' s.stratum (b k).val) ∧
        ∀ k : Fin sX.n,
          ∃ α : sX.domain k ≅ pullback f (s.immersion (b k).val),
            α.hom ≫ pullback.fst f (s.immersion (b k).val) = sX.immersion k) ∧
      ∀ i : Fin s.n, Nonempty (pullback f (s.immersion i) : Scheme.{u}) →
        (Sieve.generate (Presieve.ofArrows
          (fun a : A i ↦ (proEtaleBaseChange (pullback.snd f (s.immersion i))).obj (U i a))
          (fun a : A i ↦ terminal.from
            ((proEtaleBaseChange (pullback.snd f (s.immersion i))).obj (U i a)))) ∈
          ProEt.topology (pullback f (s.immersion i)) (⊤_ (pullback f (s.immersion i)).ProEt)) ∧
        ∀ a : A i, IsIso (localComparison l E f (s.immersion i) (U i a) K (L i a) (e i a))
```

The actual source retains its original declaration docstring between the scoped option
and the theorem. The theorem type is unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.OrdinaryPullbackStratifiedModels | F7 | Only this declaration's unused-variable diagnostic is suppressed; the original public type and data are identical. |

The read-only downstream query and direct-import search find no current importers or
external declaration users. DAG parents with unfinished proofs retain the same API.
No consumer adaptation or importer compile is needed for this declaration-local linter option.

## Status

landed 20261026T235857-L-1464600 2026-10-26 (merge of deliver/F7/Sheaf.Paper.OrdinaryPullbackStratifiedModels)
