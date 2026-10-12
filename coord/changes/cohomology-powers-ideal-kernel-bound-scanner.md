# AlgebraicGeometry.cohomology_powers_ideal_kernel_bound

## Reason

The dry-run preflight's text scanner classifies this proof edit as a change of commands.
The pre-existing theorem signature contains an unindented `(∀ n : ℕ, c ≤ n →` line.
`leanindex.commands` therefore treats the signature continuation and proof as an `other`
command, which changes when the proof replaces sorry. There is no actual interface change.
This record reports the tool issue to the independent reviewer/maintainer, rather than changing
the scanner or the theorem statement. No new instance, notation, attribute or file-level option
is introduced. Both modules compile with no warnings. The new generic module is proof-only
imported, so it does not change the interface of existing importers.

## Old

```lean
theorem cohomology_powers_ideal_kernel_bound
    (A : Type v) [CommRing A] [IsNoetherianRing A] {X : Scheme.{v}}
    (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f] (J : X.IdealSheafData)
    (hJ : J = (Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F) (q : ℕ)
    (i : ∀ (k n : ℕ), n ≤ k →
      (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι k).2 F ⟶
        Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι n).2 F))
    (hi : ∀ (k n : ℕ) (h : n ≤ k),
      i k n h ≫ Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι n).2 F =
        Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι k).2 F) :
    ∃ c0 : ℕ, ∀ c : ℕ, c0 ≤ c →
(∀ n : ℕ, c ≤ n →
          LinearMap.ker ((ModuleCat.restrictScalars
              ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).map
            ((RingedSpace.moduleCohomology X.toRingedSpace q).map (i n 0 (Nat.zero_le n)))).hom =
          LinearMap.ker ((ModuleCat.restrictScalars
              ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).map
            ((RingedSpace.moduleCohomology X.toRingedSpace q).map
              (i n (n - c) (Nat.sub_le n c)))).hom)
```

Proof: `by sorry`.

## New

```lean
theorem cohomology_powers_ideal_kernel_bound
    (A : Type v) [CommRing A] [IsNoetherianRing A] {X : Scheme.{v}}
    (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f] (J : X.IdealSheafData)
    (hJ : J = (Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F) (q : ℕ)
    (i : ∀ (k n : ℕ), n ≤ k →
      (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι k).2 F ⟶
        Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι n).2 F))
    (hi : ∀ (k n : ℕ) (h : n ≤ k),
      i k n h ≫ Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι n).2 F =
        Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι k).2 F) :
    ∃ c0 : ℕ, ∀ c : ℕ, c0 ≤ c →
(∀ n : ℕ, c ≤ n →
          LinearMap.ker ((ModuleCat.restrictScalars
              ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).map
            ((RingedSpace.moduleCohomology X.toRingedSpace q).map (i n 0 (Nat.zero_le n)))).hom =
          LinearMap.ker ((ModuleCat.restrictScalars
              ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).map
            ((RingedSpace.moduleCohomology X.toRingedSpace q).map
              (i n (n - c) (Nat.sub_le n c)))).hom)
```

The signature and visibility are identical. The proof now uses the finite Rees action,
the fully proved `ReesAlgebra.bounded_generators` theorem, compatibility and kernel antisymmetry.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.CohomologyPowersIdealKernelBound --uses
cohomology_powers_ideal_kernel_bound` finds only the item itself and the application module as
textual uses. None requires adaptation, since no existing interface changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CohomologyPowersIdealKernelBound | F1 | Proof completed; signature identical. |
| Sheaf.AlgebraicGeometry.CohomologyPowersIdealApplication | unclaimed | No change; identical theorem signature and public imports. |

## Status

landed 20261012T173821-L-3294040 2026-10-12 (merge of deliver/F1/Sheaf.AlgebraicGeometry.CohomologyPowersIdealKernelBound)
