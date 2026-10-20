# Algebra.localizedModuleColimitComparison

## Reason

Retire the unused Sheaf duplicate in favor of the adopted, proved
`Algebra.exists_colimit_addEquiv_localizedModule`. The signatures agree verbatim after
renaming the theorem. No declaration in the adopted source tree is removed or changed.
The DAG attachment still names the obsolete Sheaf copy; it is redirected to the upstream proof.

## Old

```lean
theorem localizedModuleColimitComparison
    {Λ : Type u} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    {T : Type u} [CommRing T] {M : Type v} [AddCommGroup M] [Module T M]
    (B : Λ ⥤ CommRingCat.{u}) (D : Λ ⥤ AddCommGrpCat.{v})
    (N : Λ ⥤ AddCommGrpCat.{max u v})
    (κ : B ⟶ (Functor.const Λ).obj (CommRingCat.of T))
    (ν : D ⟶ (Functor.const Λ).obj (AddCommGrpCat.of M))
    [∀ i, Module (B.obj i) (D.obj i)]
    (hB : Nonempty (IsColimit (Cocone.mk (CommRingCat.of T) κ)))
    (hD : Nonempty (IsColimit (Cocone.mk (AddCommGrpCat.of M) ν)))
    (hs : ∀ (i j : Λ) (f : i ⟶ j) (b : B.obj i) (x : D.obj i),
      (D.map f).hom (b • x) = (B.map f).hom b • (D.map f).hom x)
    (hν : ∀ i (b : B.obj i) (x : D.obj i),
      (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) (b • x) =
        (@CommRingCat.Hom.hom _ (CommRingCat.of T) (κ.app i)) b •
          (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) x)
    (q : PrimeSpectrum T)
    (eᵢ : ∀ i, N.obj i ≃+
      LocalizedModule (q.asIdeal.comap (κ.app i).hom).primeCompl (D.obj i))
    (hm : ∀ (i j : Λ) (f : i ⟶ j) (x : D.obj i)
      (s : (q.asIdeal.comap (κ.app i).hom).primeCompl),
      ∃ t : (q.asIdeal.comap (κ.app j).hom).primeCompl,
        (t : B.obj j) = (B.map f).hom s ∧
        eᵢ j ((N.map f).hom ((eᵢ i).symm (LocalizedModule.mk x s))) =
          LocalizedModule.mk ((D.map f).hom x) t)
    (g : ∀ i, N.obj i →+ LocalizedModule q.asIdeal.primeCompl M)
    (hg : ∀ i (x : D.obj i) (s : (q.asIdeal.comap (κ.app i).hom).primeCompl),
      g i ((eᵢ i).symm (LocalizedModule.mk x s)) =
        LocalizedModule.mk
          ((@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) x)
          ⟨(@CommRingCat.Hom.hom _ (CommRingCat.of T) (κ.app i)) s, s.property⟩) :
    ∃ e : (colimit N : AddCommGrpCat.{max u v}) ≃+
      LocalizedModule q.asIdeal.primeCompl M,
      ∀ i (z : N.obj i), e ((colimit.ι N i).hom z) = g i z
```

Declared in `Sheaf.RingTheory.LocalizedModuleColimitComparison`.

## New

```lean
theorem exists_colimit_addEquiv_localizedModule
    {Λ : Type u} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    {T : Type u} [CommRing T] {M : Type v} [AddCommGroup M] [Module T M]
    (B : Λ ⥤ CommRingCat.{u}) (D : Λ ⥤ AddCommGrpCat.{v})
    (N : Λ ⥤ AddCommGrpCat.{max u v})
    (κ : B ⟶ (Functor.const Λ).obj (CommRingCat.of T))
    (ν : D ⟶ (Functor.const Λ).obj (AddCommGrpCat.of M))
    [∀ i, Module (B.obj i) (D.obj i)]
    (hB : Nonempty (IsColimit (Cocone.mk (CommRingCat.of T) κ)))
    (hD : Nonempty (IsColimit (Cocone.mk (AddCommGrpCat.of M) ν)))
    (hs : ∀ (i j : Λ) (f : i ⟶ j) (b : B.obj i) (x : D.obj i),
      (D.map f).hom (b • x) = (B.map f).hom b • (D.map f).hom x)
    (hν : ∀ i (b : B.obj i) (x : D.obj i),
      (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) (b • x) =
        (@CommRingCat.Hom.hom _ (CommRingCat.of T) (κ.app i)) b •
          (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) x)
    (q : PrimeSpectrum T)
    (eᵢ : ∀ i, N.obj i ≃+
      LocalizedModule (q.asIdeal.comap (κ.app i).hom).primeCompl (D.obj i))
    (hm : ∀ (i j : Λ) (f : i ⟶ j) (x : D.obj i)
      (s : (q.asIdeal.comap (κ.app i).hom).primeCompl),
      ∃ t : (q.asIdeal.comap (κ.app j).hom).primeCompl,
        (t : B.obj j) = (B.map f).hom s ∧
        eᵢ j ((N.map f).hom ((eᵢ i).symm (LocalizedModule.mk x s))) =
          LocalizedModule.mk ((D.map f).hom x) t)
    (g : ∀ i, N.obj i →+ LocalizedModule q.asIdeal.primeCompl M)
    (hg : ∀ i (x : D.obj i) (s : (q.asIdeal.comap (κ.app i).hom).primeCompl),
      g i ((eᵢ i).symm (LocalizedModule.mk x s)) =
        LocalizedModule.mk
          ((@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) x)
          ⟨(@CommRingCat.Hom.hom _ (CommRingCat.of T) (κ.app i)) s, s.property⟩) :
    ∃ e : (colimit N : AddCommGrpCat.{max u v}) ≃+
      LocalizedModule q.asIdeal.primeCompl M,
      ∀ i (z : N.obj i), e ((colimit.ι N i).hom z) = g i z
```

Already declared and proved in `WeilConjectures.RingTheory.LocalizedModuleColimitComparison`.
Withdraw `lean/Sheaf/RingTheory/LocalizedModuleColimitComparison.lean` as an empty module,
using `deleted.txt`. Reattach `lem-pc-localized-module-colimit-comparison` to the existing
upstream declaration. No mathematical statement or definition changes.

## Users

`tools/downstream.py Sheaf.RingTheory.LocalizedModuleColimitComparison
--uses Algebra.localizedModuleColimitComparison` reports zero downstream modules and only
the declaration's own file as a textual name occurrence. A whole-library search likewise
finds no imports or uses of the withdrawn declaration.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.LocalizedModuleColimitComparison | Q2 | Withdraw unused duplicate. |

The historical consumers `WeilConjectures.RingTheory.CanonicalLocalizedApproximationLimit`
and `WeilConjectures.RingTheory.LocalizedApproximationColimits` already import the upstream
module and apply `exists_colimit_addEquiv_localizedModule`; neither needs adaptation.
The unit's route and all target statements keep the same meaning.

## Status

landed 20261020T144300-L-2261254 2026-10-20 (merge of deliver/Q2/Sheaf.RingTheory.LocalizedModuleColimitComparison)
