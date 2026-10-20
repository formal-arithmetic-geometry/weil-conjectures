# CochainComplex.isKProjective_of_filtered_free

## Reason

Retire the duplicate `Sheaf.Algebra.Homology.FilteredFreeKProjective` in favour of
`WeilConjectures.Algebra.Homology.FilteredFreeKProjective`, as requested by the human's
2026-10-20 retirement instruction and this module's row in `coord/retire-items.tsv`.
The module has zero holes already. Rewriting its existing proofs, as the previous K6
report did, would not carry out that retirement.

The earlier `PROOFDIFF_UNSAFE` classification was due to the Sheaf assembly twin.
Y7 retired that twin on 2026-10-20; the present Sheaf module already privately imports
the upstream assembly and split-extension modules. There are no remaining Lean
importers, including in `quarantine/`. The three DAG attachments still pointed to
this redundant copy, so this delivery preserves them by redirecting them to the
identically stated upstream theorems. No adopted source file is changed.

## Old

The following three declarations are removed only from the Sheaf copy:

```lean
theorem isKProjective_of_filtered_free_stage {A : Type u} [CommRing A]
    (F : ℕ → CochainComplex (ModuleCat.{max u v} A) ℤ)
    (step : ∀ n, F n ⟶ F (n + 1))
    (hzero : IsZero (F 0))
    (hsplit : ∀ (n : ℕ) (k : ℤ),
      ∃ r : (F (n + 1)).X k ⟶ (F n).X k,
        (step n).f k ≫ r = 𝟙 ((F n).X k))
    (hquot : ∀ n, ∃ (I : Type (max u v)) (degree : I → ℤ),
      Nonempty (cokernel (step n) ≅
        ∐ (fun i : I ↦
          (HomologicalComplex.single (ModuleCat.{max u v} A) (.up ℤ) (degree i)).obj
            (ModuleCat.of A (ULift.{v} A))))) :
    ∀ n, (F n).IsKProjective

theorem isKProjective_of_filtered_free_telescope
    {A : Type u} [CommRing A]
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (F : ℕ → CochainComplex (ModuleCat.{max u v} A) ℤ)
    (ι : ∀ n, F n ⟶ P) (step : ∀ n, F n ⟶ F (n + 1))
    (hzero : IsZero (F 0)) (hmono : ∀ n, Mono (ι n))
    (hcompat : ∀ n, step n ≫ ι (n + 1) = ι n)
    (hexhaustive : ∀ (k : ℤ) (x : P.X k),
      ∃ (n : ℕ) (y : (F n).X k), (ι n).f k y = x)
    (hsplit : ∀ (n : ℕ) (k : ℤ),
      ∃ r : (F (n + 1)).X k ⟶ (F n).X k,
        (step n).f k ≫ r = 𝟙 ((F n).X k))
    (hstage : ∀ n, (F n).IsKProjective) :
    P.IsKProjective

theorem isKProjective_of_filtered_free {A : Type u} [CommRing A]
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (F : ℕ → CochainComplex (ModuleCat.{max u v} A) ℤ)
    (ι : ∀ n, F n ⟶ P) (step : ∀ n, F n ⟶ F (n + 1))
    (hzero : IsZero (F 0)) (hmono : ∀ n, Mono (ι n))
    (hcompat : ∀ n, step n ≫ ι (n + 1) = ι n)
    (hexhaustive : ∀ (k : ℤ) (x : P.X k),
      ∃ (n : ℕ) (y : (F n).X k), (ι n).f k y = x)
    (hsplit : ∀ (n : ℕ) (k : ℤ),
      ∃ r : (F (n + 1)).X k ⟶ (F n).X k,
        (step n).f k ≫ r = 𝟙 ((F n).X k))
    (hquot : ∀ n, ∃ (I : Type (max u v)) (degree : I → ℤ),
      Nonempty (cokernel (step n) ≅
        ∐ (fun i : I ↦
          (HomologicalComplex.single (ModuleCat.{max u v} A) (.up ℤ) (degree i)).obj
            (ModuleCat.of A (ULift.{v} A))))) :
    P.IsKProjective
```

## New

Exactly the same three full signatures above remain available from
`WeilConjectures.Algebra.Homology.FilteredFreeKProjective`, with the same declaration
names and universes. The signatures compare byte for byte. The proofs are complete:
finite-stage induction uses the zero-object null homotopy and the split-extension
theorem; telescope assembly applies `filtered_free_telescope_assembly`; the final
result combines these two facts. Their `#print axioms` results are precisely
`[propext, Classical.choice, Quot.sound]`, checked through `lcompile.py`.

Withdraw the Sheaf module via `deleted.txt`; redirect all three node attachments
(`lem-pc-filtered-free-kprojective`, its `-stage` and `-telescope` nodes) to the
upstream module, retaining their statements and dependency lists. Update proof origins
and describe the telescope's current direct conclusion. No target statement or
definition changes, and no target statement review is reopened.

## Users

`tools/downstream.py Sheaf.Algebra.Homology.FilteredFreeKProjective --uses
CochainComplex.isKProjective_of_filtered_free` reports zero downstream modules and
one name-use module (the copy itself). A separate search of `lean/` and `quarantine/`
finds no imports of the withdrawn module.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.FilteredFreeKProjective | J9 | Withdraw redundant copy. |
| WeilConjectures.Algebra.Homology.FilteredFreeKProjective | unclaimed; unchanged | Reuse the identical theorems. |
| WeilConjectures.Algebra.Homology.BaseDerivedExtensionCoherentTriangle | unchanged | Already imports the upstream replacement; node continues to cite the same result. |
| WeilConjectures.Algebra.Homology.BaseDerivedExtensionResolution | unchanged | Already imports the upstream replacement; node continues to cite the same result. |
| Sheaf.RingTheory.MarkedFiniteFreeLiftCompatibility | unchanged | Already imports the upstream replacement; node continues to cite the same result. |

The last three rows are every external DAG parent of the affected nodes. All already
use the replacement theorem, so no parent source or dependency-list adaptation is
needed. The main affected node itself still cites the stage and telescope nodes,
whose attachments are redirected together. The unit's realized lists are empty;
its mathematical route is preserved. No new import environment or twin collision
is introduced, since all consumers already use the upstream module.

## Status

landed 20261020T221227-L-4161255 2026-10-20 (merge of deliver/J9/Sheaf.Algebra.Homology.FilteredFreeKProjective)
