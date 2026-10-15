# AlgebraicGeometry.ProEtale.exists_condensedQbar_finiteFree_refinement

## Reason

Reviewer X-c7b77 E1: the matrix-refinement proof uses flat going-down, but the
returned split statement allowed an arbitrary morphism f. Require WeaklyEtale f,
as is available for every member of the parent theorem's presentation cover.
The parent target statement stays identical. The matrix node's statement and
lean.statement receive the same signature correction. H8/E5 is addressed by
replacing the compressed outline with seven complete proof steps in the theorem
docstring and node, with the exactness, coefficient-comparison, and
geometric-evaluation dependencies explicitly recorded.

## Old

```lean
theorem exists_condensedQbar_finiteFree_refinement
    (ℓ : ℕ) [Fact ℓ.Prime]
    (X Y : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (f : Y ⟶ X)
    (P : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
    (hP : Mod.IsFinitelyPresented
      ((upperStar Ab.{u + 1} f).obj (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
      (((upperStar Ab.{u + 1} f).mapMod
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)).obj P)) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage Y, ∀ i : C.I₀,
      ∃ r : ℕ, Nonempty
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) (C.f i ≫ f)).obj P ≅
          Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (C.X i)) r)
```

## New

```lean
theorem exists_condensedQbar_finiteFree_refinement
    (ℓ : ℕ) [Fact ℓ.Prime]
    (X Y : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (f : Y ⟶ X) (hf : WeaklyEtale f)
    (P : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
    (hP : Mod.IsFinitelyPresented
      ((upperStar Ab.{u + 1} f).obj (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
      (((upperStar Ab.{u + 1} f).mapMod
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)).obj P)) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage Y, ∀ i : C.I₀,
      ∃ r : ℕ, Nonempty
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) (C.f i ≫ f)).obj P ≅
          Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (C.X i)) r)
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CondensedQbarLfpLocalTriviality | C2 | Passes 𝒰.forgetQc.map_prop i immediately after 𝒰.f i. Its signature is unchanged. |

The matrix-refinement module is a new, unlanded split in this delivery. The shared
repository has no other user of its declaration. No module held by another group
was edited. The parent theorem's direct importer is
Sheaf.AlgebraicGeometry.CondensedConstructibleSerre; its statement and call to the
parent theorem are unaffected by the extra hypothesis internal to this proof.

The parent's original public imports of Sheaf.Paper.ProfinitePointPullback and
Sheaf.NumberTheory.Padics.FiniteCoefficientFields are restored. With the returned
pruning, the unchanged downstream importer failed at lines 240, 646, and 709 with
`failed to synthesize NatTrans.IsMonoidal e.inv`. Restoring the old public interface
repairs this without adapting any downstream file. The earlier import-pruning
change record is withdrawn from the sandbox. The unchanged downstream module
compiled against the restored sandbox overlay in 42.5 seconds.

## Status

landed 20261015T201714-L-1447338 2026-10-15 (merge of deliver/C2/Sheaf.Paper.CondensedQbarLfpLocalTriviality)
