# AlgebraicGeometry.ProEtale.continuousField_matrix_sheaf_normalForm

## Reason

Complete the matrix-to-module and pullback argument within the item module. The delivery
adds private helper declarations, namespace-scoped variables and opens, local instance
attributes, and local elaboration options. The preflight conservatively treats new
`variable`, `open` and `attribute` commands as an interface change, requiring this record.

There is no change to any existing public statement, definition, visibility or public
import. The three instance proofs are ordinary private lemmas registered with
`attribute [local instance]`; this delivery adds no global instance. The new imports are proof-only:
`WeilConjectures.CategoryTheory.Sites.MonObj` and
`import all Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization`. The latter
exposes the existing private `CategoryTheory.pushforwardRingMonObj` only inside this
module; that module was already in the public import closure. The repair removes the
duplicate private `cfmPushforwardRingMonObj` and its namespace-scoped setup, replacing
its sole use with the existing theorem. The previous second reader removed
the redundant proof-only import of `LowerShriek.Open.Defs`. No target definition changes
and no target statement review is reopened.

## Old

The public signature, verbatim (the old proof was `by sorry`):

```lean
theorem continuousField_matrix_sheaf_normalForm
    (E : Type u) [NormedField E] {V W : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1}) [MonObj R]
    (e : R ⟶ (sheafCompose (Scheme.ProEt.topology V)
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
        (continuousCoefficientRingSheaf V E)) [IsIso e] [IsMonHom e]
    {m n : ℕ} (f : Mod.finiteFree R m ⟶ Mod.finiteFree R n)
    (g : W ⟶ V) [IsOpenImmersion g]
    (r : ℕ) (ρ : Fin r → Fin n) (γ : Fin r → Fin m)
    (hρ : Function.Injective ρ) (hγ : Function.Injective γ)
    (P : Matrix (Fin n) (Fin n) (C(W, E)))
    (Q : Matrix (Fin m) (Fin m) (C(W, E)))
    (hP : IsUnit P.det) (hQ : IsUnit Q.det)
    (h : (continuousFieldPresentationMatrix E V e f).map
        (ContinuousMap.compRightAlgHom ℤ E ⟨g.base.hom, g.continuous⟩) =
      P * ((Matrix.fromBlocks 1 0 0 0 :
        Matrix (Fin r ⊕ {i // i ∉ Set.range ρ})
          (Fin r ⊕ {j // j ∉ Set.range γ}) _).reindex
            (sumComplEquiv ρ hρ).symm (sumComplEquiv γ hγ).symm) * Q) :
    ∃ (s t : ℕ)
      (a : ((upperStar AddCommGrpCat.{u + 1} g).mapMod R).obj
          (Mod.finiteFree R m) ≅
        Mod.finiteFree ((upperStar AddCommGrpCat.{u + 1} g).obj R) r ⊞
          Mod.finiteFree ((upperStar AddCommGrpCat.{u + 1} g).obj R) s)
      (b : ((upperStar AddCommGrpCat.{u + 1} g).mapMod R).obj
          (Mod.finiteFree R n) ≅
        Mod.finiteFree ((upperStar AddCommGrpCat.{u + 1} g).obj R) r ⊞
          Mod.finiteFree ((upperStar AddCommGrpCat.{u + 1} g).obj R) t),
      ((upperStar AddCommGrpCat.{u + 1} g).mapMod R).map f =
        a.hom ≫ biprod.map (𝟙 _) 0 ≫ b.inv
```

## New

The same public signature, verbatim; its proof is now complete:

```lean
theorem continuousField_matrix_sheaf_normalForm
    (E : Type u) [NormedField E] {V W : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1}) [MonObj R]
    (e : R ⟶ (sheafCompose (Scheme.ProEt.topology V)
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
        (continuousCoefficientRingSheaf V E)) [IsIso e] [IsMonHom e]
    {m n : ℕ} (f : Mod.finiteFree R m ⟶ Mod.finiteFree R n)
    (g : W ⟶ V) [IsOpenImmersion g]
    (r : ℕ) (ρ : Fin r → Fin n) (γ : Fin r → Fin m)
    (hρ : Function.Injective ρ) (hγ : Function.Injective γ)
    (P : Matrix (Fin n) (Fin n) (C(W, E)))
    (Q : Matrix (Fin m) (Fin m) (C(W, E)))
    (hP : IsUnit P.det) (hQ : IsUnit Q.det)
    (h : (continuousFieldPresentationMatrix E V e f).map
        (ContinuousMap.compRightAlgHom ℤ E ⟨g.base.hom, g.continuous⟩) =
      P * ((Matrix.fromBlocks 1 0 0 0 :
        Matrix (Fin r ⊕ {i // i ∉ Set.range ρ})
          (Fin r ⊕ {j // j ∉ Set.range γ}) _).reindex
            (sumComplEquiv ρ hρ).symm (sumComplEquiv γ hγ).symm) * Q) :
    ∃ (s t : ℕ)
      (a : ((upperStar AddCommGrpCat.{u + 1} g).mapMod R).obj
          (Mod.finiteFree R m) ≅
        Mod.finiteFree ((upperStar AddCommGrpCat.{u + 1} g).obj R) r ⊞
          Mod.finiteFree ((upperStar AddCommGrpCat.{u + 1} g).obj R) s)
      (b : ((upperStar AddCommGrpCat.{u + 1} g).mapMod R).obj
          (Mod.finiteFree R n) ≅
        Mod.finiteFree ((upperStar AddCommGrpCat.{u + 1} g).obj R) r ⊞
          Mod.finiteFree ((upperStar AddCommGrpCat.{u + 1} g).obj R) t),
      ((upperStar AddCommGrpCat.{u + 1} g).mapMod R).map f =
        a.hom ≫ biprod.map (𝟙 _) 0 ≫ b.inv
```

The local helper registrations are:

```lean
attribute [local instance] coeffPullbackIso_mon
attribute [local instance] pulledRealization_isIso
attribute [local instance] pulledRealization_isMonHom
```

The additional namespace commands serve only the private proof helpers. Every auxiliary
object is explicitly constructed and every auxiliary lemma is proved. No new statement
with a hole is introduced.

## Users

`tools/downstream.py` reports the following import closure. Its `--uses` search finds
only the item and `ContinuousFieldPresentationNormalForm` mentioning the theorem.
The original signature is unchanged, so every user remains valid without edits.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm | C1 | Own module: private proof helpers and local registrations; public signature unchanged. |
| Sheaf.AlgebraicGeometry.CondensedConstructibleSerre | unclaimed | No adaptation; public signature and imports unchanged. |
| Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality | unclaimed | No adaptation; public signature and imports unchanged. |
| Sheaf.AlgebraicGeometry.ContinuousFieldCokernelLocalFree | unclaimed | No adaptation; public signature and imports unchanged. |
| Sheaf.AlgebraicGeometry.ContinuousFieldPresentationNormalForm | unclaimed | No adaptation; public signature and imports unchanged. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | No adaptation; public signature and imports unchanged. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | No adaptation; public signature and imports unchanged. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | G2 | No adaptation; public signature and imports unchanged. |
| Sheaf.Paper.CondensedLfpHomContinuity | unclaimed | No adaptation; public signature and imports unchanged. |
| Sheaf.Paper.CondensedLocalPieceHomContinuity | unclaimed | No adaptation; public signature and imports unchanged. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | No adaptation; public signature and imports unchanged. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | No adaptation; public signature and imports unchanged. |
| Sheaf.Paper.CondensedQbarExchangeEquality | A3 | No adaptation; public signature and imports unchanged. |
| Sheaf.Paper.CondensedQbarLfpLocalTriviality | unclaimed | No adaptation; public signature and imports unchanged. |
| Sheaf.Paper.CondensedQbarLfpMatrixRefinement | E3 | No adaptation; public signature and imports unchanged. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | No adaptation; public signature and imports unchanged. |
| Sheaf.Paper.CondensedStratumModelAssembly | unclaimed | No adaptation; public signature and imports unchanged. |
| Sheaf.Paper.CondensedStratumModelInductionStep | unclaimed | No adaptation; public signature and imports unchanged. |
| Sheaf.Paper.CondensedStratumModelInductionStepEmpty | unclaimed | No adaptation; public signature and imports unchanged. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonempty | F3 | No adaptation; public signature and imports unchanged. |
| Sheaf.Paper.ConstructibleCokernelsExtensions | unclaimed | No adaptation; public signature and imports unchanged. |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | A4 | No adaptation; public signature and imports unchanged. |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | No adaptation; public signature and imports unchanged. |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | B4 | No adaptation; public signature and imports unchanged. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | No adaptation; public signature and imports unchanged. |
| Sheaf.Paper.IntegralConstructibleKernels | H2 | No adaptation; public signature and imports unchanged. |
| Sheaf.Paper.IntegralConstructibleNakayama | unclaimed | No adaptation; public signature and imports unchanged. |
| Sheaf.Paper.IntegralConstructibleSerre | unclaimed | No adaptation; public signature and imports unchanged. |
| Sheaf.Paper.IntegralReductionConservative | unclaimed | No adaptation; public signature and imports unchanged. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | No adaptation; public signature and imports unchanged. |
| TargetsCheck | unclaimed | No adaptation; public signature and imports unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | No adaptation; public signature and imports unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | No adaptation; public signature and imports unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | No adaptation; public signature and imports unchanged. |

## Status

landed 20261016T023751-L-1280232 2026-10-16 (merge of deliver/C1/Sheaf.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm)
