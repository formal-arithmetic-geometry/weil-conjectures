# SheafOfModules.KFlatConeComparison.total

## Reason

The original uncurry total-map expression produced costly dependent transports in
cone comparisons. `totalBifunctor` uses the simultaneous `mapBifunctorMap` formula;
`uncurry_map_eq` and `total_eq_uncurry` prove equality with the original functor.
The signed transposition and the degree-zero tensor identification are named generic
constructions, with proved component/naturality APIs. A named irreducible local
`moduleMonoidal` caches the original sheaf monoidal structure. The private cone
isomorphisms and public comparison roof are kept irreducible so proof elaboration uses
those APIs instead of repeatedly expanding localization and totalization data.
All existing signatures and mathematical constructions retain their meaning.

## Old

```lean
noncomputable def tensor : Modules R ⥤ Modules R ⥤ Modules R :=
  letI := SheafOfModules.monoidalCategory R
  curriedTensor _
```

```lean
noncomputable def total : CochainComplex (Modules R) ℤ × CochainComplex (Modules R) ℤ ⥤
    CochainComplex (Modules R) ℤ :=
  letI := SheafOfModules.monoidalCategory R
  Functor.uncurry.obj ((curriedTensor (Modules R)).map₂CochainComplex)
```

```lean
noncomputable def ordinaryIso (L M : Modules R) :
    (total R).obj ((single R).obj L, (single R).obj M) ≅
      (single R).obj (((tensor R).obj L).obj M) :=
  letI := SheafOfModules.monoidalCategory R
  CochainComplex.mapBifunctorSingle₁Iso (curriedTensor _) L ((single R).obj M) ≪≫
    (HomologicalComplex.singleMapHomologicalComplex ((curriedTensor _).obj L) (.up ℤ) 0).app M
```

```lean
noncomputable def swap (K L : CochainComplex (Modules R) ℤ) :
    (total R).obj (K, L) ≅ (total R).obj (L, K) := by
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.symmetricCategory R
  let T := curriedTensor (Modules R)
  let A := ((T.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj K).obj L
  let B := ((T.flip.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj K).obj L
  let e : A ≅ B := HomologicalComplex.Hom.isoOfComponents
    (fun p => HomologicalComplex.Hom.isoOfComponents
      (fun q => β_ (K.X p) (L.X q)) (by
        intro q q' _
        exact (BraidedCategory.braiding_naturality_right (K.X p) (L.d q q')).symm))
    (by
      intro p p' _
      ext q : 1
      exact (BraidedCategory.braiding_naturality_left (K.d p p') (L.X q)).symm)
  exact HomologicalComplex₂.total.mapIso e (.up ℤ) ≪≫
    HomologicalComplex.mapBifunctorFlipIso L K T (.up ℤ)
```

```lean
noncomputable def coneMap {A B A' B' : CochainComplex (Modules R) ℤ}
    {f : A ⟶ B} {g : A' ⟶ B'} (a : A ⟶ A') (b : B ⟶ B')
    (h : a ≫ g = f ≫ b) : CochainComplex.mappingCone f ⟶ CochainComplex.mappingCone g :=
  HomologicalComplex.homotopyCofiber.mapArrowHom f g
    (fun j : ℤ => ⟨j - 1, by change j - 1 + 1 = j; omega⟩) (Arrow.homMk a b h)
```

```lean
noncomputable def localizationPair [HasDerivedCategory.{w} (Modules R)] :=
  ((resolving R).ι ⋙ DerivedCategory.Q).prod ((resolving R).ι ⋙ DerivedCategory.Q)
```

```lean
noncomputable def resolvedTensor [HasDerivedCategory.{w} (Modules R)] :=
  ((resolving R).ι.prod (resolving R).ι) ⋙ total R ⋙ DerivedCategory.Q
```

```lean
noncomputable def comparison
    (T : DerivedCategory (Modules R) × DerivedCategory (Modules R) ⥤
      DerivedCategory (Modules R))
    (ρ : resolvedTensor R ≅ localizationPair R ⋙ T) (r : Pair R) :
    T.obj (DerivedCategory.Q.obj ((single R).obj r.L),
      DerivedCategory.Q.obj ((single R).obj r.M)) ⟶
        DerivedCategory.Q.obj ((single R).obj (((tensor R).obj r.L).obj r.M)) :=
  letI := r.q_quasiIso
  letI := r.ε_quasiIso
  (T.mapIso ((asIso (DerivedCategory.Q.map r.q)).prod
    (asIso (DerivedCategory.Q.map r.ε)))).inv ≫
    ρ.inv.app (resolvedPair R r) ≫ DerivedCategory.Q.map ((total R).map (r.q ×ₘ r.ε)) ≫
      DerivedCategory.Q.map (ordinaryIso R r.L r.M).hom
```

## New

```lean
@[reducible] noncomputable def tensor : Modules R ⥤ Modules R ⥤ Modules R :=
  curriedTensor (Modules R)
```

```lean
noncomputable def total : CochainComplex (Modules R) ℤ × CochainComplex (Modules R) ℤ ⥤
    CochainComplex (Modules R) ℤ :=
  totalBifunctor (curriedTensor (Modules R))
```

```lean
noncomputable def ordinaryIso (L M : Modules R) :
    (total R).obj ((single R).obj L, (single R).obj M) ≅
      (single R).obj (((tensor R).obj L).obj M) :=
  totalSingleIso (curriedTensor (Modules R)) L M
```

```lean
noncomputable def swap (K L : CochainComplex (Modules R) ℤ) :
    (total R).obj (K, L) ≅ (total R).obj (L, K) := by
  exact totalSwap K L
```

```lean
noncomputable def coneMap {A B A' B' : CochainComplex (Modules R) ℤ}
    {f : A ⟶ B} {g : A' ⟶ B'} (a : A ⟶ A') (b : B ⟶ B')
    (h : a ≫ g = f ≫ b) : CochainComplex.mappingCone f ⟶ CochainComplex.mappingCone g :=
  CochainComplex.mappingCone.map f g a b h.symm
```

```lean
@[reducible] noncomputable def localizationPair [HasDerivedCategory.{w} (Modules R)] :=
  ((resolving R).ι ⋙ DerivedCategory.Q).prod ((resolving R).ι ⋙ DerivedCategory.Q)
```

```lean
@[reducible] noncomputable def resolvedTensor [HasDerivedCategory.{w} (Modules R)] :=
  ((resolving R).ι.prod (resolving R).ι) ⋙ total R ⋙ DerivedCategory.Q
```

```lean
@[irreducible] noncomputable def comparison
    (T : DerivedCategory (Modules R) × DerivedCategory (Modules R) ⥤
      DerivedCategory (Modules R))
    (ρ : resolvedTensor R ≅ localizationPair R ⋙ T) (r : Pair R) :
    T.obj (DerivedCategory.Q.obj ((single R).obj r.L),
      DerivedCategory.Q.obj ((single R).obj r.M)) ⟶
        DerivedCategory.Q.obj ((single R).obj (((tensor R).obj r.L).obj r.M)) :=
  letI := r.q_quasiIso
  letI := r.ε_quasiIso
  (T.mapIso ((asIso (DerivedCategory.Q.map r.q)).prod
    (asIso (DerivedCategory.Q.map r.ε)))).inv ≫
    ρ.inv.app (resolvedPair R r) ≫ DerivedCategory.Q.map ((total R).map (r.q ×ₘ r.ε)) ≫
      DerivedCategory.Q.map (ordinaryIso R r.L r.M).hom
```

`totalBifunctor`, `totalSwap`, and `totalSingleIso` are public because public
constructions use their data. `totalSwap` and `totalSingleIso` are irreducible.
The new local instance `moduleMonoidal` has exactly the value
`SheafOfModules.monoidalCategory R`; its symmetry and additivity instances are the
original sheaf instances. Unfolding it recovers the tensor used in K-flatness.
`ordinaryIso` is the same composition of `mapBifunctorSingle₁Iso` and
`singleMapHomologicalComplex` through `totalSingleIso`; `swap` is the same signed
braiding through `totalSwap`. `coneMap` now uses `mappingCone.map` directly: both
implementations have components b on Y and a on X[1], with the same commuting-square
proof, so this preserves the canonical cone map. The previous coordinate proof of
the equality was also checked during development. `comparison` keeps its original
augmentation-roof body and gains only the irreducibility attribute. The private
`leftIso` and `topIso` have irreducibility attributes and explicit proved APIs.

The old and new definitions have the unchanged ringed-site parameters in scope.
No target statement is edited. The standard review of definitions used by the targets
applies to these equal constructions and their reducibility changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.KFlatConeComparison | B8 | Updated implementation and proof. |
| Sheaf.Paper.PurityFiniteKummerLevel | T3 | Earlier proof-only importer; no source adaptation. See validation limitation below. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Unrelated bound variable `tensor`; unaffected. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Unrelated local variable `tensor`; unaffected. |
| Sheaf.Paper.PurityDiagonalSectionPasting | G6 | Unrelated namespaced `tensor`; unaffected. |
| Sheaf.Paper.RationalSmoothPurityCanonical | W5 | Unrelated structure field `tensor`; unaffected. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Unrelated tensor on Weil modules; unaffected. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Tactic `swap`; unaffected. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Tactic `swap`; unaffected. |

These rows exhaust the declaration-name hits of `tools/downstream.py` for `tensor`,
`total`, `swap`, `ordinaryIso`, `coneMap`, `comparison`, `localizationPair`, and
`resolvedTensor` on 2026-10-20.
The tool matches final name segments; the seven additional modules do not reference
this module's declarations. The retained earlier direct importer is `PurityFiniteKummerLevel`. Its source is absent
from the current shared checkout. A final recheck of the retained consumer stopped at
its missing published import `Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`;
the changed module itself compiled cleanly in that check (30.7 seconds). The earlier
consumer check passed (11.6 seconds). No consumer source is delivered.

The current `tools/downstream.py Sheaf.Paper.KFlatConeComparison --uses comparison`
scan reports zero downstream modules and only this module as a declaration-name hit.
The table preserves the earlier scan and the completed consumer checks for review.

## Status

landed 20261020T131938-L-1393372 2026-10-20 (merge of deliver/B8/Sheaf.Paper.KFlatConeComparison)
