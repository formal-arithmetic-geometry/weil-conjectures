# AlgebraicGeometry.Scheme.Modules.canonicalCoherentEtaleComparison

## Reason

The original file exceeds the 60-second file limit when Lean repeatedly expands the
large Ext and module-cohomology constructions. Cache the actual additive groups and
coefficient sheaf, and their maps, in named definitions. The normalization predicate
uses those same concrete maps through an additive-family interface. Its naturality,
degree-zero tensor-unit formula and every connecting-map equation are preserved.
No hypothesis, conclusion, coefficient universe, or target statement changes.
`coherentModuleGroup` is `AddCommGrpCat.of` the existing derived-functor value; it
constructs no new module cohomology. `coherentExtUniverseEquiv` factors the original
common-derived-category universe change into a generic construction. The resolution
equivalence is read directly from `moduleCohomologyExtResolutionNatIso`, exactly as
`moduleCohomologyExtResolutionEquiv` does through `moduleComparisonEquiv`; no comparison
map is changed.

The spellings `X.Modules` and `SheafOfModules.{u} X.ringCatSheaf` are definitionally
equal. Explicit use of the latter avoids failed instance search through the former.
All existing declaration names and visibility are retained.

## Old

```lean
abbrev liftedCoherentEtaleSheaf {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
    (etaleTensorSectionsSheaf F)
```

```lean
def IsNormalizedCoherentEtaleComparison (X : Scheme.{u})
    (c : ∀ (F : X.Modules) [F.IsQuasicoherent] (q : ℕ),
      @Sheaf.H _ _ (Opens.grothendieckTopology X)
          ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj F)
          inferInstance (HasExt.standard _) q ≃+
        @Sheaf.H.{u + 1, u + 1, u, u + 1} _ _ X.smallEtaleTopology
          (liftedCoherentEtaleSheaf F) inferInstance inferInstance q) : Prop :=
  (∀ (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
      (φ : F ⟶ G) (q : ℕ) (x : @Sheaf.H _ _
        (Opens.grothendieckTopology X)
        ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj F)
        inferInstance (HasExt.standard _) q),
    c G q (@Sheaf.H.map _ _ _ inferInstance (HasExt.standard _) _ _
      ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map φ) q x) =
      @Sheaf.H.map.{u + 1, u + 1, u, u + 1} _ _ _ inferInstance inferInstance _ _
        (coherentEtaleMap F G φ) q (c F q x)) ∧
  (∀ (F : X.Modules) [F.IsQuasicoherent]
      (x : @Sheaf.H _ _ (Opens.grothendieckTopology X)
        ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj F)
        inferInstance (HasExt.standard _) 0),
    @Sheaf.H.equiv₀.{u + 1, u + 1, u, u + 1} _ _ _ inferInstance inferInstance
        (liftedCoherentEtaleSheaf F) _ terminalIsTerminal (c F 0 x) =
      ULift.up (tensorSectionsUnit (⊤_ X.Etale).hom F
        (@Sheaf.H.equiv₀ _ _ _ inferInstance (HasExt.standard _)
          ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj F) _ isTerminalTop x))) ∧
  ∀ (S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf))
      [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
      (_hS : S.ShortExact)
      (hz : coherentEtaleMap S.X₁ S.X₂ S.f ≫ coherentEtaleMap S.X₂ S.X₃ S.g = 0)
      (ha : (S.map (SheafOfModules.toSheaf.{u} X.ringCatSheaf)).ShortExact)
      (he : (ShortComplex.mk (coherentEtaleMap S.X₁ S.X₂ S.f)
        (coherentEtaleMap S.X₂ S.X₃ S.g) hz).ShortExact)
      (q : ℕ) (x : @Sheaf.H _ _ (Opens.grothendieckTopology X)
        ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj S.X₃)
        inferInstance (HasExt.standard _) q),
    c S.X₁ (q + 1)
        (@Abelian.Ext.comp _ _ _ (HasExt.standard _) _ _ _ q 1 x
          (@ShortComplex.ShortExact.extClass _ _ _ (HasExt.standard _) _ ha)
          (q + 1) rfl) =
      @Abelian.Ext.comp _ _ _ inferInstance _ _ _ q 1 (c S.X₃ q x)
        (@ShortComplex.ShortExact.extClass _ _ _ inferInstance _ he) (q + 1) rfl
```

```lean
def normalizedCoherentEtaleComparison {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (F : X.Modules)
    [F.IsQuasicoherent] (q : ℕ) :
    @Sheaf.H _ _ (Opens.grothendieckTopology X)
        ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj F)
        inferInstance (HasExt.standard _) q ≃+
      @Sheaf.H.{u + 1, u + 1, u, u + 1} _ _ X.smallEtaleTopology
        (liftedCoherentEtaleSheaf F) inferInstance inferInstance q :=
  Classical.choose (exists_unique_normalizedCoherentEtaleComparison f) F q
```

```lean
def moduleAbelianCohomologyLarge (X : Scheme.{u}) (F : X.Modules) (q : ℕ) :
    ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F) ≃+
      @Sheaf.H _ _ (Opens.grothendieckTopology X)
        ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj F)
        inferInstance (HasExt.standard _) q :=
  letI := HasDerivedCategory.standard
    (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
  letI : HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    HasExt.standard _
  (moduleCohomologyExtResolutionEquiv X F q).trans
    (Abelian.Ext.homAddEquiv.{u + 1, u}.trans
      Abelian.Ext.homAddEquiv.{u + 1, u + 1}.symm)
```

```lean
def canonicalCoherentEtaleComparison {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (F : X.Modules)
    [F.IsQuasicoherent] (q : ℕ) :
    @Sheaf.H.{u + 1, u + 1, u, u + 1} _ _ X.smallEtaleTopology
        (liftedCoherentEtaleSheaf F) inferInstance inferInstance q ≃+
      ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F) :=
  ((moduleAbelianCohomologyLarge X F q).trans
    (normalizedCoherentEtaleComparison f F q)).symm
```

```lean
def coherentAdditiveEndomorphism (X : Scheme.{u}) (F : X.Modules) (q : ℕ)
    (φ : (SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj F ⟶
      (SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj F) :
    ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F) →+
      ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F) :=
  (moduleAbelianCohomologyLarge X F q).symm.toAddMonoidHom.comp
    ((@Sheaf.H.map _ _ _ inferInstance (HasExt.standard _) _ _ φ q).comp
      (moduleAbelianCohomologyLarge X F q).toAddMonoidHom)
```

## New

```lean
abbrev liftedCoherentEtaleSheaf {X : Scheme.{u}} (F : SheafOfModules.{u} X.ringCatSheaf)
    [F.IsQuasicoherent] : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  CoherentEtale.Coeff F
```

```lean
def IsNormalizedCoherentEtaleComparison (X : Scheme.{u})
    (c : ∀ (F : SheafOfModules.{u} X.ringCatSheaf) [F.IsQuasicoherent] (q : ℕ),
      CoherentEtale.Source X F q ≃+ CoherentEtale.Target X F q) : Prop :=
  CoherentEtale.IsNormalized X (fun F G _ _ φ ↦ coherentEtaleMap F G φ)
    (fun F _ q ↦ (c F q).toAddMonoidHom)
```

```lean
def normalizedCoherentEtaleComparison {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (F : SheafOfModules.{u} X.ringCatSheaf)
    [F.IsQuasicoherent] (q : ℕ) :
    CoherentEtale.Source X F q ≃+ CoherentEtale.Target X F q :=
  Classical.choose (exists_unique_normalizedCoherentEtaleComparison f) F q
```

```lean
def moduleAbelianCohomologyLarge (X : Scheme.{u})
    (F : SheafOfModules.{u} X.ringCatSheaf) (q : ℕ) :
    coherentModuleGroup X F q ≃+ CoherentEtale.Source X F q :=
  ((moduleCohomologyExtResolutionNatIso X q).app F).addCommGroupIsoToAddEquiv.trans
    (@coherentExtUniverseEquiv
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      inferInstance inferInstance (comparisonHasExt X) (HasExt.standard _) _ _ q)
```

```lean
def canonicalCoherentEtaleComparison {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (F : SheafOfModules.{u} X.ringCatSheaf)
    [F.IsQuasicoherent] (q : ℕ) :
    CoherentEtale.Target X F q ≃+ coherentModuleGroup X F q :=
  ((moduleAbelianCohomologyLarge X F q).trans
    (normalizedCoherentEtaleComparison f F q)).symm
```

```lean
def coherentAdditiveEndomorphism (X : Scheme.{u}) (F : SheafOfModules.{u} X.ringCatSheaf) (q : ℕ)
    (φ : (SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj F ⟶
      (SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj F) :
    coherentModuleGroup X F q →+ coherentModuleGroup X F q :=
  (moduleAbelianCohomologyLarge X F q).symm.toAddMonoidHom.comp
    ((@Sheaf.H.map _ _ _ inferInstance (HasExt.standard _) _ _ φ q).comp
      (moduleAbelianCohomologyLarge X F q).toAddMonoidHom)
```

The remaining module binders use the same definitionally equal explicit module type.
The existence-and-uniqueness theorem quantifies over the same equivalences, with the
carriers written using `CoherentEtale.Source` and `CoherentEtale.Target`.

New cached construction (no former declaration):

```lean
def coherentModuleGroup (X : Scheme.{u})
    (F : SheafOfModules.{u} X.ringCatSheaf) (q : ℕ) : AddCommGrpCat.{u} :=
  AddCommGrpCat.of ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F)
```

New cached construction (no former declaration):

```lean
def coherentExtUniverseEquiv {A : Type u₀} [Category.{v₀} A] [Abelian A]
    [HasExt.{v} A] [HasExt.{w} A] (M N : A) (q : ℕ) :
    Abelian.Ext.{v} M N q ≃+ Abelian.Ext.{w} M N q :=
  letI := HasDerivedCategory.standard A
  (Abelian.Ext.homAddEquiv.{max u₀ v₀, v}).trans
    (Abelian.Ext.homAddEquiv.{max u₀ v₀, w}).symm
```

## Users

Refreshed on 2026-10-18 after the return at b134590b6. The current
`tools/downstream.py Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison`
reports 17 downstream modules, nine of them direct importers. Searches with
`--uses` for every original declaration find the explicit users below; all 17
importers are recorded so the transitive impact is also visible. No consumer
is adapted. Current claims contain no holder for these consumers.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison | Q3 | Definitionally equal cached presentations; its proof hole is reduced to the normalized additive-map construction. |
| Sheaf.AlgebraicGeometry.CoherentEtaleComparisonPullback | unclaimed | Uses the same structure sheaf and canonical comparison; checked unchanged. |
| Sheaf.AlgebraicGeometry.CoherentFrobeniusComparison | unclaimed | Uses the same normalized and canonical comparisons and transported action; checked unchanged. |
| Sheaf.AlgebraicGeometry.CoherentFrobeniusPullback | unclaimed | Uses the same transported additive action; checked unchanged. |
| Sheaf.AlgebraicGeometry.CoherentPowerComparison | unclaimed | Uses the same normalized comparison and structure sheaf; checked unchanged. |
| Sheaf.AlgebraicGeometry.PrimeCurveArtinSchreierKernel | unclaimed | Uses liftedCoherentEtaleSheaf twice in the kernel statement. CoherentEtale.Coeff unfolds to the identical coefficient lift of etaleTensorSectionsSheaf, preserving both the morphism type and the ULift component formula; checked unchanged. |
| Sheaf.AlgebraicGeometry.QcoherentCohomologyComparisonPullback | unclaimed | Uses the same lifted sheaf, maps and module cohomology; checked unchanged. |
| Sheaf.AlgebraicGeometry.QcoherentNormalizedComparison | unclaimed | Uses the same lifted sheaf, coefficient map and normalization; checked unchanged. |
| Sheaf.AlgebraicGeometry.QcoherentNormalizedPullbackSquare | unclaimed | Uses the same lifted sheaf, normalization and module cohomology; checked unchanged. |
| Sheaf.AlgebraicGeometry.SmoothCurveEtaleStructureDirectImages | unclaimed | Uses the same lifted sheaf in the structure direct-image comparison; checked unchanged. |
| Sheaf.AlgebraicGeometry.ConstantShriekRelativeDimensionOne | unclaimed | Transitive importer; no direct use of a changed declaration. |
| Sheaf.AlgebraicGeometry.EtaleAffineLineShriekFiniteTypeDenseOpen | unclaimed | Transitive importer; no direct use of a changed declaration. |
| Sheaf.AlgebraicGeometry.EtaleAffineLineShriekSheafConstructible | unclaimed | Transitive importer; no direct use of a changed declaration. |
| Sheaf.AlgebraicGeometry.EtaleCompactificationConstructibility | unclaimed | Transitive importer; no direct use of a changed declaration. |
| Sheaf.AlgebraicGeometry.EtaleProperDirectImageFiniteness | unclaimed | Transitive importer; no direct use of a changed declaration. |
| Sheaf.AlgebraicGeometry.LisseOpenRelativeLineConstructibility | unclaimed | Transitive importer; no direct use of a changed declaration. |
| Sheaf.AlgebraicGeometry.ProperSmoothCurvesFiniteModule | unclaimed | Transitive importer; no direct use of a changed declaration. |
| Sheaf.AlgebraicGeometry.ProperSmoothCurvesPrimeCoefficients | unclaimed | Transitive importer; no direct use of a changed declaration. |

The nine direct importers are the first nine consumer rows. Their unchanged
sources are compiled individually in dependency order against the retained
sandbox modules. This includes PrimeCurveArtinSchreierKernel, the specific
consumer omitted from the returned change record. No forced adaptation is
necessary. The previous stale CoherentEtaleRawDirectImageComparison row is
removed because that module no longer exists in the current library.

The targets whose definitions traverse these comparisons retain their original
meanings. The retained Lean interface check proves `Iff.rfl` between the full
original normalization formula and the cached predicate, including its boundary
clause. This definition change reopens the statement-meaning review for any
target traversing it, as required by AGENTS.md section 4.

## Status

landed 20261018T101752-L-4010951 2026-10-18 (merge of deliver/Q3/Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison)
