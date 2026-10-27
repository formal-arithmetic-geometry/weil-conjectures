# relativeKummerAbelianPullback, relativeKummerCohomologyPullback, relativeKummerConstant

## Reason

The original module compiled in approximately 45 seconds before adding the proof; profiling attributed approximately 35–40 seconds to checking its unchanged definitions. Share the scalar-comparison, cohomology-pullback, and degree-zero-section conversions through helpers with abstract coefficient sheaves. All three specialized definitions retain their signatures, irreducible attributes, and the same maps after unfolding the helpers. The generic pullback uses the explicit Ext formula of `cohomologyMap_apply`; this is
the same map by reduction. The three new helpers are irreducible, with formulas unfolded
only when their proofs require them.
Two proved public helpers, `relativeKummerHasSheafify` and `relativeKummerHasExt`,
cache the existing propositional typeclass witnesses. They are used only as local instances
while elaborating the cohomology definitions. Their proofs are `infer_instance`; they
introduce no new assumptions, selected data, or global instance attributes. Sharing these
witnesses reduces the definitions-only compile to approximately 16 seconds.

No data are chosen and no mathematical convention or target statement changes. The item remains one module; this is a definition refactor, not a file split.

## Old

```lean
def relativeKummerAbelianPullback (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hm : 0 < m) (hA : (m : A) = 0) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : IsUnit (m : Γ(Y, ⊤))) (hX : IsUnit (m : Γ(X, ⊤))) :
    (upperStar AddCommGrpCat.{u + 1} f).obj
      ((RawModuleScalarComparison.forget A Y).obj (Scheme.finiteEtaleTateLine Y m A hA)) ⟶
    (RawModuleScalarComparison.forget A X).obj (Scheme.finiteEtaleTateLine X m A hA) :=
  (RawModuleScalarComparison.pullbackIso A f).inv.app
      (Scheme.finiteEtaleTateLine Y m A hA) ≫
    (RawModuleScalarComparison.forget A X).map
      ((Scheme.finiteEtaleTwistPullbackData A m hm hA).c f hY hX 1).hom

def relativeKummerCohomologyPullback (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hm : 0 < m) (hA : (m : A) = 0) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : IsUnit (m : Γ(Y, ⊤))) (hX : IsUnit (m : Γ(X, ⊤))) (q : ℕ) :
    Sheaf.H ((RawModuleScalarComparison.forget A Y).obj
      (Scheme.finiteEtaleTateLine Y m A hA)) q →
    Sheaf.H ((RawModuleScalarComparison.forget A X).obj
      (Scheme.finiteEtaleTateLine X m A hA)) q :=
  fun c ↦ relativeKummerMapOnCohomology
    (relativeKummerAbelianPullback A m hm hA f hY hX) q
    (cohomologyMap f ((RawModuleScalarComparison.forget A Y).obj
      (Scheme.finiteEtaleTateLine Y m A hA)) q c)

def relativeKummerConstant (A : Type (u + 1)) [CommRing A] (m : ℕ) (hm : 0 < m)
    (hA : (m : A) = 0) {k : Type u} [Field k] {ζ : k}
    (hζ : IsPrimitiveRoot ζ m) (T : Scheme.{u}) (aT : T ⟶ Spec (.of k)) (a : A) :
    Sheaf.H ((RawModuleScalarComparison.forget A T).obj
      (Scheme.finiteEtaleTateLine T m A hA)) 0 :=
  letI : NeZero m := ⟨ne_of_gt hm⟩
  (Sheaf.H.equiv₀ ((RawModuleScalarComparison.forget A T).obj
    (Scheme.finiteEtaleTateLine T m A hA))
      (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)).symm
    (Scheme.finiteEtaleTateOneGenerator A m T hA (op (Scheme.Etale.mk (𝟙 T))) a
      ((T.constantZModIsoRootsOfUnitySheaf m aT hζ).hom.hom.app
        (op (Scheme.Etale.mk (𝟙 T)))
          ((toSheafify T.smallEtaleTopology
            ((Functor.const T.Etaleᵒᵖ).obj
              (AddCommGrpCat.of (ULift.{u + 1} (ZMod m))))).app
                (op (Scheme.Etale.mk (𝟙 T))) (ULift.up 1))))
```

## New

The two propositional witness helpers are:

```lean
theorem relativeKummerHasSheafify (T : Scheme.{u}) :
    HasSheafify T.smallEtaleTopology AddCommGrpCat.{u + 1} := by infer_instance
theorem relativeKummerHasExt (T : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) := by infer_instance
```

The coefficient-map helpers and their specializations are:

```lean
@[irreducible]
def relativeKummerUnderlyingPullback (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (c : (upperStar (ModuleCat.{u + 1} A) f).obj F ⟶ G) :
    (upperStar AddCommGrpCat.{u + 1} f).obj
      ((RawModuleScalarComparison.forget A Y).obj F) ⟶
    (RawModuleScalarComparison.forget A X).obj G :=
  (RawModuleScalarComparison.pullbackIso A f).inv.app F ≫
    (RawModuleScalarComparison.forget A X).map c

@[irreducible]
def relativeKummerPullbackOnCohomology {X Y : Scheme.{u}} (f : X ⟶ Y)
    {F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (c : (upperStar AddCommGrpCat.{u + 1} f).obj F ⟶ G) (q : ℕ) :
    Sheaf.H F q → Sheaf.H G q :=
  fun x ↦ relativeKummerMapOnCohomology c q
    ((CategoryTheory.Abelian.Ext.mk₀
      ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).symm.app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom).comp
      (x.mapExactFunctor (upperStar AddCommGrpCat.{u + 1} f)) (zero_add q))

@[irreducible]
def relativeKummerModuleSectionClass (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (x : F.obj.obj (op (Scheme.Etale.mk (𝟙 T)))) :
    Sheaf.H ((RawModuleScalarComparison.forget A T).obj F) 0 :=
  (Sheaf.H.equiv₀ ((RawModuleScalarComparison.forget A T).obj F)
    (show IsTerminal (Scheme.Etale.mk (𝟙 T)) from
      MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)).symm x

@[irreducible]
def relativeKummerAbelianPullback (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hm : 0 < m) (hA : (m : A) = 0) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : IsUnit (m : Γ(Y, ⊤))) (hX : IsUnit (m : Γ(X, ⊤))) :
    (upperStar AddCommGrpCat.{u + 1} f).obj
      ((RawModuleScalarComparison.forget A Y).obj (Scheme.finiteEtaleTateLine Y m A hA)) ⟶
    (RawModuleScalarComparison.forget A X).obj (Scheme.finiteEtaleTateLine X m A hA) :=
  relativeKummerUnderlyingPullback A f
    ((Scheme.finiteEtaleTwistPullbackData A m hm hA).c f hY hX 1).hom

@[irreducible]
def relativeKummerCohomologyPullback (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hm : 0 < m) (hA : (m : A) = 0) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : IsUnit (m : Γ(Y, ⊤))) (hX : IsUnit (m : Γ(X, ⊤))) (q : ℕ) :
    Sheaf.H ((RawModuleScalarComparison.forget A Y).obj
      (Scheme.finiteEtaleTateLine Y m A hA)) q →
    Sheaf.H ((RawModuleScalarComparison.forget A X).obj
      (Scheme.finiteEtaleTateLine X m A hA)) q :=
  relativeKummerPullbackOnCohomology f
    (relativeKummerAbelianPullback A m hm hA f hY hX) q

@[irreducible]
def relativeKummerConstant (A : Type (u + 1)) [CommRing A] (m : ℕ) (hm : 0 < m)
    (hA : (m : A) = 0) {k : Type u} [Field k] {ζ : k}
    (hζ : IsPrimitiveRoot ζ m) (T : Scheme.{u}) (aT : T ⟶ Spec (.of k)) (a : A) :
    Sheaf.H ((RawModuleScalarComparison.forget A T).obj
      (Scheme.finiteEtaleTateLine T m A hA)) 0 :=
  letI : NeZero m := ⟨ne_of_gt hm⟩
  relativeKummerModuleSectionClass A T (Scheme.finiteEtaleTateLine T m A hA)
    (Scheme.finiteEtaleTateOneGenerator A m T hA (op (Scheme.Etale.mk (𝟙 T))) a
      ((T.constantZModIsoRootsOfUnitySheaf m aT hζ).hom.hom.app
        (op (Scheme.Etale.mk (𝟙 T)))
          ((toSheafify T.smallEtaleTopology
            ((Functor.const T.Etaleᵒᵖ).obj
              (AddCommGrpCat.of (ULift.{u + 1} (ZMod m))))).app
                (op (Scheme.Etale.mk (𝟙 T))) (ULift.up 1))))
```

## Users

The read-only downstream scan found the modules below. Direct name searches found the coefficient-map and cohomology-map definitions used only in the item; constants also occur in NormalizedKummerGlobalArrows and RelativeKummerNormalizedStalks. Every consumer sees identical types and definitionally equal formulas. No consumer adaptation is required. The final item and all six unchanged consumers
compiled together against the sandbox overlay without warnings. These definitions occur below the targets, whose meanings are preserved; the definition review remains available to the independent reader.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RelativeKummerStrictLocalInvariance | U7 | Same signatures and maps; no adaptation. |
| Sheaf.AlgebraicGeometry.NormalizedKummerCohomologyArrows | unclaimed at scan | Same signatures and maps; no adaptation. |
| Sheaf.AlgebraicGeometry.NormalizedKummerGeneratorArrows | unclaimed at scan | Same signatures and maps; no adaptation. |
| Sheaf.AlgebraicGeometry.NormalizedKummerGlobalArrows | unclaimed at scan | Same signatures and maps; no adaptation. |
| Sheaf.AlgebraicGeometry.RelativeKummerNormalizedStalks | unclaimed at scan | Same signatures and maps; no adaptation. |
| Sheaf.Paper.KummerSiteCohomologyNormalization | unclaimed at scan | Same signatures and maps; no adaptation. |
| Sheaf.Paper.RelativeKummerSiteNormalization | unclaimed at scan | Same signatures and maps; no adaptation. |

## Status

landed 20261025T002536-L-3130013 2026-10-25 (merge of deliver/U7/Sheaf.AlgebraicGeometry.RelativeKummerStrictLocalInvariance)
