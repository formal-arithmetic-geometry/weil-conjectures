# AlgebraicGeometry.Etale.SmoothCompactDualModel and finiteLisseDualPullbackComparison

## Reason

The compact-dual construction specializes generic derived monoidal APIs to module
sheaves. Explicit generic abbreviations keep the derived pullback and degree-zero
complex behind uniform coefficient instances. The finite-dual comparison likewise
infers the result type of its unchanged generic construction. These are definitionally
equal interfaces, not mathematical changes. The original consumer is checked against
them unchanged. The model theorem retains its original signature.

The item adds local derived-functor irreducibility controls and scoped instance
priorities. They are not exported. All added imports of the item are private proof
imports. No declaration, attribute or public import of the adopted source tree changes.

## Old

The existing record, verbatim:

```lean
structure SmoothCompactDualModel (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {S X : Scheme.{u}} (f : X ⟶ S)
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) where
  complex : DerivedCategoryModule Λ S
  boundedConstructible : DerivedCategory.isBoundedConstructible Λ S complex
  openIso : ∀ (U : S.Opens) (XU : Scheme.{u}) (p : XU ⟶ X) (fU : XU ⟶ U.toScheme),
    IsPullback p fU f U.ι →
    ((R(lowerStar (ModuleCat.{u + 1} Λ) fU)).obj
        ((L(upperStar (ModuleCat.{u + 1} Λ) p)).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj L)) ≅
      ((derivedHom (ModuleCat.{u + 1} Λ) U.toScheme).obj
        (op ((L(upperStar (ModuleCat.{u + 1} Λ) U.ι)).obj complex))).obj
          (constantComplex Λ U.toScheme))
  testIso : ∀ (U : S.Opens) (XU : Scheme.{u}) (p : XU ⟶ X) (fU : XU ⟶ U.toScheme),
    IsPullback p fU f U.ι →
    ∀ (T : Scheme.{u}) [IsNoetherian T] (v : T ⟶ U.toScheme)
      (XT : Scheme.{u}) (vX : XT ⟶ XU) (fT : XT ⟶ T),
    IsPullback vX fT fU v →
    ((R(lowerStar (ModuleCat.{u + 1} Λ) fT)).obj
        ((L(upperStar (ModuleCat.{u + 1} Λ) vX)).obj
          ((L(upperStar (ModuleCat.{u + 1} Λ) p)).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj L))) ≅
      ((derivedHom (ModuleCat.{u + 1} Λ) T).obj
        (op ((L(upperStar (ModuleCat.{u + 1} Λ) v)).obj
          ((L(upperStar (ModuleCat.{u + 1} Λ) U.ι)).obj complex)))).obj
            (constantComplex Λ T))
  exchange : ∀ (U : S.Opens) (XU : Scheme.{u}) (p : XU ⟶ X) (fU : XU ⟶ U.toScheme)
    (sqU : IsPullback p fU f U.ι)
    (T : Scheme.{u}) [IsNoetherian T] (v : T ⟶ U.toScheme)
    (XT : Scheme.{u}) (vX : XT ⟶ XU) (fT : XT ⟶ T)
    (sq : IsPullback vX fT fU v),
    (L(upperStar (ModuleCat.{u + 1} Λ) v)).map (openIso U XU p fU sqU).hom ≫
        finiteLisseDualPullbackComparison v
          ((L(upperStar (ModuleCat.{u + 1} Λ) U.ι)).obj complex) =
      (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
          ((L(upperStar (ModuleCat.{u + 1} Λ) p)).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj L)) ≫
        (testIso U XU p fU sqU T v XT vX fT sq).hom
```

The existing finite-dual comparison, verbatim:

```lean
noncomputable def finiteLisseDualPullbackComparison
    {Λ : Type (u + 1)} [CommRing Λ] {T T' : Scheme.{u}} (v : T' ⟶ T)
    (C : DerivedCategoryModule Λ T) :
    (L(upperStar (ModuleCat.{u + 1} Λ) v)).obj
        (((derivedHom (ModuleCat.{u + 1} Λ) T).obj (op C)).obj (constantComplex Λ T)) ⟶
      ((derivedHom (ModuleCat.{u + 1} Λ) T').obj
        (op ((L(upperStar (ModuleCat.{u + 1} Λ) v)).obj C))).obj (constantComplex Λ T') :=
  derivedHomPullbackAlongIsoComparison v C (constantComplex Λ T) (constantComplex Λ T')
    (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) v)
```

## New

The generic aliases and their equality API:

```lean
noncomputable abbrev smoothCompactPullback
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {S T : Scheme.{u}} (v : T ⟶ S) :
    _root_.DerivedCategory (Sheaf S.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf T.smallEtaleTopology A) :=
  L(upperStar A v)


/-- The generic pullback alias is the standard derived inverse image. -/
theorem smoothCompactPullback_eq
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {S T : Scheme.{u}} (v : T ⟶ S) :
    smoothCompactPullback A v = L(upperStar A v) := by
  rfl


/-- A sheaf placed in degree zero, with generic coefficient instances. -/
noncomputable abbrev smoothCompactSingle
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] (X : Scheme.{u})
    (L : Sheaf X.smallEtaleTopology A) :
    _root_.DerivedCategory (Sheaf X.smallEtaleTopology A) :=
  (_root_.DerivedCategory.singleFunctor _ 0).obj L
```

The record, verbatim:

```lean
structure SmoothCompactDualModel (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {S X : Scheme.{u}} (f : X ⟶ S)
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) where
  complex : DerivedCategoryModule Λ S
  boundedConstructible : DerivedCategory.isBoundedConstructible Λ S complex
  openIso : ∀ (U : S.Opens) (XU : Scheme.{u}) (p : XU ⟶ X) (fU : XU ⟶ U.toScheme),
    IsPullback p fU f U.ι →
    ((R(lowerStar (ModuleCat.{u + 1} Λ) fU)).obj
        ((smoothCompactPullback (ModuleCat.{u + 1} Λ) p).obj
          (smoothCompactSingle (ModuleCat Λ) X L)) ≅
      ((derivedHom (ModuleCat.{u + 1} Λ) U.toScheme).obj
        (op ((smoothCompactPullback (ModuleCat.{u + 1} Λ) U.ι).obj complex))).obj
          (constantComplex Λ U.toScheme))
  testIso : ∀ (U : S.Opens) (XU : Scheme.{u}) (p : XU ⟶ X) (fU : XU ⟶ U.toScheme),
    IsPullback p fU f U.ι →
    ∀ (T : Scheme.{u}) [IsNoetherian T] (v : T ⟶ U.toScheme)
      (XT : Scheme.{u}) (vX : XT ⟶ XU) (fT : XT ⟶ T),
    IsPullback vX fT fU v →
    ((R(lowerStar (ModuleCat.{u + 1} Λ) fT)).obj
        ((smoothCompactPullback (ModuleCat.{u + 1} Λ) vX).obj
          ((smoothCompactPullback (ModuleCat.{u + 1} Λ) p).obj
            (smoothCompactSingle (ModuleCat Λ) X L))) ≅
      ((derivedHom (ModuleCat.{u + 1} Λ) T).obj
        (op ((smoothCompactPullback (ModuleCat.{u + 1} Λ) v).obj
          ((smoothCompactPullback (ModuleCat.{u + 1} Λ) U.ι).obj complex)))).obj
            (constantComplex Λ T))
  exchange : ∀ (U : S.Opens) (XU : Scheme.{u}) (p : XU ⟶ X) (fU : XU ⟶ U.toScheme)
    (sqU : IsPullback p fU f U.ι)
    (T : Scheme.{u}) [IsNoetherian T] (v : T ⟶ U.toScheme)
    (XT : Scheme.{u}) (vX : XT ⟶ XU) (fT : XT ⟶ T)
    (sq : IsPullback vX fT fU v),
    (smoothCompactPullback (ModuleCat.{u + 1} Λ) v).map (openIso U XU p fU sqU).hom ≫
        finiteLisseDualPullbackComparison v
          ((smoothCompactPullback (ModuleCat.{u + 1} Λ) U.ι).obj complex) =
      (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
          ((smoothCompactPullback (ModuleCat.{u + 1} Λ) p).obj
            (smoothCompactSingle (ModuleCat Λ) X L)) ≫
        (testIso U XU p fU sqU T v XT vX fT sq).hom
```

The finite-dual comparison retains its binders and construction and infers their
result type, definitionally the original type:

```lean
noncomputable def finiteLisseDualPullbackComparison
    {Λ : Type (u + 1)} [CommRing Λ] {T T' : Scheme.{u}} (v : T' ⟶ T)
    (C : DerivedCategoryModule Λ T) :=
  derivedHomPullbackAlongIsoComparison v C (constantComplex Λ T) (constantComplex Λ T')
    (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) v)
```

The explicit relative dual is the derived internal Hom. Its canonical bidual map is
braided evaluation transposed into the double internal Hom, followed by the equality
isomorphism naming the relative-dual alias. Relative-dual finiteness, dualizability and
biduality are proved from source APIs. No object is selected from an unproved existence
statement. The private image constructor is the actual functor image Rf_! N, with a
proved identity isomorphism. The comparison isomorphisms are built from canonical
adjunction, compact exchange and the inverse of the explicit bidual map.

Two public property theorems in their own modules remain deferred: Cartesian
compatibility of compact adjunction, and the affine-line exceptional-exchange case
with finite field coefficients. Their sources, complete proofs in words, and DAG
nodes accompany the packet. Neither asserts existence of a compact model.

The higher source smooth-base-change implementation now reaches this item through
projective-line trace, affine-line Kunneth and Deligne finiteness. To avoid a cycle the
item uses the existing lower etale/affine-line chart reduction and isolates its
finite-field affine-line case. Chartwise invertibility is proved directly from the
shifted rank-one description, so CohomologicalSmoothness is unnecessary. The compact
adjunction module imports UpperShriekCanonicalMaps directly. No higher source theorem
or import is removed.

## Users

The read-only downstream scans for SmoothCompactDualModel and
finiteLisseDualPullbackComparison, supplemented by a search of both Lean roots, find
these three modules with textual uses. Transitive importers use the unchanged parent
API. The model's public imports, field meanings and existence-theorem signature are
unchanged. The consumer compiles without adaptations. Definitions in the targets'
proof closure retain exactly their original mathematical meanings; the independent
definition review should check these equal aliases.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FiniteLisseFieldDual | unclaimed | Infer the definitionally equal type of the unchanged generic comparison. |
| Sheaf.AlgebraicGeometry.SmoothCompactDualModel | B3 | Use equal pullback/single aliases; construct the model from explicit relative dual and compact image. |
| Sheaf.AlgebraicGeometry.SmoothGenericDirectImage | unclaimed | Unchanged source and proof; included for a compile against the final interfaces. |

## Status

landed 20261026T065155-L-2731829 2026-10-26 (merge of deliver/B3/Sheaf.AlgebraicGeometry.SmoothCompactDualModel)
