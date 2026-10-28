# WeilConjectures.LocallyFiniteAdicRealization.CondensedStageComparison

## Reason

Extract the native scalar equivalence and comparison record into a data module so that the
new integral normalization statement can import them without a cycle. The assigned module
publicly reexports the data module. Every existing declaration name, signature, attribute and
definition body is preserved. No target meaning changes. No source-library module is changed.

## Old

In Sheaf.Paper.LocallyFiniteAdicCondensedStageComparison:

```lean
/-- The actual coefficient comparison: bounded finite-field functions are locally finite
functions. Source: Bhatt--Scholze, Lemma 6.8.2, via the two published ring comparisons
(blueprint: lem-sf-locally-finite-adic-condensed-stage-comparison). -/
def condensedNativeMap (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    ProEtale.padicAlgClRingObj X l ⟶ abRing l X :=
  (ProEtale.CondensedQbarCoefficientRealization.globalCoefficientIso l X).hom.hom ≫
    ProEtale.padicAlgClSheafToAdicConstantSheaf X l

instance condensedNativeMap_isMonHom (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    IsMonHom (condensedNativeMap l X) := by
  unfold condensedNativeMap
  infer_instance

instance condensedNativeMap_isIso (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    IsIso (condensedNativeMap l X) := by
  unfold condensedNativeMap
  infer_instance

/-- Transport native modules to the condensed coefficient, retaining their abelian sheaves.
Source: Bhatt--Scholze, Lemma 6.8.2; restriction along the specified ring isomorphism
(blueprint: lem-sf-locally-finite-adic-condensed-stage-comparison). -/
def nativeCondensedModules (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :=
  ProEtale.AdicSheaf.forgetAb l X ⋙ Mod.comap (condensedNativeMap l X)

instance nativeCondensedModules_isEquivalence (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    (nativeCondensedModules l X).IsEquivalence := by
  letI := ProEtale.nativeScalarForgetting_isEquivalence l X
  letI : (Mod.comap (condensedNativeMap l X)).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso (condensedNativeMap l X)).isEquivalence_functor
  unfold nativeCondensedModules
  infer_instance

instance nativeCondensedModules_additive (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    (nativeCondensedModules l X).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The exact derived transport along the same coefficient isomorphism.
Source: Bhatt--Scholze, Lemma 6.8.2
(blueprint: lem-sf-locally-finite-adic-condensed-stage-comparison). -/
def nativeCondensedDerived (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :=
  (nativeCondensedModules l X).mapDerivedCategory

instance nativeCondensedDerived_isEquivalence (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    (nativeCondensedDerived l X).IsEquivalence := by
  unfold nativeCondensedDerived
  infer_instance

open AlgebraicallyClosedCoefficients (Index)

/-- Only finite-stage data: full faithful functors on raw rational stages, scalar comparisons,
and their action on a representative. No statement about a Hom colimit is included.
Source: Bhatt--Scholze, Proposition 6.8.14(2) and Remark 6.8.15
(blueprint: lem-sf-locally-finite-adic-condensed-stage-comparison). -/
structure CondensedStageComparison (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (D : NormalizedFunctor l X) where
  finite : ∀ E : Index l (PadicAlgCl l),
    GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) X E ⥤
      ProEtale.PadicSubfieldConstructible X l E
  full : ∀ E, (finite E).Full
  faithful : ∀ E, (finite E).Faithful
  scalar : ∀ {E L : Index l (PadicAlgCl l)} (h : E ≤ L),
    finite E ⋙ ProEtale.constructibleExtendScalars X l h ≅
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).T h ⋙
        finite L
  objectIso : ∀ A : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X,
    (nativeCondensedDerived l X).obj (D.J.obj A) ≅
      ((ProEtale.constructibleToPadicAlgCl X l A.stage).obj
        ((finite A.stage).obj A.obj)).obj
  representative : ∀ {A B : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X}
    (L : Index l (PadicAlgCl l)) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
    (f : A.toStage hA ⟶ B.toStage hB),
    (nativeCondensedDerived l X).map
        (D.J.map (StageSystem.PairCategory.mkHom L hA hB f)) =
      (objectIso A).hom ≫
        (((ProEtale.constructibleToPadicAlgClCompIso X l hA).inv.app
              ((finite A.stage).obj A.obj) ≫
            (ProEtale.constructibleToPadicAlgCl X l L).map
              ((scalar hA).hom.app A.obj ≫ (finite L).map f ≫
                (scalar hB).inv.app B.obj) ≫
            (ProEtale.constructibleToPadicAlgClCompIso X l hB).hom.app
              ((finite B.stage).obj B.obj)).hom) ≫
        (objectIso B).inv
```

## New

The identical declarations below are in Sheaf.Paper.LocallyFiniteAdicCondensedStageData,
publicly reexported by Sheaf.Paper.LocallyFiniteAdicCondensedStageComparison.

```lean
/-- The actual coefficient comparison: bounded finite-field functions are locally finite
functions. Source: Bhatt--Scholze, Lemma 6.8.2, via the two published ring comparisons
(blueprint: lem-sf-locally-finite-adic-condensed-stage-comparison). -/
def condensedNativeMap (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    ProEtale.padicAlgClRingObj X l ⟶ abRing l X :=
  (ProEtale.CondensedQbarCoefficientRealization.globalCoefficientIso l X).hom.hom ≫
    ProEtale.padicAlgClSheafToAdicConstantSheaf X l

instance condensedNativeMap_isMonHom (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    IsMonHom (condensedNativeMap l X) := by
  unfold condensedNativeMap
  infer_instance

instance condensedNativeMap_isIso (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    IsIso (condensedNativeMap l X) := by
  unfold condensedNativeMap
  infer_instance

/-- Transport native modules to the condensed coefficient, retaining their abelian sheaves.
Source: Bhatt--Scholze, Lemma 6.8.2; restriction along the specified ring isomorphism
(blueprint: lem-sf-locally-finite-adic-condensed-stage-comparison). -/
def nativeCondensedModules (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :=
  ProEtale.AdicSheaf.forgetAb l X ⋙ Mod.comap (condensedNativeMap l X)

instance nativeCondensedModules_isEquivalence (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    (nativeCondensedModules l X).IsEquivalence := by
  letI := ProEtale.nativeScalarForgetting_isEquivalence l X
  letI : (Mod.comap (condensedNativeMap l X)).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso (condensedNativeMap l X)).isEquivalence_functor
  unfold nativeCondensedModules
  infer_instance

instance nativeCondensedModules_additive (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    (nativeCondensedModules l X).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The exact derived transport along the same coefficient isomorphism.
Source: Bhatt--Scholze, Lemma 6.8.2
(blueprint: lem-sf-locally-finite-adic-condensed-stage-comparison). -/
def nativeCondensedDerived (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :=
  (nativeCondensedModules l X).mapDerivedCategory

instance nativeCondensedDerived_isEquivalence (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    (nativeCondensedDerived l X).IsEquivalence := by
  unfold nativeCondensedDerived
  infer_instance

open AlgebraicallyClosedCoefficients (Index)

/-- Only finite-stage data: full faithful functors on raw rational stages, scalar comparisons,
and their action on a representative. No statement about a Hom colimit is included.
Source: Bhatt--Scholze, Proposition 6.8.14(2) and Remark 6.8.15
(blueprint: lem-sf-locally-finite-adic-condensed-stage-comparison). -/
structure CondensedStageComparison (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (D : NormalizedFunctor l X) where
  finite : ∀ E : Index l (PadicAlgCl l),
    GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) X E ⥤
      ProEtale.PadicSubfieldConstructible X l E
  full : ∀ E, (finite E).Full
  faithful : ∀ E, (finite E).Faithful
  scalar : ∀ {E L : Index l (PadicAlgCl l)} (h : E ≤ L),
    finite E ⋙ ProEtale.constructibleExtendScalars X l h ≅
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).T h ⋙
        finite L
  objectIso : ∀ A : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X,
    (nativeCondensedDerived l X).obj (D.J.obj A) ≅
      ((ProEtale.constructibleToPadicAlgCl X l A.stage).obj
        ((finite A.stage).obj A.obj)).obj
  representative : ∀ {A B : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X}
    (L : Index l (PadicAlgCl l)) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
    (f : A.toStage hA ⟶ B.toStage hB),
    (nativeCondensedDerived l X).map
        (D.J.map (StageSystem.PairCategory.mkHom L hA hB f)) =
      (objectIso A).hom ≫
        (((ProEtale.constructibleToPadicAlgClCompIso X l hA).inv.app
              ((finite A.stage).obj A.obj) ≫
            (ProEtale.constructibleToPadicAlgCl X l L).map
              ((scalar hA).hom.app A.obj ≫ (finite L).map f ≫
                (scalar hB).inv.app B.obj) ≫
            (ProEtale.constructibleToPadicAlgClCompIso X l hB).hom.app
              ((finite B.stage).obj B.obj)).hom) ≫
        (objectIso B).inv
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.LocallyFiniteAdicFunctorDescentHom | unclaimed | Same public names and bodies; compiles unchanged through the public reexport. |

The new normalization module imports the data module directly. There are no forced
adaptations and no existing importer is delivered as changed.

## Status

landed 20261028T055827-L-814092 2026-10-28 (merge of deliver/X3/Sheaf.Paper.LocallyFiniteAdicCondensedStageComparison)
