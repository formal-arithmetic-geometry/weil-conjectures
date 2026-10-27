# AlgebraicGeometry.topDegreeDerivedImage

## Reason

The assembled proof is logically accepted but takes 79--86 seconds when the native
derived image, its unit map and its total/classical comparison are reconstructed
independently in the global and top-degree presentations. Introduce shared canonical
objects and maps in `GlobalLerayUnitSquare`, keep those definitions irreducible for
importers, and delegate the existing top-degree definitions to them. This keeps the
large derived-image expressions out of the final assembly's conversions. The proved
API lemma `globalLerayImage_isGE` gives the nonnegative bound directly for the
shared object, using the existing right-derived single-functor bound. Both modules
use the same native abelian cache `globalLerayModuleAbelian`; its body is the
existing native instance, with no new existence assumption.

All three shared data constructions are real terms: the image is Rf_*(F[0]), the unit
map is exactly `derivedSquareUnitMap`, and the comparison is exactly Mathlib's
`homologyRightDerivedFunctorObjSingleFunctorIso`, via the existing
`schemeSingleCohomologyComparison`. No data is selected from a new
existence statement. The new shared module is a public import because these data
definitions use it. Existing public imports remain present.

## Old

```lean
def topDegreeDerivedImage {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) :
    schemeDerivedCategory.{u, w} S :=
  (schemeDerivedDirectImage.{u, w, w} f).obj
    ((DerivedCategory.singleFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F)

def topDegreeLerayComparison {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) :
    ((DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 1)).obj
        (topDegreeDerivedImage.{u, w} f F) ≅
      (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived 1).obj F) :=
  Functor.homologyRightDerivedFunctorObjSingleFunctorIso
    (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) F 1

def topDegreeTensorBaseChange
    {X S Y T : Scheme.{u}} (f : X ⟶ S) (q : Y ⟶ T) (g : T ⟶ S) (p : Y ⟶ X)
    (hs : p ≫ f = q ≫ g) (F : X.Modules) :
    (derivedPullback.{u, w} g).obj (topDegreeDerivedImage.{u, w} f F) ⟶
      topDegreeDerivedImage.{u, w} q ((Scheme.Modules.tensorPullback p).obj F) := by
  letI : ∀ {V W : Scheme.{u}} (k : V ⟶ W),
      (Scheme.Modules.tensorPullback k).Additive :=
    fun {_ _} k ↦ (Classical.choose exists_derivedPullbackComposition) k
  exact singleDegreeBaseChangeComposite f g p q hs 0 F

def topDegreeBaseChangeMap
    {X S Y T : Scheme.{u}} (f : X ⟶ S) (q : Y ⟶ T) (g : T ⟶ S) (p : Y ⟶ X)
    (hs : p ≫ f = q ≫ g) (F : X.Modules) (M : Y.Modules)
    (a : (Scheme.Modules.tensorPullback p).obj F ⟶ M) :
    (derivedPullback.{u, w} g).obj (topDegreeDerivedImage.{u, w} f F) ⟶
      topDegreeDerivedImage.{u, w} q M :=
  topDegreeTensorBaseChange f q g p hs F ≫
    (schemeDerivedDirectImage q).map ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map a)
```

## New

```lean
def topDegreeDerivedImage {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) :
    schemeDerivedCategory.{u, w} S :=
  globalLerayImage.{u, w} f F

def topDegreeLerayComparison {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) :
    ((DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 1)).obj
        (topDegreeDerivedImage.{u, w} f F) ≅
      (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived 1).obj F) :=
  globalLerayComparison.{u, w} f F 1

def topDegreeTensorBaseChange
    {X S Y T : Scheme.{u}} (f : X ⟶ S) (q : Y ⟶ T) (g : T ⟶ S) (p : Y ⟶ X)
    (hs : p ≫ f = q ≫ g) (F : X.Modules) :
    (derivedPullback.{u, w} g).obj (topDegreeDerivedImage.{u, w} f F) ⟶
      topDegreeDerivedImage.{u, w} q ((Scheme.Modules.tensorPullback p).obj F) := by
  letI : ∀ {V W : Scheme.{u}} (k : V ⟶ W),
      (Scheme.Modules.tensorPullback k).Additive :=
    fun {_ _} k ↦ (Classical.choose exists_derivedPullbackComposition) k
  with_unfolding_all exact singleDegreeBaseChangeComposite f g p q hs 0 F

def topDegreeBaseChangeMap
    {X S Y T : Scheme.{u}} (f : X ⟶ S) (q : Y ⟶ T) (g : T ⟶ S) (p : Y ⟶ X)
    (hs : p ≫ f = q ≫ g) (F : X.Modules) (M : Y.Modules)
    (a : (Scheme.Modules.tensorPullback p).obj F ⟶ M) :
    (derivedPullback.{u, w} g).obj (topDegreeDerivedImage.{u, w} f F) ⟶
      topDegreeDerivedImage.{u, w} q M := by
  with_unfolding_all
    exact topDegreeTensorBaseChange f q g p hs F ≫
      (schemeDerivedDirectImage q).map ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map a)
```

The scalar restriction, classical edge, section pullback, tensor mate and coefficient
composition retain their mathematical formulas. The two latter bodies use explicit
unfolding only to check conversion to the shared endpoints. All existing public types
and the statement of `topDegreeLeray_commutativeSquare` are unchanged. Its node's route
continues to use the same transpose, top edge and local cocycle argument.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.TopDegreeLeraySquare | G3 | Uses shared image and unit-map endpoints in the assembly; same morphisms and comparison. |
| Sheaf.AlgebraicGeometry.CoherentAffineBaseChangeEdge | unclaimed | Its degree-one edge and base-change formulas have the same denotation; one forced proof line also unfolds `globalLerayImage`. Adapted consumer check accepted. |
| Sheaf.AlgebraicGeometry.UnitAffineComparisonTransportCore | unclaimed | Uses the same cohomology and scalar restriction; the unchanged source compiled against the changed dependencies. |
| Sheaf.AlgebraicGeometry.CurveAffineEdge | unclaimed | Tensor base change remains the pinned composite; its existing local transparency setting also includes `globalLerayImage`. Adapted check accepted. |
| Sheaf.AlgebraicGeometry.SmoothCurveEtaleStructureDirectImages | unclaimed | Derived images still denote Rf_*(F[0]); two forced proof lines additionally unfold `globalLerayImage`. Adapted check accepted. |

These are the users identified by `tools/downstream.py --uses` for the original
public declarations. No current claim record was found for the four consumers.
Targets transitively using these definitions require the normal independent
meaning review: the change preserves their exact objects and maps, not merely
isomorphism classes. The existing source-library modules are untouched.

## Consumer adaptation

The original `CoherentAffineBaseChangeEdge` failed in `coherentEdge_typed_pasting`
at `exact raw` (original line 727): the raw theorem used the native derived-image
expressions, while the goal retained `globalLerayImage f G` and
`globalLerayImage q ((tensorPullback p).obj G)`. Its existing line
`delta topDegreeDerivedImage` is extended to
`delta topDegreeDerivedImage globalLerayImage`. This resolves the type mismatch. That version took 64 seconds (>60); local instance
priorities immediately before the private proof section now also select the native
category/additive instances at 3000 and the shared abelian cache at 4000. These are
the dependency's same definitionally equal dictionaries:

```lean
attribute [local instance 3000] SheafOfModules.instCategory SheafOfModules.instPreadditive
attribute [local instance 4000] globalLerayModuleAbelian
```

The exported edge/coefficient data declarations precede this selection and remain
unchanged. All definition-body text, declaration type text, imports and visibility
remain unchanged; later private helpers and cached local instances store the same
native structures through definitionally equal instance arguments. No new mathematical dependency is introduced, since
these are exactly the same expanded image objects.

The original `CurveAffineEdge` (unclaimed) failed at four conversions (original
lines 180, 246, 252, 255) between the structural derived image and `coherentEdgeK`
after the new alias was introduced. Its existing local semireducibility setting
for `topDegreeDerivedImage` now also names `globalLerayImage`. This is its sole
changed line and affects only local conversion, preserving every data body and
signature.

The original `SmoothCurveEtaleStructureDirectImages` failed at `change` in its
quasicoherence and finite-local-freeness local instances (original lines 227, 232).
Their goals retained `globalLerayImage` after the three old wrappers were unfolded.
Its two existing unfold lists now also name `globalLerayImage`. No other source
line changes; the module has no current claim record.

## Status

landed 20261026T065756-L-3232285 2026-10-26 (merge of deliver/G3/Sheaf.AlgebraicGeometry.TopDegreeLeraySquare)
