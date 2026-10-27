# ringedSiteOrdinaryHomComparison

## Reason

Repair the returns at heads 4c45fe90e and 0cf283214. The latter return identifies
public signatures in CoefficientBidualEvaluationShiftOne and
CoefficientBidualTriangleCompatibility that also need explicit public duality imports.
The slice comparison proof imports the normalized internal-Hom shift module. That module imported RingedSiteDualityMaps solely
for its fixed augmentation and ordinary-Hom comparison. The new duality restriction proof
imports slice comparisons, completing the reported cycle. Separate the existing five
comparison declarations into RingedSiteOrdinaryHomComparison, which imports only their
independent representative and resolution interfaces. This is an import-graph repair:
all five declaration names, signatures, docstrings and bodies are preserved verbatim.
No mathematical definition or target meaning changes.

## Old

The following block belonged to Sheaf.CategoryTheory.RingedSiteDualityMaps:

```lean
/-- The actual augmentation to the fixed K-injective replacement.
Source: Stacks 079P (blueprint: lem-sfb-ringed-site-duality-maps). -/
def ringedSiteHomAugmentation : 𝟭 _ ⟶ WeilConjectures.coefficientHomResolution.{r, c, v} J R :=
  letI :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r} J R).1
  CochainComplex.toKInjectiveResolution.{max c v r} _

/-- The action of the recorded Hom-complex bifunctor, with both variables explicit.
Source: Stacks 0A8X (blueprint: lem-sfb-ringed-site-duality-maps). -/
def ringedSiteHomComplexMap
    {E E' F F' : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ}
    (f : E' ⟶ E) (g : F ⟶ F') :
    homComplex.{c, v, max c v r, max c v r} (R := R) E F ⟶
      homComplex.{c, v, max c v r, max c v r} (R := R) E' F' :=
  ((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).map f.op).app F ≫
    ((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).obj (op E')).map g

/-- Ordinary Hom to derived Hom, using the fixed augmentation and localization factorization.
Source: Stacks 0A95 (blueprint: lem-sfb-ringed-site-duality-maps). -/
def ringedSiteOrdinaryHomComparison (E F : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ) :
    DerivedCategory.Q.obj (homComplex.{c, v, max c v r, max c v r} (R := R) E F) ⟶
      (derivedInternalHomOfUniverses.{c, v, r, w} J R).obj
        (op (DerivedCategory.Q.obj E), DerivedCategory.Q.obj F) :=
  DerivedCategory.Q.map
    (ringedSiteHomComplexMap.{c, v, r} J R (𝟙 E) ((ringedSiteHomAugmentation.{c, v, r} J R).app F))
      ≫
      (WeilConjectures.coefficientHomResolutionIso.{r, c, v, w} J R E F).inv

/-- The ordinary comparison is invertible precisely when its augmentation Hom map is.
Source: Stacks 0A95 (blueprint: lem-sfb-ringed-site-duality-maps).
Proof: the factorization comparison is an isomorphism. Q inverts the displayed
quasi-isomorphism, so their composite is an isomorphism. -/
theorem ringedSiteOrdinaryHomComparison_isIso (E F : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (h : QuasiIso (ringedSiteHomComplexMap.{c, v, r} J R (𝟙 E)
      ((ringedSiteHomAugmentation.{c, v, r} J R).app F))) :
    IsIso (ringedSiteOrdinaryHomComparison.{c, v, r, w} J R E F) := by
  let _ := h
  unfold ringedSiteOrdinaryHomComparison
  infer_instance

/-- The specified comparison iso when ordinary Hom computes derived Hom.
Source: Stacks 0A95 (blueprint: lem-sfb-ringed-site-duality-maps). -/
def ringedSiteOrdinaryHomIso (E F : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (h : QuasiIso (ringedSiteHomComplexMap.{c, v, r} J R (𝟙 E)
      ((ringedSiteHomAugmentation.{c, v, r} J R).app F))) :=
  letI := ringedSiteOrdinaryHomComparison_isIso.{c, v, r, w} J R E F h
  asIso (ringedSiteOrdinaryHomComparison.{c, v, r, w} J R E F)
```

RingedInternalHomShiftOfUniverses had:

```lean
public import Sheaf.CategoryTheory.RingedSiteDualityMaps
```

RingedSliceHomSourceShift and RingedSiteSignedDualRestriction received the duality
model through that public import and did not import the duality module themselves.
CoefficientBidualEvaluationShiftOne and CoefficientBidualTriangleCompatibility had
only `import all Sheaf.CategoryTheory.RingedSiteDualityMaps`; it provides private
proof access, not the public access needed by their existing signatures.

## New

The exact block above belongs to Sheaf.CategoryTheory.RingedSiteOrdinaryHomComparison.
RingedSiteDualityMaps adds:

```lean
public import Sheaf.CategoryTheory.RingedSiteOrdinaryHomComparison
```

RingedInternalHomShiftOfUniverses replaces the old import with:

```lean
public import Sheaf.CategoryTheory.RingedSiteOrdinaryHomComparison
```

RingedSliceHomSourceShift, RingedSiteSignedDualRestriction,
CoefficientBidualEvaluationShiftOne and CoefficientBidualTriangleCompatibility each add:

```lean
public import Sheaf.CategoryTheory.RingedSiteDualityMaps
```

All other lines of those five adapted modules are unchanged. None was claimed by
another group when inspected in coord/claims. No WeilConjectures source file changes.

## Users

Read the direct declaration users reported by tools/downstream.py --uses for the five
moved names. Also checked all direct shift importers and, by source import-closure
analysis, all modules mentioning the duality declarations. The earlier census was
wrong about the two coefficient-bidual consumers: their private `import all` is
insufficient for the public signatures. The four explicit imports above restore
the needed public paths. The lower comparison module and the revised shift module have no path to RingedSiteDualityMaps,
even if RingedSliceNormalizedComparisons imports the shift module as in the return.
The four added public imports restore the original public signatures without changing
their theorem bodies. Existing slice-source-shift sorry is retained, not added.

The exact compiler errors motivating the two coefficient-bidual adaptations are the
return's unknown identifiers `RingedSiteDualityModel`, `ringedSiteDualityUnit` and
`ringedSiteBidual` in public declarations. Each module gains only the public import
at line 9; their private `import all` lines and all declarations are unchanged.
A fresh source scan finds only CoefficientBidualTriangleCompatibility importing
CoefficientBidualEvaluationShiftOne, and no importers of
CoefficientBidualTriangleCompatibility. Both passed the fresh packet compilation (37.0 seconds and 37.4 seconds respectively).
A temporary importing module also checked public visibility of the three names and
passed in 9.4 seconds; it is not delivered.
The overlay has no source import cycle among the 655 modules reachable from the
item and these two consumers. Other private-only uses of the same names retain
their existing proof imports and do not need public-import adaptations.

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.RingedSiteDualityMaps | U7 | Reexports the unchanged five declarations from the lower module. |
| Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses | unclaimed | Replace the public duality import by the lower comparison import; shift signatures and proofs unchanged. |
| Sheaf.Algebra.Homology.RingedSliceHomSourceShift | unclaimed | Add explicit public duality import for RingedSiteDualityModel in the existing signature. |
| Sheaf.CategoryTheory.RingedSiteSignedDualRestriction | unclaimed | Add explicit public duality import for the existing model and coefficient-object signatures. |
| Sheaf.Algebra.Homology.InternalHomLocalizationComparison | unclaimed | The same augmentation remains public through the shift interface; no adaptation. |
| Sheaf.Algebra.Homology.RHomColimitSourceTransport | unclaimed | The same augmentation remains public through the shift interface; no adaptation. |
| Sheaf.Algebra.Homology.RingedSiteStrictPerfectHom | unclaimed | Existing duality imports retain the unchanged comparison interface; no adaptation. |
| Sheaf.CategoryTheory.CoefficientBidualEvaluationShiftOne | unclaimed | Add public duality import for the existing public model, unit and bidual signatures; retain private import all for private proof helpers. |
| Sheaf.CategoryTheory.CoefficientBidualTriangleCompatibility | unclaimed | Add public duality import for the existing public model, unit and bidual signatures; retain private import all for private proof helpers. |
| Sheaf.CategoryTheory.SignedDerivedInternalHomExact | unclaimed | The same comparison remains public through the shift interface; no adaptation. |
| Sheaf.Paper.HomFiniteProjective | unclaimed | The unchanged comparison remains available from its existing duality import path; no adaptation. |
| Sheaf.CategoryTheory.RingedSitePerfectDuality | unclaimed | The unchanged comparison isomorphism remains reexported by duality; no adaptation. |

## Status

landed 20261022T114252-L-597874 2026-10-22 (merge of deliver/U7/Sheaf.CategoryTheory.RingedSiteDualityMaps)
