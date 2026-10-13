# affineTildePushforwardCohomologyMap / affineTildeRepresentativeCohomologyIso

## Reason

The two lower lemmas need the same concrete coordinates as the parent theorem,
without importing the parent (which would create an import cycle). Inlining the
large coordinate constructions into both theorem types made the parent elaborate
the same derived-functor terms repeatedly and exceed 60 seconds even on its first
use of the edge lemma. Introduce one generic coordinate API, parameterized by the
ordinary comparison sigma, and retain both original names as transparent aliases.
This removes repeated large terms from the theorem interfaces. All data remain
explicit composites. No theorem is divided to evade a compilation limit.

The original signatures, universes, and visibility are unchanged, and the alias
bodies reduce to the original composites. The definitions therefore have exactly
their original meaning in every target. A public import of the coordinate API is
added because it occurs in the public alias bodies. The lower lemmas are imported
only for proofs. The ordinary comparison is locally irreducible in the parent's
proofs to avoid unfolding its naturality and invertibility witnesses accidentally.

## Old

```lean
def affineTildePushforwardCohomologyMap (A B : Type u) [CommRing A] [CommRing B]
    (φ : B →+* A) (C : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    (affineTildeFunctor B).obj ((ModuleCat.restrictScalars φ).obj (C.homology i)) ⟶
      (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i).obj
        ((schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ))).obj
          (DerivedCategory.Q.obj
            (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj C))) := by
  let T := affineTildeFunctor A
  let F := ModuleCat.restrictScalars φ ⋙ affineTildeFunctor B
  let P := Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom φ))
  let : (affineTildeFunctor B).Additive := instAdditiveModuleCatCarrierModulesSpecOfFunctor
  let : (affineTildeFunctor B).PreservesHomology := tilde_preservesHomology B
  let : PreservesFiniteLimits (affineTildeFunctor B) :=
    Functor.preservesFiniteLimits_of_preservesHomology (affineTildeFunctor B)
  let : PreservesFiniteColimits (affineTildeFunctor B) :=
    Functor.preservesFiniteColimits_of_preservesHomology (affineTildeFunctor B)
  let : F.PreservesHomology := inferInstance
  let : T.Additive := instAdditiveModuleCatCarrierModulesSpecOfFunctor
  let : P.Additive := inferInstance
  let D := (T.mapHomologicalComplex (.up ℤ)).obj C
  let a : (F.mapHomologicalComplex (.up ℤ)).obj C ⟶
      (P.mapHomologicalComplex (.up ℤ)).obj D :=
    ((affineTildePushforwardComparison A B φ).hom.mapHomologicalComplex (.up ℤ)).app C
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i
  let β := (RingedSpace.moduleDirectImage
    (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).rightDerivedFunctorUnit
  exact ((C.sc i).mapHomologyIso F).inv ≫
    ((DerivedCategory.homologyFunctorFactors _ i).app
      ((F.mapHomologicalComplex (.up ℤ)).obj C)).inv ≫
    H.map (DerivedCategory.Q.map a) ≫
    H.map (β.app ((HomotopyCategory.quotient _ (.up ℤ)).obj D))

def affineTildeRepresentativeCohomologyIso (A : Type u) [CommRing A]
    (C : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : schemeDerivedCategory (Spec (.of A)))
    (t : DerivedCategory.Q.obj
      (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj C) ≅ L) (i : ℤ) :
    C.homology i ≅ (moduleSpecΓFunctor (R := .of A)).obj
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) i).obj L) := by
  let T := affineTildeFunctor A
  let : T.Additive := instAdditiveModuleCatCarrierModulesSpecOfFunctor
  let : T.PreservesHomology := tilde_preservesHomology A
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) i
  exact tilde.isoTop (R := .of A) (C.homology i) ≪≫
    (moduleSpecΓFunctor (R := .of A)).mapIso
      (((C.sc i).mapHomologyIso T).symm ≪≫
        ((DerivedCategory.homologyFunctorFactors _ i).app
          ((T.mapHomologicalComplex (.up ℤ)).obj C)).symm ≪≫ H.mapIso t)
```

## New

```lean
abbrev affineTildePushforwardCohomologyMap (A B : Type u) [CommRing A] [CommRing B]
    (φ : B →+* A) (C : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    (affineTildeFunctor B).obj ((ModuleCat.restrictScalars φ).obj (C.homology i)) ⟶
      (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i).obj
        ((schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ))).obj
          (DerivedCategory.Q.obj
            (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj C))) :=
  affinePushforwardCohomologyMapOfComparison A B φ
    (affineTildePushforwardComparison A B φ) C i

abbrev affineTildeRepresentativeCohomologyIso (A : Type u) [CommRing A]
    (C : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : schemeDerivedCategory (Spec (.of A)))
    (t : DerivedCategory.Q.obj
      (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj C) ≅ L) (i : ℤ) :
    C.homology i ≅ (moduleSpecΓFunctor (R := .of A)).obj
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) i).obj L) :=
  affinePushforwardRepresentativeCohomologyIso A C L t i
```

The new generic constructors contain the old composites verbatim, with sigma a
parameter instead of `affineTildePushforwardComparison A B phi`. Both tilde
abbreviations reduce to Mathlib's `tilde.functor`. No data or proof are chosen from
a mere existence theorem.

## Users

`tools/downstream.py --uses` reports 431 transitive importers and the following
three modules with direct uses of the changed names (including the item itself).
The transitive importers keep the same elaborated types and the same coordinates.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.AffineTildePushforwardCohomologyNormalization | U1 | Coordinate unfolding in the existing extension proof names the shared constructor; base proof decomposed. |
| Sheaf.Algebra.Homology.AffineBaseChangeTildeOrdinaryComparison | unclaimed | No source adaptation: original map names and elaborated types are retained, with definitionally equal bodies. |
| Sheaf.Algebra.Homology.AffineBaseChangeTildeMateFactorization | P1 | No source adaptation: original map names and elaborated types are retained, with definitionally equal bodies. |

No other module is adapted or delivered. Unchanged originals of the two direct
clients are compiled against the delivered coordinate API before the dry run.

## Status

landed 20261013T211116-L-396106 2026-10-13 (merge of deliver/U1/Sheaf.Algebra.Homology.AffineTildePushforwardCohomologyNormalization)
