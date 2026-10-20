# AlgebraicGeometry.Etale.supported_kummer_scalar_source

## Reason

The delivery adds a section of private proved categorical helpers and local elaboration
settings. The preflight treats added attributes and options conservatively as interface
changes. This record documents that they are scoped to the private proof section. The
section ends before the public theorem. All original public signatures, definitions and
public imports are unchanged. These proof-scoping edits do not change target meaning.
The companion definition repair separately reopens semantic review as recorded in
`D3-supported-scalar-universal-api.md`.

Local irreducibility keeps Lean from unfolding chosen sheafification and derived
localization constructions while elaborating the categorical proof. The private API
states the same universal property with abstract functors. It changes no public data.

## Old

```lean
def supportedScalarMap (N : ℕ) (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0) :
    ULift.{u + 1} (ZMod N) →+* A :=
  (Scheme.finiteEtaleTwistScalar N A hA).comp ULift.ringEquiv.toRingHom

theorem supported_kummer_scalar_source
    (T : Scheme.{u}) (N : ℕ) (hN : 1 ≤ N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    {D : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i] :
    ∃ (ηD : ordinaryFiniteConstant (ULift.{u + 1} (ZMod N)) D ⟶
        (Sheaf.restrictScalars D.smallEtaleTopology
          (supportedScalarMap N A hA)).obj
          (ordinaryFiniteConstant A D))
      (ηT : ordinaryFiniteConstant (ULift.{u + 1} (ZMod N)) T ⟶
        (Sheaf.restrictScalars T.smallEtaleTopology
          (supportedScalarMap N A hA)).obj
          (ordinaryFiniteConstant A T)),
      (∀ (U : D.Etaleᵒᵖ) (r : ULift.{u + 1} (ZMod N)),
        ηD.hom.app U
          ((toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
            (ModuleCat.of (ULift.{u + 1} (ZMod N)) (ULift.{u + 1} (ZMod N))))).app U r) =
        (toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
          (ModuleCat.of A A))).app U (supportedScalarMap N A hA r)) ∧
      (∀ (U : T.Etaleᵒᵖ) (r : ULift.{u + 1} (ZMod N)),
        ηT.hom.app U
          ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
            (ModuleCat.of (ULift.{u + 1} (ZMod N)) (ULift.{u + 1} (ZMod N))))).app U r) =
        (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
          (ModuleCat.of A A))).app U (supportedScalarMap N A hA r)) ∧
      SupportedDerivedScalarUnit
          (supportedScalarMap N A hA) D
          (ordinaryFiniteConstant (ULift.{u + 1} (ZMod N)) D)
          (ordinaryFiniteConstant A D) ηD ∧
      SupportedDerivedScalarUnit
          (supportedScalarMap N A hA) T
          ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N))) i).obj
            (ordinaryFiniteConstant (ULift.{u + 1} (ZMod N)) D))
          ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
          ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N))) i).map ηD ≫
            (lowerStarCompRestrictScalarsIso
              (supportedScalarMap N A hA) i).inv.app
              (ordinaryFiniteConstant A D)) ∧
      SupportedDerivedScalarUnit
          (supportedScalarMap N A hA) T
          (ordinaryFiniteConstant (ULift.{u + 1} (ZMod N)) T)
          (ordinaryFiniteConstant A T) ηT ∧
      ηT ≫
          (Sheaf.restrictScalars T.smallEtaleTopology
            (supportedScalarMap N A hA)).map
            (supportedConstantUnit A i) =
        supportedConstantUnit (ULift.{u + 1} (ZMod N)) i ≫
          (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N))) i).map ηD ≫
          (lowerStarCompRestrictScalarsIso
            (supportedScalarMap N A hA) i).inv.app
            (ordinaryFiniteConstant A D)
```

The original theorem proof was `by sorry`.

## New

The public definition and theorem signature remain verbatim:

```lean
def supportedScalarMap (N : ℕ) (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0) :
    ULift.{u + 1} (ZMod N) →+* A :=
  (Scheme.finiteEtaleTwistScalar N A hA).comp ULift.ringEquiv.toRingHom

theorem supported_kummer_scalar_source
    (T : Scheme.{u}) (N : ℕ) (hN : 1 ≤ N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    {D : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i] :
    ∃ (ηD : ordinaryFiniteConstant (ULift.{u + 1} (ZMod N)) D ⟶
        (Sheaf.restrictScalars D.smallEtaleTopology
          (supportedScalarMap N A hA)).obj
          (ordinaryFiniteConstant A D))
      (ηT : ordinaryFiniteConstant (ULift.{u + 1} (ZMod N)) T ⟶
        (Sheaf.restrictScalars T.smallEtaleTopology
          (supportedScalarMap N A hA)).obj
          (ordinaryFiniteConstant A T)),
      (∀ (U : D.Etaleᵒᵖ) (r : ULift.{u + 1} (ZMod N)),
        ηD.hom.app U
          ((toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
            (ModuleCat.of (ULift.{u + 1} (ZMod N)) (ULift.{u + 1} (ZMod N))))).app U r) =
        (toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
          (ModuleCat.of A A))).app U (supportedScalarMap N A hA r)) ∧
      (∀ (U : T.Etaleᵒᵖ) (r : ULift.{u + 1} (ZMod N)),
        ηT.hom.app U
          ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
            (ModuleCat.of (ULift.{u + 1} (ZMod N)) (ULift.{u + 1} (ZMod N))))).app U r) =
        (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
          (ModuleCat.of A A))).app U (supportedScalarMap N A hA r)) ∧
      SupportedDerivedScalarUnit
          (supportedScalarMap N A hA) D
          (ordinaryFiniteConstant (ULift.{u + 1} (ZMod N)) D)
          (ordinaryFiniteConstant A D) ηD ∧
      SupportedDerivedScalarUnit
          (supportedScalarMap N A hA) T
          ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N))) i).obj
            (ordinaryFiniteConstant (ULift.{u + 1} (ZMod N)) D))
          ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
          ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N))) i).map ηD ≫
            (lowerStarCompRestrictScalarsIso
              (supportedScalarMap N A hA) i).inv.app
              (ordinaryFiniteConstant A D)) ∧
      SupportedDerivedScalarUnit
          (supportedScalarMap N A hA) T
          (ordinaryFiniteConstant (ULift.{u + 1} (ZMod N)) T)
          (ordinaryFiniteConstant A T) ηT ∧
      ηT ≫
          (Sheaf.restrictScalars T.smallEtaleTopology
            (supportedScalarMap N A hA)).map
            (supportedConstantUnit A i) =
        supportedConstantUnit (ULift.{u + 1} (ZMod N)) i ≫
          (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N))) i).map ηD ≫
          (lowerStarCompRestrictScalarsIso
            (supportedScalarMap N A hA) i).inv.app
            (ordinaryFiniteConstant A D)
```

The theorem proof uses privately constructed normalized constant coefficient maps,
the existing closed supported coefficient-comparison theorem, categorical transport
through identity pushforwards, and the constant-presheaf generator formula for the
pushforward unit. All private definitions are actual constructions; all private
lemmas are proved. No module of another group is edited.

## Users

`tools/downstream.py` with either fully qualified public name lists only this module
as a textual user. A search for the unqualified names also finds only this module.
There are 651 transitive downstream modules, all unaffected because the signatures,
definitions, attributes on existing public declarations and public imports are unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SupportedKummerScalarSource | D3 | One theorem proof filled; private proof API and scoped elaboration settings added. |

## Status

landed 20261020T221115-L-4145063 2026-10-20 (merge of deliver/D3/Sheaf.AlgebraicGeometry.SupportedKummerScalarSource)
