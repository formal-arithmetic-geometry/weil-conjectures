# AlgebraicGeometry.Scheme.quotientRestrictedHom

## Reason

H6 proves both holes of `Sheaf.Paper.LisseAdicSheaves`. The scalar-composition
argument needs quotient restriction for arbitrary rings. The two existing private
restriction helpers therefore use `Ring` instead of `CommRing`; their constructions
and underlying functions are unchanged. The old private balanced-map implementation
is replaced by Mathlib's semilinear tensor map, with the identical pure-tensor formula.

The preflight also classifies the added universe parameters, private proof sections,
section variables, `omit` commands and local transparency attributes as command
changes requiring a change record. They serve only the new proofs and prevent
repeated unfolding during elaboration. No exported attribute, public import, public
signature or public non-theorem body changes. No target meaning changes or target
statement review is required.

## Old

Existing private signatures, verbatim:

```lean
private def quotientRestrictedHom {S A : Type (u + 1)} [CommRing S] [CommRing A]
    (q : S →+* A) (hq : Function.Surjective q) (M N : ModuleCat.{u + 1} A)
    (f : (ModuleCat.restrictScalars.{u + 1} q).obj M ⟶
      (ModuleCat.restrictScalars.{u + 1} q).obj N) :
    M ⟶ N
```

```lean
private def quotientRestrictedSheafHom {S A : Type (u + 1)} [CommRing S] [CommRing A]
    (q : S →+* A) (hq : Function.Surjective q)
    (M N : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (f : (sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} q)).obj M ⟶
      (sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} q)).obj N) : M ⟶ N
```

```lean
private def scalarBilinear (F G : LisseRationalSheaf l E Y) :
    E →+ (F.integral ⟶ G.integral) →+
      lisseRationalHom l L Y
        ⟨(lisseIntegralScalarExtension l E Y L ι).obj F.integral⟩
        ⟨(lisseIntegralScalarExtension l E Y L ι).obj G.integral⟩
```

```lean
private theorem scalarBilinear_apply (F G : LisseRationalSheaf l E Y)
    (a : E) (f : F.integral ⟶ G.integral) :
    scalarBilinear l E Y L ι F G a f = TensorProduct.tmul _ (ι a)
      ((lisseIntegralScalarExtension l E Y L ι).map f)
```

```lean
private theorem scalarBilinear_balanced (F G : LisseRationalSheaf l E Y)
    (r : Padic.coefficientExtensionIntegers l E) (a : E) (f : F.integral ⟶ G.integral) :
    scalarBilinear l E Y L ι F G (r • a) f =
      scalarBilinear l E Y L ι F G a (r • f)
```

The previous private rational-map construction, verbatim:

```lean
@[irreducible]
private def rationalScalarMap (F G : LisseRationalSheaf l E Y) :
    lisseRationalHom l E Y F G →+
      lisseRationalHom l L Y
        ⟨(lisseIntegralScalarExtension l E Y L ι).obj F.integral⟩
        ⟨(lisseIntegralScalarExtension l E Y L ι).obj G.integral⟩ :=
  TensorProduct.liftAddHom (scalarBilinear l E Y L ι F G)
    (scalarBilinear_balanced l E Y L ι F G)
```

The previous universe command was `universe u`. The original public declarations
and public definition bodies are retained in the delivery.

## New

The generalized private signatures, verbatim:

```lean
private def quotientRestrictedHom {S A : Type (u + 1)} [Ring S] [Ring A]
    (q : S →+* A) (hq : Function.Surjective q) (M N : ModuleCat.{u + 1} A)
    (f : (ModuleCat.restrictScalars.{u + 1} q).obj M ⟶
      (ModuleCat.restrictScalars.{u + 1} q).obj N) :
    M ⟶ N
```

```lean
private def quotientRestrictedSheafHom {S A : Type (u + 1)} [Ring S] [Ring A]
    (q : S →+* A) (hq : Function.Surjective q)
    (M N : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (f : (sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} q)).obj M ⟶
      (sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} q)).obj N) : M ⟶ N
```

The three `scalarBilinear` helpers are removed. Their only user was the private
`rationalScalarMap`; it now uses the proved tensor universal-property helper:

```lean
@[irreducible]
private def rationalScalarMap (F G : LisseRationalSheaf l E Y) :
    lisseRationalHom l E Y F G →+
      lisseRationalHom l L Y
        ⟨(lisseIntegralScalarExtension l E Y L ι).obj F.integral⟩
        ⟨(lisseIntegralScalarExtension l E Y L ι).obj G.integral⟩ :=
  (tensorSemilinearMap_exists (lisseIntegerInclusion l E L ι)
    (scalarCoefficientSemilinear l E L ι) (scalarHomSemilinear l E Y L ι F G)).choose
```

The helper's pure-tensor formula uniquely determines its additive map. Its witness
is constructed by Mathlib's `TensorProduct.map`, and its proof is complete.

The extra universes are private-proof parameters:

```lean
universe u v w z
```

Representative local transparency commands, verbatim:

```lean
attribute [local irreducible] scalarSheafAdj scalarSheafUnit sheafScalarComp
  scalarTransportIso scalarIdentityTransportIso sheafIso_conjugateWithFormula

attribute [local irreducible] scalarCompositeRawIso scalarCompositeLevelIso
  scalarCompositeFunctorIso

attribute [local irreducible] extendedGenerator

attribute [local irreducible] scalarCompositeFunctorIso scalarIdentityFunctorIso
  rationalScalarIdentityIso rationalScalarCompositeIso
```

All additional section variables are scoped to the private constructions or reproduce
the existing standing hypotheses. The final local unused-section-variable linter
setting preserves the existing coefficient-diagram theorem interface. Private helpers
never enter public definition bodies or signatures.

## Users

`tools/downstream.py Sheaf.Paper.LisseAdicSheaves --uses quotientRestrictedHom
quotientRestrictedSheafHom scalarBilinear scalarBilinear_apply scalarBilinear_balanced`
finds uses only in this module for every changed or removed private declaration.
It lists 140 downstream modules; none mentions any of these private names. Their
public interfaces and meanings are unchanged, so no downstream adaptation is needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.LisseAdicSheaves | H6 | Generalized private quotient helpers; replaced private balanced-map implementation; added proof-local commands and complete proofs. |

No other module is changed or adapted. An audit against the current shared source
finds no changed public declaration header, no new public declaration and no changed
public non-theorem body. The entire delivered module compiles without warnings in
47.6 seconds; the delivery's local axiom audit has also passed.

## Status

landed 20261020T211730-L-3494823 2026-10-20 (merge of deliver/H6/Sheaf.Paper.LisseAdicSheaves)
