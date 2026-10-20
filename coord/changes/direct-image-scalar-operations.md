# AlgebraicGeometry.ProEtale.directImageConstantExchange

## Reason

The proof first needs a cube of scalar and geometric pullbacks. The cube must use
exactly the constructions defining chi and Ex. Moving the five supporting constructors
to DirectImageScalarOperations avoids an import cycle, and the item publicly imports
that module so existing entry imports still provide every original declaration.
The scalar extension, direct image, and scalar pullback isomorphism retain their
original signatures and bodies. The scalar mate and geometric exchange factor through
the actual canonical adjunction with an explicitly typed constant-coefficient
interface. The exchange additionally uses the shared directImageConstantPullbackIso.
These are definitionally the original constructions.
No target signature or intended mathematical definition changes. The independent
reader should recheck this definitional preservation for the target-definition review.
No adopted source-library file is changed.

## Old

```lean
def directImageScalarComparison {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {T V : Scheme.{u}} (f : T ⟶ V) :
    directImageConstantPush A f ⋙ directImageScalarExtension φ V ⟶
      directImageScalarExtension φ T ⋙ directImageConstantPush B f :=
  (mateEquiv
    (Scheme.proEtaleRingDerivedAdjunction f
      (Scheme.proEtaleConstantRing V A) (Scheme.proEtaleConstantRing T A)
      (Scheme.proEtaleConstantRingComparison f A))
    (Scheme.proEtaleRingDerivedAdjunction f
      (Scheme.proEtaleConstantRing V B) (Scheme.proEtaleConstantRing T B)
      (Scheme.proEtaleConstantRingComparison f B))
    (directImageScalarPullbackIso φ f).hom).natTrans

def directImageConstantExchange (A : Type u) [CommRing A]
    {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare h f' f g) :
    directImageConstantPush A f ⋙ Scheme.proEtaleConstantRingDerivedPullback A g ⟶
      Scheme.proEtaleConstantRingDerivedPullback A h ⋙ directImageConstantPush A f' :=
  Scheme.proEtaleAmbientRingedExchange sq
    (Scheme.proEtaleConstantRing X A) (Scheme.proEtaleConstantRing Y A)
    (Scheme.proEtaleConstantRing X' A) (Scheme.proEtaleConstantRing Y' A)
    (Scheme.proEtaleConstantRingComparison f A)
    (Scheme.proEtaleConstantRingComparison g A)
    (Scheme.proEtaleConstantRingComparison h A)
    (Scheme.proEtaleConstantRingComparison f' A)
    ((heq_of_eq (Scheme.proEtaleConstantRingCompositeCoefficients_eq h f A)).trans
      ((congr_arg_heq (fun q : X' ⟶ Y ↦ Scheme.proEtaleConstantRingComparison q A)
        sq.w).trans
          (heq_of_eq (Scheme.proEtaleConstantRingCompositeCoefficients_eq f' g A)).symm))

```

## New

The five constructors now live in
`lean/Sheaf/SecSmoothPurity/DirectImageScalarOperations.lean`. The explicitly typed
canonical adjunction prevents repeated unfolding of the derived functors in mate
calculations; its data remains the actual source-library adjunction. The factored
constructions are:

```lean
def directImageConstantAdjunction (A : Type u) [CommRing A]
    {T V : Scheme.{u}} (f : T ⟶ V) :
    Scheme.proEtaleConstantRingDerivedPullback A f ⊣ directImageConstantPush A f :=
  Scheme.proEtaleRingDerivedAdjunction f
    (Scheme.proEtaleConstantRing V A) (Scheme.proEtaleConstantRing T A)
    (Scheme.proEtaleConstantRingComparison f A)

def directImageScalarComparison {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {T V : Scheme.{u}} (f : T ⟶ V) :
    directImageConstantPush A f ⋙ directImageScalarExtension φ V ⟶
      directImageScalarExtension φ T ⋙ directImageConstantPush B f :=
  (mateEquiv
    (directImageConstantAdjunction A f)
    (directImageConstantAdjunction B f)
    (directImageScalarPullbackIso φ f).hom).natTrans

def directImageConstantPullbackIso (A : Type u) [CommRing A]
    {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare h f' f g) :
    Scheme.proEtaleConstantRingDerivedPullback A g ⋙
      Scheme.proEtaleConstantRingDerivedPullback A f' ≅
        Scheme.proEtaleConstantRingDerivedPullback A f ⋙
          Scheme.proEtaleConstantRingDerivedPullback A h :=
  Scheme.proEtaleAmbientRingedPullbackComparison sq
    (Scheme.proEtaleConstantRing X A) (Scheme.proEtaleConstantRing Y A)
    (Scheme.proEtaleConstantRing X' A) (Scheme.proEtaleConstantRing Y' A)
    (Scheme.proEtaleConstantRingComparison f A)
    (Scheme.proEtaleConstantRingComparison g A)
    (Scheme.proEtaleConstantRingComparison h A)
    (Scheme.proEtaleConstantRingComparison f' A)
    ((heq_of_eq (Scheme.proEtaleConstantRingCompositeCoefficients_eq h f A)).trans
      ((congr_arg_heq (fun q : X' ⟶ Y ↦ Scheme.proEtaleConstantRingComparison q A)
        sq.w).trans
          (heq_of_eq (Scheme.proEtaleConstantRingCompositeCoefficients_eq f' g A)).symm))

/-- The ambient ringed exchange specialized to the canonical constant rings.
Its pullback square is built from the canonical composition comparisons. The two
composite coefficient identifications are the constant comparison for the same
scheme map; the proof below supplies that compatibility, rather than assuming it.
Source: Stacks Tags 07A7, 0D6D and 0E47
(blueprint: lem-fix-direct-image-scalar-exchange). -/
def directImageConstantExchange (A : Type u) [CommRing A]
    {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare h f' f g) :
    directImageConstantPush A f ⋙ Scheme.proEtaleConstantRingDerivedPullback A g ⟶
      Scheme.proEtaleConstantRingDerivedPullback A h ⋙ directImageConstantPush A f' :=
  (mateEquiv
    (directImageConstantAdjunction A f)
    (directImageConstantAdjunction A f')
    (directImageConstantPullbackIso A sq).hom).natTrans
```

## Users

The full `tools/downstream.py` scan reports 468 transitive importers and the seven
actual constructor users listed below. The original public imports remain public,
so all existing exports remain available. Every original constructor signature and
data value is preserved, with scalar-mate and exchange preservation also checked by `rfl`
comparisons against their original complete bodies. No consumer statement changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AbsoluteFrobeniusCoefficientNaturality | unclaimed | Same scalar and pullback constructions through the preserved public entry. |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | unclaimed | Same scalar and pullback constructions. |
| Sheaf.Paper.EtaleProEtaleCoefficientTransport | unclaimed | Same direct-image construction. |
| Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction | unclaimed | Same direct-image construction. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Same pullback, direct image and geometric exchange. |
| Sheaf.SecSmoothPurity.ReductionDirectImageComparison | unclaimed | Same direct image and scalar mate. |
| Sheaf.SecSmoothPurity.ReductionExceptional | unclaimed | Same direct-image data and pullback comparison. |
| Sheaf.SecSmoothPurity.DirectImageScalarExchange | X7 | Publicly re-exports all constructors and original public imports; proves the original theorem. |
| Sheaf.AlgebraicGeometry.ProEtaleConstantScalarPullbackCube | new, X7 | Uses the shared scalar and geometric pullback comparisons. |

## Status

landed 20261020T230848-L-622494 2026-10-20 (merge of deliver/X7/Sheaf.SecSmoothPurity.DirectImageScalarExchange)
