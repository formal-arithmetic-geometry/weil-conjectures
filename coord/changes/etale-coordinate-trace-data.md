# AlgebraicGeometry.Etale.CoordinateTrace canonical definitions

## Reason

The independent contraction-step modules need the canonical maps without importing the
parent theorem, which imports those step modules. Extract all fourteen existing definitions
verbatim into `Sheaf.AlgebraicGeometry.EtaleCoordinateTraceData` and publicly re-export them
from the original module. Declaration names, signatures, bodies, and visibility stay the same;
only their declaration/module ownership and blueprint tags change. This is an interface
extraction to prevent an import cycle, not a workaround for slow compilation.
The original theorem signature is unchanged. No adopted source-library file is edited.

## Old

Declared in `Sheaf.AlgebraicGeometry.EtaleCoordinateTraceContractions`:

```lean
/-- Evaluation of the existing derived tensor bifunctor (notation-free abbreviation).
Source: the two triangle computations in thm-amb-p1-adjunction.proof.md
(blueprint: lem-sfb-etale-coordinate-trace-contractions). -/
abbrev tensor (X : Scheme.{u}) (K E : DerivedCategoryModule A X) :=
  ((derivedTensor (ModuleCat.{u + 1} A) X).obj K).obj E

/-- The existing exact inverse image in its canonically equivalent left-derived presentation.
Source: thm-amb-p1-adjunction.proof.md, both triangles
(blueprint: lem-sfb-etale-coordinate-trace-contractions). -/
abbrev pull {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor

/-- The existing ordinary unbounded right derived direct image.
Source: thm-amb-p1-adjunction.proof.md, both triangles
(blueprint: lem-sfb-etale-coordinate-trace-contractions). -/
abbrev push {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor

/-- The canonical signed tensor swap, without choosing an isomorphism of endpoints.
Source: thm-amb-p1-adjunction.proof.md, even-shift rearrangement
(blueprint: lem-sfb-etale-coordinate-trace-contractions). -/
def swap (X : Scheme.{u}) (K E : DerivedCategoryModule A X) :
    tensor A X K E ≅ tensor A X E K :=
  ((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).app K).app E

/-- The common pullback comparison p1* f* N -> p2* f* N.
Source: thm-amb-p1-adjunction.proof.md, equality of the two maps to the base
(blueprint: lem-sfb-etale-coordinate-trace-contractions). -/
def coordinate {X Y : Scheme.{u}} (f : X ⟶ Y) (N : DerivedCategoryModule A Y) :
    (pull A (pullback.fst f f)).obj ((pull A f).obj N) ≅
      (pull A (pullback.snd f f)).obj ((pull A f).obj N) :=
  (derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
    (CommSq.mk (pullback.condition (f := f) (g := f)).symm)).app N

/-- Ordered projection with the outside coefficient first, conjugated by the actual symmetries.
Source: thm-amb-p1-adjunction.proof.md, projection formula in both coordinates
(blueprint: lem-sfb-etale-coordinate-trace-contractions). -/
def orderedProjectionIso [Finite A] {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (K : DerivedCategoryModule A Y) (E : DerivedCategoryModule A X) :
    tensor A Y K ((push A f).obj E) ≅
      (push A f).obj (tensor A X ((pull A f).obj K) E) :=
  have := isIso_rightDerivedLowerStarProjectionMap_app_app_of_isProper_of_isAddTorsion
    A isAddTorsion_of_finite f E K
  swap A Y K ((push A f).obj E) ≪≫
    asIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app E).app K) ≪≫
      (push A f).mapIso (swap A X E ((pull A f).obj K))

/-- The specified proper exchange for the second projection, from the existing mate.
Source: thm-amb-p1-adjunction.proof.md, first triangle, proper base change
(blueprint: lem-sfb-etale-coordinate-trace-contractions). -/
def exchange2 [Finite A] {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (M : DerivedCategoryModule A X) :
    (pull A f).obj ((push A f).obj M) ≅
      (push A (pullback.snd f f)).obj ((pull A (pullback.fst f f)).obj M) :=
  have := isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring
    A isAddTorsion_of_finite (IsPullback.of_hasPullback f f)
  asIso ((derivedBaseChangeMap (ModuleCat.{u + 1} A)
    (IsPullback.of_hasPullback f f).toCommSq).app M)

/-- The specified proper exchange for the first projection, with the square flipped.
Source: thm-amb-p1-adjunction.proof.md, first-coordinate integration
(blueprint: lem-sfb-etale-coordinate-trace-contractions). -/
def exchange1 [Finite A] {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (M : DerivedCategoryModule A X) :
    (pull A f).obj ((push A f).obj M) ≅
      (push A (pullback.fst f f)).obj ((pull A (pullback.snd f f)).obj M) :=
  have := isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring
    A isAddTorsion_of_finite (IsPullback.of_hasPullback f f).flip
  asIso ((derivedBaseChangeMap (ModuleCat.{u + 1} A)
    (IsPullback.of_hasPullback f f).flip.toCommSq).app M)

/-- H(K) = f* K tensor f* L, as an actual functor, so H(e) has its specified meaning.
Source: thm-amb-p1-adjunction.proof.md, proposed right adjoint
(blueprint: lem-sfb-etale-coordinate-trace-contractions). -/
def H {X Y : Scheme.{u}} (f : X ⟶ Y) (L : DerivedCategoryModule A Y) :
    DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X :=
  pull A f ⋙ derivedTensorRight (ModuleCat.{u + 1} A) X ((pull A f).obj L)

/-- Inverse ordered projection followed by tensoring the given trace and the right unitor.
Source: thm-amb-p1-adjunction.proof.md, the displayed counit
(blueprint: lem-sfb-etale-coordinate-trace-contractions). -/
def evaluation [Finite A] {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (L : DerivedCategoryModule A Y)
    (t : (push A f).obj ((pull A f).obj L) ⟶ constantComplex A Y)
    (K : DerivedCategoryModule A Y) : (push A f).obj ((H A f L).obj K) ⟶ K :=
  (orderedProjectionIso A f K ((pull A f).obj L)).inv ≫
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj K).map t ≫
      (derivedTensorRightUnitor (ModuleCat.{u + 1} A) Y K).hom

/-- Inverse projection for p2, then inverse proper exchange tensor the identity.
This is precisely C_M; L_W is represented by p2* f* L.
Source: thm-amb-p1-adjunction.proof.md, the last arrow defining the unit
(blueprint: lem-sfb-etale-coordinate-trace-contractions). -/
def comparison [Finite A] {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (L : DerivedCategoryModule A Y) (M : DerivedCategoryModule A X) :
    (push A (pullback.snd f f)).obj
      (tensor A (pullback f f) ((pull A (pullback.fst f f)).obj M)
        ((pull A (pullback.snd f f)).obj ((pull A f).obj L))) ≅
      (H A f L).obj ((push A f).obj M) :=
  have := isIso_rightDerivedLowerStarProjectionMap_app_app_of_isProper_of_isAddTorsion
    A isAddTorsion_of_finite (pullback.snd f f)
      ((pull A (pullback.fst f f)).obj M) ((pull A f).obj L)
  (asIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A)
    (pullback.snd f f)).app ((pull A (pullback.fst f f)).obj M)).app
      ((pull A f).obj L))).symm ≪≫
    ((derivedTensor (ModuleCat.{u + 1} A) X).mapIso (exchange2 A f M).symm).app
      ((pull A f).obj L)

/-- FRp2* -> FRp1*, via the normalized direct-image compositors and fp1=fp2.
Source: thm-amb-p1-adjunction.proof.md, coordinate interchange in the first triangle
(blueprint: lem-sfb-etale-coordinate-trace-contractions). -/
def directComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    push A (pullback.snd f f) ⋙ push A f ≅ push A (pullback.fst f f) ⋙ push A f :=
  rightDerivedLowerStarComp (ModuleCat.{u + 1} A) (pullback.snd f f) f ≪≫
    eqToIso (congrArg (push A) (pullback.condition (f := f) (g := f)).symm) ≪≫
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) (pullback.fst f f) f).symm

/-- Identify p1* HK and p2* HK by the tensor and common-base pullback comparisons.
Source: thm-amb-p1-adjunction.proof.md, extracting the common coefficient
(blueprint: lem-sfb-etale-coordinate-trace-contractions). -/
def coordinateH {X Y : Scheme.{u}} (f : X ⟶ Y) (L K : DerivedCategoryModule A Y) :
    (pull A (pullback.fst f f)).obj ((H A f L).obj K) ≅
      (pull A (pullback.snd f f)).obj ((H A f L).obj K) :=
  (pull A (pullback.fst f f)).mapIso
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) f K L).symm ≪≫
    coordinate A f (tensor A Y K L) ≪≫
      (pull A (pullback.snd f f)).mapIso
        (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) f K L)

/-- The given sheaf line placed in degree zero and shifted by the specified even integer.
Source: thm-amb-p1-adjunction.proof.md, the even shifted coefficient
(blueprint: lem-sfb-etale-coordinate-trace-contractions). -/
abbrev shiftedLine {Y : Scheme.{u}}
    (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) (d : ℤ) :
    DerivedCategoryModule A Y :=
  ((_root_.DerivedCategory.singleFunctor _ 0).obj J)⟦(2 * d : ℤ)⟧
```

## New

Declared in `Sheaf.AlgebraicGeometry.EtaleCoordinateTraceData`, publicly re-exported by
`Sheaf.AlgebraicGeometry.EtaleCoordinateTraceContractions`:

```lean
/-- Evaluation of the existing derived tensor bifunctor (notation-free abbreviation).
Source: the two triangle computations in thm-amb-p1-adjunction.proof.md
(blueprint: def-sfb-etale-coordinate-trace-data). -/
abbrev tensor (X : Scheme.{u}) (K E : DerivedCategoryModule A X) :=
  ((derivedTensor (ModuleCat.{u + 1} A) X).obj K).obj E

/-- The existing exact inverse image in its canonically equivalent left-derived presentation.
Source: thm-amb-p1-adjunction.proof.md, both triangles
(blueprint: def-sfb-etale-coordinate-trace-data). -/
abbrev pull {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor

/-- The existing ordinary unbounded right derived direct image.
Source: thm-amb-p1-adjunction.proof.md, both triangles
(blueprint: def-sfb-etale-coordinate-trace-data). -/
abbrev push {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor

/-- The canonical signed tensor swap, without choosing an isomorphism of endpoints.
Source: thm-amb-p1-adjunction.proof.md, even-shift rearrangement
(blueprint: def-sfb-etale-coordinate-trace-data). -/
def swap (X : Scheme.{u}) (K E : DerivedCategoryModule A X) :
    tensor A X K E ≅ tensor A X E K :=
  ((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).app K).app E

/-- The common pullback comparison p1* f* N -> p2* f* N.
Source: thm-amb-p1-adjunction.proof.md, equality of the two maps to the base
(blueprint: def-sfb-etale-coordinate-trace-data). -/
def coordinate {X Y : Scheme.{u}} (f : X ⟶ Y) (N : DerivedCategoryModule A Y) :
    (pull A (pullback.fst f f)).obj ((pull A f).obj N) ≅
      (pull A (pullback.snd f f)).obj ((pull A f).obj N) :=
  (derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
    (CommSq.mk (pullback.condition (f := f) (g := f)).symm)).app N

/-- Ordered projection with the outside coefficient first, conjugated by the actual symmetries.
Source: thm-amb-p1-adjunction.proof.md, projection formula in both coordinates
(blueprint: def-sfb-etale-coordinate-trace-data). -/
def orderedProjectionIso [Finite A] {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (K : DerivedCategoryModule A Y) (E : DerivedCategoryModule A X) :
    tensor A Y K ((push A f).obj E) ≅
      (push A f).obj (tensor A X ((pull A f).obj K) E) :=
  have := isIso_rightDerivedLowerStarProjectionMap_app_app_of_isProper_of_isAddTorsion
    A isAddTorsion_of_finite f E K
  swap A Y K ((push A f).obj E) ≪≫
    asIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app E).app K) ≪≫
      (push A f).mapIso (swap A X E ((pull A f).obj K))

/-- The specified proper exchange for the second projection, from the existing mate.
Source: thm-amb-p1-adjunction.proof.md, first triangle, proper base change
(blueprint: def-sfb-etale-coordinate-trace-data). -/
def exchange2 [Finite A] {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (M : DerivedCategoryModule A X) :
    (pull A f).obj ((push A f).obj M) ≅
      (push A (pullback.snd f f)).obj ((pull A (pullback.fst f f)).obj M) :=
  have := isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring
    A isAddTorsion_of_finite (IsPullback.of_hasPullback f f)
  asIso ((derivedBaseChangeMap (ModuleCat.{u + 1} A)
    (IsPullback.of_hasPullback f f).toCommSq).app M)

/-- The specified proper exchange for the first projection, with the square flipped.
Source: thm-amb-p1-adjunction.proof.md, first-coordinate integration
(blueprint: def-sfb-etale-coordinate-trace-data). -/
def exchange1 [Finite A] {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (M : DerivedCategoryModule A X) :
    (pull A f).obj ((push A f).obj M) ≅
      (push A (pullback.fst f f)).obj ((pull A (pullback.snd f f)).obj M) :=
  have := isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring
    A isAddTorsion_of_finite (IsPullback.of_hasPullback f f).flip
  asIso ((derivedBaseChangeMap (ModuleCat.{u + 1} A)
    (IsPullback.of_hasPullback f f).flip.toCommSq).app M)

/-- H(K) = f* K tensor f* L, as an actual functor, so H(e) has its specified meaning.
Source: thm-amb-p1-adjunction.proof.md, proposed right adjoint
(blueprint: def-sfb-etale-coordinate-trace-data). -/
def H {X Y : Scheme.{u}} (f : X ⟶ Y) (L : DerivedCategoryModule A Y) :
    DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X :=
  pull A f ⋙ derivedTensorRight (ModuleCat.{u + 1} A) X ((pull A f).obj L)

/-- Inverse ordered projection followed by tensoring the given trace and the right unitor.
Source: thm-amb-p1-adjunction.proof.md, the displayed counit
(blueprint: def-sfb-etale-coordinate-trace-data). -/
def evaluation [Finite A] {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (L : DerivedCategoryModule A Y)
    (t : (push A f).obj ((pull A f).obj L) ⟶ constantComplex A Y)
    (K : DerivedCategoryModule A Y) : (push A f).obj ((H A f L).obj K) ⟶ K :=
  (orderedProjectionIso A f K ((pull A f).obj L)).inv ≫
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj K).map t ≫
      (derivedTensorRightUnitor (ModuleCat.{u + 1} A) Y K).hom

/-- Inverse projection for p2, then inverse proper exchange tensor the identity.
This is precisely C_M; L_W is represented by p2* f* L.
Source: thm-amb-p1-adjunction.proof.md, the last arrow defining the unit
(blueprint: def-sfb-etale-coordinate-trace-data). -/
def comparison [Finite A] {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (L : DerivedCategoryModule A Y) (M : DerivedCategoryModule A X) :
    (push A (pullback.snd f f)).obj
      (tensor A (pullback f f) ((pull A (pullback.fst f f)).obj M)
        ((pull A (pullback.snd f f)).obj ((pull A f).obj L))) ≅
      (H A f L).obj ((push A f).obj M) :=
  have := isIso_rightDerivedLowerStarProjectionMap_app_app_of_isProper_of_isAddTorsion
    A isAddTorsion_of_finite (pullback.snd f f)
      ((pull A (pullback.fst f f)).obj M) ((pull A f).obj L)
  (asIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A)
    (pullback.snd f f)).app ((pull A (pullback.fst f f)).obj M)).app
      ((pull A f).obj L))).symm ≪≫
    ((derivedTensor (ModuleCat.{u + 1} A) X).mapIso (exchange2 A f M).symm).app
      ((pull A f).obj L)

/-- FRp2* -> FRp1*, via the normalized direct-image compositors and fp1=fp2.
Source: thm-amb-p1-adjunction.proof.md, coordinate interchange in the first triangle
(blueprint: def-sfb-etale-coordinate-trace-data). -/
def directComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    push A (pullback.snd f f) ⋙ push A f ≅ push A (pullback.fst f f) ⋙ push A f :=
  rightDerivedLowerStarComp (ModuleCat.{u + 1} A) (pullback.snd f f) f ≪≫
    eqToIso (congrArg (push A) (pullback.condition (f := f) (g := f)).symm) ≪≫
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) (pullback.fst f f) f).symm

/-- Identify p1* HK and p2* HK by the tensor and common-base pullback comparisons.
Source: thm-amb-p1-adjunction.proof.md, extracting the common coefficient
(blueprint: def-sfb-etale-coordinate-trace-data). -/
def coordinateH {X Y : Scheme.{u}} (f : X ⟶ Y) (L K : DerivedCategoryModule A Y) :
    (pull A (pullback.fst f f)).obj ((H A f L).obj K) ≅
      (pull A (pullback.snd f f)).obj ((H A f L).obj K) :=
  (pull A (pullback.fst f f)).mapIso
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) f K L).symm ≪≫
    coordinate A f (tensor A Y K L) ≪≫
      (pull A (pullback.snd f f)).mapIso
        (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) f K L)

/-- The given sheaf line placed in degree zero and shifted by the specified even integer.
Source: thm-amb-p1-adjunction.proof.md, the even shifted coefficient
(blueprint: def-sfb-etale-coordinate-trace-data). -/
abbrev shiftedLine {Y : Scheme.{u}}
    (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) (d : ℤ) :
    DerivedCategoryModule A Y :=
  ((_root_.DerivedCategory.singleFunctor _ 0).obj J)⟦(2 * d : ℤ)⟧
```

The old unused public import of `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`
is removed. Its theorem is still a proof dependency of the new transport lemmas.
All other public imports of the original module are publicly imported by the data module.

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.EtaleCoordinateTraceContractions`
reported zero current Lean module importers. The DAG's unfinished parents still need the
contraction theorem, which remains present with its original signature. No existing consumer
needs adaptation. The following new modules use the extracted definitions:

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleCoordinateTraceContractions | G5 | Re-export data; prove theorem from step lemmas. |
| Sheaf.AlgebraicGeometry.EtaleCoordinateKunnethFactorization | new, G5 | Import canonical data for its statement. |
| Sheaf.AlgebraicGeometry.EtaleProjectionTraceNormalization | new, G5 | Import canonical data for its statement. |
| Sheaf.AlgebraicGeometry.EtaleEvenLineSelfSymmetry | new, G5 | Import canonical data for its statement. |
| Sheaf.AlgebraicGeometry.EtaleSecondCoordinateContraction | new, G5 | Import canonical data for its statement. |

## Status

landed 20261025T123006-L-1822645 2026-10-25 (merge of deliver/G5/Sheaf.AlgebraicGeometry.EtaleCoordinateTraceContractions)
