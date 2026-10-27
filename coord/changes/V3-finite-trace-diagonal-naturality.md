# Canonical maps reexported by Sheaf.Paper.FiniteTraceDiagonalDatum

## Reason

The two lower canonical-naturality statements must be independently importable
by the datum module. Keeping their generic canonical data in the datum would
create an import cycle. Extract exactly that existing data into
`Sheaf.Paper.FiniteTraceDiagonalCanonicalMaps`, and publicly import it from the
item. Every old declaration name, signature, body and attribute is preserved;
only the blueprint identifiers in its docstrings now point to the extraction
node. No definition is replaced by unknown data, and no map is changed.

All original public imports of the item stay. The new public import reexports
all moved names, so any existing client retains the same API. No source-library
file is changed. The two new proof imports contain strictly smaller canonical
contraction and exchange naturality statements; the unit proof combines them
with tensor naturality for the actual diagonal class.

## Old

In `lean/Sheaf/Paper/FiniteTraceDiagonalDatum.lean`:

```lean
/-- Properness of the existing diagonal with its explicit fibre-product codomain.
Source: blueprint def-pur-td-datum, separated f (blueprint: def-pur-td-datum). -/
instance normalizedDiagonalProper {S T : Scheme.{u}} (h : S ⟶ T) [IsSeparated h] :
    IsProper (Etale.TraceDiagonalDatum.diagonal h) :=
  inferInstanceAs (IsProper (pullback.diagonal h))

section GenericTensor

variable (C : Type v) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]

/-- The coefficient unit, with the same monoidal term as the published tensor.
Source: blueprint def-pur-td-datum, Lambda_T (blueprint: def-pur-td-datum). -/
def coefficientUnit (T : Scheme.{u}) :
    _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) C) := 𝟙_ _

/-- The canonical signed symmetry: descend the Koszul braiding of cochain complexes.
It is constructed by the localization universal property, with no Nonempty choice.
Source: blueprint def-pur-td-datum, signed tensor symmetry
(blueprint: def-pur-td-datum). -/
def signedSymmetry (T : Scheme.{u}) : derivedTensor C T ≅ (derivedTensor C T).flip :=
  letI := _root_.DerivedCategory.braidedCategory' (Sheaf (Scheme.ProEt.topology T) C)
  BraidedCategory.curriedBraidingNatIso _

/-- Multiplication by the coefficient unit on a K-flat representative, localized.
Source: blueprint def-pur-td-datum, unit constraint (blueprint: def-pur-td-datum). -/
def unitLeft (T : Scheme.{u}) :
    (derivedTensor C T).obj (coefficientUnit C T) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun K ↦ λ_ K) (fun h ↦ leftUnitor_naturality h)

/-- The right multiplication unit constraint, localized from cochain representatives.
Source: blueprint def-pur-td-datum, counit (blueprint: def-pur-td-datum). -/
def unitRight (T : Scheme.{u}) (K :
    _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) C)) :
    ((derivedTensor C T).obj K).obj (coefficientUnit C T) ≅ K := ρ_ K

end GenericTensor

/-- An abbreviation for the native derived tensor.
Source: blueprint def-pur-td-datum, tensor (blueprint: def-pur-td-datum). -/
abbrev tensorFor (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :=
  derivedTensor (ModuleCat.{u + 1} A) T

/-- An abbreviation for the native derived pullback.
Source: blueprint def-pur-td-datum, pullback (blueprint: def-pur-td-datum). -/
abbrev pullFor (A : Type (u + 1)) [CommRing A] {S T : Scheme.{u}} (h : S ⟶ T) :
    _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) ⥤
      _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A)) :=
  (upperStar (ModuleCat.{u + 1} A) h).leftDerivedFunctor

/-- An abbreviation for the published compact-support functor.
Source: blueprint def-pur-td-datum, Rf!
(blueprint: def-pur-td-datum). -/
abbrev compactSupportFor (A : Type (u + 1)) [CommRing A]
    {S T : Scheme.{u}} {h : S ⟶ T} (c : Compactification h) :
    _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A)) ⥤
      _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) :=
  rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c

section CompactSection

variable (A : Type (u + 1)) [CommRing A] [Finite A]
  {S T : Scheme.{u}} {h : S ⟶ T} [QuasiCompact h]

/-- The canonical change of compactification, descended by full faithfulness from
bounded-below etale models. Source: blueprint def-pur-td-datum, composition convention
(blueprint: def-pur-td-datum). -/
def originChange (c d : Compactification h) :
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) S).ι ⋙
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) S).ι ⋙
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d :=
  let Φ := comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) S
  (Φ.asEquivalence.congrLeft.fullyFaithfulInverse).preimageIso
    (rightDerivedLowerShriekOfCompactificationOriginIso A c d)

/-- Compact-support composition for a section, with the canonical identity normalization.
The last comparison uses the published identity compositor, which is normalized by the
trivial compactification. Source: blueprint def-pur-td-datum, first unit isomorphism
(blueprint: def-pur-td-datum). -/
def compactSection (c : Compactification h) {k : T ⟶ S} [QuasiCompact k]
    (d : Compactification k) (hk : h ≫ k = 𝟙 S)
    (K : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) S).FullSubcategory) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).obj
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K.obj) ≅
        K.obj :=
  letI := c.hasCompactification
  letI := d.hasCompactification
  letI : HasCompactification (h ≫ k) := HasCompactification.of_eq hk.symm
  let C := ModuleCat.{u + 1} A
  let K' : (DerivedCategory.plusEtaleOrigin C T).FullSubcategory :=
    ⟨(rightDerivedLowerShriek C h).obj K.obj,
      K.property.rightDerivedLowerShriek_obj h⟩
  (rightDerivedLowerShriekOfCompactification C d).mapIso
      ((originChange A c (HasCompactification.compactification h)).app K) ≪≫
    (originChange A d (HasCompactification.compactification k)).app K' ≪≫
    (originCompositionAmbient A h k).app K ≪≫
    (DerivedCategory.plusEtaleOrigin C S).ι.mapIso
      ((originCompactSupportCongr A (h ≫ k) hk ≪≫ originCompactSupportId A S).app K)

end CompactSection

section GenericDiagonal

variable (A : Type (u + 1)) [CommRing A] [Finite A]

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [QuasiCompact f]

/-- The published projection transformation, inverted on finite-Tor inputs.
Source: blueprint def-pur-td-datum, projection comparisons
(blueprint: def-pur-td-datum). -/
def projectionCore (c : Compactification f)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)))
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X K)
    (hL : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) Y L) :
    ((tensorFor A Y).obj ((compactSupportFor A c).obj K)).obj L ≅
      (compactSupportFor A c).obj (((tensorFor A X).obj K).obj ((pullFor A f).obj L)) :=
  letI : IsIso (((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app K).app L) :=
    hasProjectionFormulaOfCompactification_of_constructibleFiniteTor A c hK hL
  asIso (((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app K).app L)

/-- The section comparison for pullback, over an abstract coefficient ring.
Source: blueprint def-pur-td-datum, p1 Delta = id (blueprint: def-pur-td-datum). -/
def diagonalPullbackCore : pullFor A (pullback.fst f f) ⋙
    pullFor A (Etale.TraceDiagonalDatum.diagonal f) ≅
      𝟭 (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :=
  (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (Etale.TraceDiagonalDatum.diagonal f)
    (pullback.fst f f)).symm ≪≫
    leftDerivedUpperStarCongr (ModuleCat.{u + 1} A) (Etale.TraceDiagonalDatum.diagonal_fst f) ≪≫
    leftDerivedUpperStarId (ModuleCat.{u + 1} A) X

/-- The canonical diagonal contraction over a general finite coefficient ring.
Its hypotheses are precisely the typing conditions supplied by diagonal_inputs.
Source: blueprint def-pur-td-datum, first unit isomorphism (blueprint: def-pur-td-datum). -/
def contractionCore (c : Compactification f) (K : (_root_.DerivedCategory (Sheaf
  (Scheme.ProEt.topology (X)) (ModuleCat.{u + 1} A))))
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X K)
    (hU : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X (coefficientUnit
      (ModuleCat.{u + 1} A) (X)))
    (hP : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) (pullback f f)
      (((pullFor A (pullback.fst f f))).obj K)) :
    ((compactSupportFor A (c.ofIsPullback
      (IsPullback.of_hasPullback f f)))).obj
      ((((tensorFor A (pullback f f))).obj (((pullFor A (pullback.fst f f))).obj K)).obj
        (((compactSupportFor A
          (HasCompactification.compactification (Etale.TraceDiagonalDatum.diagonal f)))).obj
            (coefficientUnit
          (ModuleCat.{u + 1} A) (X)))) ≅ K :=
  let δ := Etale.TraceDiagonalDatum.diagonal f
  let cδ := HasCompactification.compactification δ
  let S₂ := compactSupportFor A (c.ofIsPullback (IsPullback.of_hasPullback f f))
  let Sδ := compactSupportFor A cδ
  let T := (pullFor A (pullback.fst f f)).obj K
  let U := coefficientUnit (ModuleCat.{u + 1} A) X
  let Q := (pullFor A δ).obj T
  let e₁ : ((tensorFor A (pullback f f)).obj T).obj (Sδ.obj U) ≅
      ((tensorFor A (pullback f f)).obj (Sδ.obj U)).obj T :=
    ((signedSymmetry (ModuleCat.{u + 1} A) (pullback f f)).app T).app (Sδ.obj U)
  let e₂ : ((tensorFor A (pullback f f)).obj (Sδ.obj U)).obj T ≅
      Sδ.obj (((tensorFor A X).obj U).obj Q) :=
    projectionCore A δ cδ U T hU hP
  let e₃ : ((tensorFor A X).obj U).obj Q ≅ Q :=
    (unitLeft (ModuleCat.{u + 1} A) X).app Q
  let e₄ : Q ≅ K := (diagonalPullbackCore A f).app K
  let e₅ : S₂.obj (Sδ.obj K) ≅ K :=
    compactSection A cδ (c.ofIsPullback (IsPullback.of_hasPullback f f))
      (Etale.TraceDiagonalDatum.diagonal_snd f) ⟨K, hK⟩
  S₂.mapIso (e₁ ≪≫ e₂ ≪≫ Sδ.mapIso (e₃ ≪≫ e₄)) ≪≫ e₅

/-- The existing self-square exchange map, inverted on its finite-Tor domain.
Source: blueprint def-pur-td-datum, self-square exchange
(blueprint: def-pur-td-datum). -/
def selfExchangeCore (c : Compactification f)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X K) :
    (pullFor A f).obj ((compactSupportFor A c).obj K) ≅
      (compactSupportFor A (c.ofIsPullback (IsPullback.of_hasPullback f f))).obj
        ((pullFor A (pullback.fst f f)).obj K) :=
  letI := isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_app
    A (IsPullback.of_hasPullback f f) c K hK.plusEtaleOrigin
  asIso ((rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} A)
    (IsPullback.of_hasPullback f f) c).app K)

/-- The canonical inverse-projection/inverse-exchange comparison over a finite ring.
Source: blueprint def-pur-td-datum, final unit isomorphism (blueprint: def-pur-td-datum). -/
def exchangeCore (c : Compactification f) (K L : (_root_.DerivedCategory (Sheaf
  (Scheme.ProEt.topology (X)) (ModuleCat.{u + 1} A))))
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X K)
    (hL : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X L)
    (hP : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) (pullback f f)
      (((pullFor A (pullback.fst f f))).obj K)) :
    ((compactSupportFor A (c.ofIsPullback
      (IsPullback.of_hasPullback f f)))).obj
      ((((tensorFor A (pullback f f))).obj (((pullFor A (pullback.fst f f))).obj K)).obj
        (((pullFor A (pullback.snd f f))).obj L)) ≅
      ((((tensorFor A X).obj ((pullFor A f).obj ((compactSupportFor A c).obj K))).obj L)) :=
  let c₂ := c.ofIsPullback (IsPullback.of_hasPullback f f)
  (projectionCore A (pullback.snd f f) c₂
    ((pullFor A (pullback.fst f f)).obj K) L hP hL).symm ≪≫
    ((tensorFor A X).flip.obj L).mapIso (selfExchangeCore A f c K hK).symm

end GenericDiagonal
```

## New

The item publicly imports `Sheaf.Paper.FiniteTraceDiagonalCanonicalMaps`.
The same declarations in that new module are:

```lean
/-- Properness of the existing diagonal with its explicit fibre-product codomain.
Source: blueprint def-pur-td-datum, separated f
(blueprint: def-pur-finite-trace-canonical-maps). -/
instance normalizedDiagonalProper {S T : Scheme.{u}} (h : S ⟶ T) [IsSeparated h] :
    IsProper (Etale.TraceDiagonalDatum.diagonal h) :=
  inferInstanceAs (IsProper (pullback.diagonal h))

section GenericTensor

variable (C : Type v) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]

/-- The coefficient unit, with the same monoidal term as the published tensor.
Source: blueprint def-pur-td-datum, Lambda_T
(blueprint: def-pur-finite-trace-canonical-maps). -/
def coefficientUnit (T : Scheme.{u}) :
    _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) C) := 𝟙_ _

/-- The canonical signed symmetry: descend the Koszul braiding of cochain complexes.
It is constructed by the localization universal property, with no Nonempty choice.
Source: blueprint def-pur-td-datum, signed tensor symmetry
(blueprint: def-pur-finite-trace-canonical-maps). -/
def signedSymmetry (T : Scheme.{u}) : derivedTensor C T ≅ (derivedTensor C T).flip :=
  letI := _root_.DerivedCategory.braidedCategory' (Sheaf (Scheme.ProEt.topology T) C)
  BraidedCategory.curriedBraidingNatIso _

/-- Multiplication by the coefficient unit on a K-flat representative, localized.
Source: blueprint def-pur-td-datum, unit constraint
(blueprint: def-pur-finite-trace-canonical-maps). -/
def unitLeft (T : Scheme.{u}) :
    (derivedTensor C T).obj (coefficientUnit C T) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun K ↦ λ_ K) (fun h ↦ leftUnitor_naturality h)

/-- The right multiplication unit constraint, localized from cochain representatives.
Source: blueprint def-pur-td-datum, counit
(blueprint: def-pur-finite-trace-canonical-maps). -/
def unitRight (T : Scheme.{u}) (K :
    _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) C)) :
    ((derivedTensor C T).obj K).obj (coefficientUnit C T) ≅ K := ρ_ K

end GenericTensor

/-- An abbreviation for the native derived tensor.
Source: blueprint def-pur-td-datum, tensor
(blueprint: def-pur-finite-trace-canonical-maps). -/
abbrev tensorFor (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :=
  derivedTensor (ModuleCat.{u + 1} A) T

/-- An abbreviation for the native derived pullback.
Source: blueprint def-pur-td-datum, pullback
(blueprint: def-pur-finite-trace-canonical-maps). -/
abbrev pullFor (A : Type (u + 1)) [CommRing A] {S T : Scheme.{u}} (h : S ⟶ T) :
    _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) ⥤
      _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A)) :=
  (upperStar (ModuleCat.{u + 1} A) h).leftDerivedFunctor

/-- An abbreviation for the published compact-support functor.
Source: blueprint def-pur-td-datum, Rf!
(blueprint: def-pur-finite-trace-canonical-maps). -/
abbrev compactSupportFor (A : Type (u + 1)) [CommRing A]
    {S T : Scheme.{u}} {h : S ⟶ T} (c : Compactification h) :
    _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A)) ⥤
      _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) :=
  rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c

section CompactSection

variable (A : Type (u + 1)) [CommRing A] [Finite A]
  {S T : Scheme.{u}} {h : S ⟶ T} [QuasiCompact h]

/-- The canonical change of compactification, descended by full faithfulness from
bounded-below etale models. Source: blueprint def-pur-td-datum, composition convention
(blueprint: def-pur-finite-trace-canonical-maps). -/
def originChange (c d : Compactification h) :
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) S).ι ⋙
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) S).ι ⋙
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d :=
  let Φ := comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) S
  (Φ.asEquivalence.congrLeft.fullyFaithfulInverse).preimageIso
    (rightDerivedLowerShriekOfCompactificationOriginIso A c d)

/-- Compact-support composition for a section, with the canonical identity normalization.
The last comparison uses the published identity compositor, which is normalized by the
trivial compactification. Source: blueprint def-pur-td-datum, first unit isomorphism
(blueprint: def-pur-finite-trace-canonical-maps). -/
def compactSection (c : Compactification h) {k : T ⟶ S} [QuasiCompact k]
    (d : Compactification k) (hk : h ≫ k = 𝟙 S)
    (K : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) S).FullSubcategory) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).obj
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K.obj) ≅
        K.obj :=
  letI := c.hasCompactification
  letI := d.hasCompactification
  letI : HasCompactification (h ≫ k) := HasCompactification.of_eq hk.symm
  let C := ModuleCat.{u + 1} A
  let K' : (DerivedCategory.plusEtaleOrigin C T).FullSubcategory :=
    ⟨(rightDerivedLowerShriek C h).obj K.obj,
      K.property.rightDerivedLowerShriek_obj h⟩
  (rightDerivedLowerShriekOfCompactification C d).mapIso
      ((originChange A c (HasCompactification.compactification h)).app K) ≪≫
    (originChange A d (HasCompactification.compactification k)).app K' ≪≫
    (originCompositionAmbient A h k).app K ≪≫
    (DerivedCategory.plusEtaleOrigin C S).ι.mapIso
      ((originCompactSupportCongr A (h ≫ k) hk ≪≫ originCompactSupportId A S).app K)

end CompactSection

section GenericDiagonal

variable (A : Type (u + 1)) [CommRing A] [Finite A]

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [QuasiCompact f]

/-- The published projection transformation, inverted on finite-Tor inputs.
Source: blueprint def-pur-td-datum, projection comparisons
(blueprint: def-pur-finite-trace-canonical-maps). -/
def projectionCore (c : Compactification f)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)))
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X K)
    (hL : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) Y L) :
    ((tensorFor A Y).obj ((compactSupportFor A c).obj K)).obj L ≅
      (compactSupportFor A c).obj (((tensorFor A X).obj K).obj ((pullFor A f).obj L)) :=
  letI : IsIso (((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app K).app L) :=
    hasProjectionFormulaOfCompactification_of_constructibleFiniteTor A c hK hL
  asIso (((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app K).app L)

/-- The section comparison for pullback, over an abstract coefficient ring.
Source: blueprint def-pur-td-datum, p1 Delta = id
(blueprint: def-pur-finite-trace-canonical-maps). -/
def diagonalPullbackCore : pullFor A (pullback.fst f f) ⋙
    pullFor A (Etale.TraceDiagonalDatum.diagonal f) ≅
      𝟭 (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :=
  (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (Etale.TraceDiagonalDatum.diagonal f)
    (pullback.fst f f)).symm ≪≫
    leftDerivedUpperStarCongr (ModuleCat.{u + 1} A) (Etale.TraceDiagonalDatum.diagonal_fst f) ≪≫
    leftDerivedUpperStarId (ModuleCat.{u + 1} A) X

/-- The canonical diagonal contraction over a general finite coefficient ring.
Its hypotheses are precisely the typing conditions supplied by diagonal_inputs.
Source: blueprint def-pur-td-datum, first unit isomorphism
(blueprint: def-pur-finite-trace-canonical-maps). -/
def contractionCore (c : Compactification f) (K : (_root_.DerivedCategory (Sheaf
  (Scheme.ProEt.topology (X)) (ModuleCat.{u + 1} A))))
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X K)
    (hU : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X (coefficientUnit
      (ModuleCat.{u + 1} A) (X)))
    (hP : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) (pullback f f)
      (((pullFor A (pullback.fst f f))).obj K)) :
    ((compactSupportFor A (c.ofIsPullback
      (IsPullback.of_hasPullback f f)))).obj
      ((((tensorFor A (pullback f f))).obj (((pullFor A (pullback.fst f f))).obj K)).obj
        (((compactSupportFor A
          (HasCompactification.compactification (Etale.TraceDiagonalDatum.diagonal f)))).obj
            (coefficientUnit
          (ModuleCat.{u + 1} A) (X)))) ≅ K :=
  let δ := Etale.TraceDiagonalDatum.diagonal f
  let cδ := HasCompactification.compactification δ
  let S₂ := compactSupportFor A (c.ofIsPullback (IsPullback.of_hasPullback f f))
  let Sδ := compactSupportFor A cδ
  let T := (pullFor A (pullback.fst f f)).obj K
  let U := coefficientUnit (ModuleCat.{u + 1} A) X
  let Q := (pullFor A δ).obj T
  let e₁ : ((tensorFor A (pullback f f)).obj T).obj (Sδ.obj U) ≅
      ((tensorFor A (pullback f f)).obj (Sδ.obj U)).obj T :=
    ((signedSymmetry (ModuleCat.{u + 1} A) (pullback f f)).app T).app (Sδ.obj U)
  let e₂ : ((tensorFor A (pullback f f)).obj (Sδ.obj U)).obj T ≅
      Sδ.obj (((tensorFor A X).obj U).obj Q) :=
    projectionCore A δ cδ U T hU hP
  let e₃ : ((tensorFor A X).obj U).obj Q ≅ Q :=
    (unitLeft (ModuleCat.{u + 1} A) X).app Q
  let e₄ : Q ≅ K := (diagonalPullbackCore A f).app K
  let e₅ : S₂.obj (Sδ.obj K) ≅ K :=
    compactSection A cδ (c.ofIsPullback (IsPullback.of_hasPullback f f))
      (Etale.TraceDiagonalDatum.diagonal_snd f) ⟨K, hK⟩
  S₂.mapIso (e₁ ≪≫ e₂ ≪≫ Sδ.mapIso (e₃ ≪≫ e₄)) ≪≫ e₅

/-- The existing self-square exchange map, inverted on its finite-Tor domain.
Source: blueprint def-pur-td-datum, self-square exchange
(blueprint: def-pur-finite-trace-canonical-maps). -/
def selfExchangeCore (c : Compactification f)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X K) :
    (pullFor A f).obj ((compactSupportFor A c).obj K) ≅
      (compactSupportFor A (c.ofIsPullback (IsPullback.of_hasPullback f f))).obj
        ((pullFor A (pullback.fst f f)).obj K) :=
  letI := isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_app
    A (IsPullback.of_hasPullback f f) c K hK.plusEtaleOrigin
  asIso ((rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} A)
    (IsPullback.of_hasPullback f f) c).app K)

/-- The canonical inverse-projection/inverse-exchange comparison over a finite ring.
Source: blueprint def-pur-td-datum, final unit isomorphism
(blueprint: def-pur-finite-trace-canonical-maps). -/
def exchangeCore (c : Compactification f) (K L : (_root_.DerivedCategory (Sheaf
  (Scheme.ProEt.topology (X)) (ModuleCat.{u + 1} A))))
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X K)
    (hL : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X L)
    (hP : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) (pullback f f)
      (((pullFor A (pullback.fst f f))).obj K)) :
    ((compactSupportFor A (c.ofIsPullback
      (IsPullback.of_hasPullback f f)))).obj
      ((((tensorFor A (pullback f f))).obj (((pullFor A (pullback.fst f f))).obj K)).obj
        (((pullFor A (pullback.snd f f))).obj L)) ≅
      ((((tensorFor A X).obj ((pullFor A f).obj ((compactSupportFor A c).obj K))).obj L)) :=
  let c₂ := c.ofIsPullback (IsPullback.of_hasPullback f f)
  (projectionCore A (pullback.snd f f) c₂
    ((pullFor A (pullback.fst f f)).obj K) L hP hL).symm ≪≫
    ((tensorFor A X).flip.obj L).mapIso (selfExchangeCore A f c K hK).symm

end GenericDiagonal
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteTraceDiagonalDatum | V3 | Reexports the unchanged data and uses its canonical isomorphisms in exactly the original component formulas. |
| Sheaf.Paper.FiniteDiagonalContractionNaturality | new item | States naturality of the first unit isomorphism, without datum arrows or the final exchange. |
| Sheaf.Paper.FiniteDiagonalExchangeNaturality | new item | States naturality of the final unit isomorphism, without datum arrows or contraction. |

`tools/downstream.py` found zero external importers of the original module.
Exact import searches of both the live and quarantined trees still find none.
Thus no existing consumer needs adaptation. The extraction preserves all data
and every target meaning; no target signature is changed and no triangle identity
is assumed. This record is supplied for independent review of the module move.

## Status

landed 20261026T202718-L-3479550 2026-10-26 (merge of deliver/V3/Sheaf.Paper.FiniteTraceDiagonalDatum)
