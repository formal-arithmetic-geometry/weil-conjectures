/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedSixOperations
public import WeilConjectures.AlgebraicGeometry.CondensedCoefficientPoint
public import WeilConjectures.DeligneLaumon.CondensedCoefficientUnit
public import WeilConjectures.DeligneLaumon.CondensedFieldSmoothDuality
public import WeilConjectures.AlgebraicGeometry.InternalSignedTateTwist
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients

/-!
# Compatibility of condensed orientation families under coefficient extension

Source: `literature/blueprint/latest/blueprint/sec-six-functors/sk-def-sf-orientation/
def-sf-orientation.md`, Change of coefficients, the comparison square; specialized to
finite coefficient-field inclusions as in `sk-def-sf-orientation/_section.md`.
(blueprint: def-sf-orientation-stage-compatibility)

The coefficient objects and derived categories below are the ordinary (unbounded)
module derived categories on the small pro-étale site.  The Tate lines and exceptional
objects are the recorded constructions from the coefficient and six-operations modules.
This interface records the square they must satisfy and makes no existence assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace WeilConjectures

/-- The finite coefficient-field index used by the stage system.
Source: coefficient setting of `def-sf-orientation.md`
(blueprint: def-sf-orientation-stage-compatibility). -/
abbrev sfStageField (ℓ : ℕ) [Fact ℓ.Prime] :=
  PadicAlgCl.FiniteIntermediateField ℓ

/-- The condensed ring attached to a finite coefficient field.
Source: coefficient setting of `def-sf-orientation.md`
(blueprint: def-sf-orientation-stage-compatibility). -/
abbrev sfStageRing (ℓ : ℕ) [Fact ℓ.Prime]
    (E : sfStageField ℓ) : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  Profinite.continuousMapRingObj E.1

/-- Schemes over the fixed algebraic closure of the finite base field.
Source: coefficient setting of `def-sf-orientation.md`
(blueprint: def-sf-orientation-stage-compatibility). -/
abbrev sfStageScheme (D : FiniteFieldDatum.{u}) :=
  Over (Spec (CommRingCat.of D.k))

/-- The ordinary unbounded module derived category on a small pro-étale site.
Source: coefficient setting of `def-sf-orientation.md`
(blueprint: def-sf-orientation-stage-compatibility). -/
abbrev sfStageDerived (D : FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : sfStageField ℓ) (X : sfStageScheme D) :=
  DerivedCategory
    (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (sfStageRing ℓ E) X.left))

/-- The actual derived extension of scalars `E_X ⟶ L_X`, namely
`L_X ⊗ᴸ_{E_X} -`.
Source: coefficient-change paragraph of `def-sf-orientation.md`
(blueprint: def-sf-orientation-stage-compatibility). -/
noncomputable abbrev sfStageExtension {D : FiniteFieldDatum.{u}} {ℓ : ℕ} [Fact ℓ.Prime]
    {E L : sfStageField ℓ} (h : E ≤ L) (X : sfStageScheme D) :
    sfStageDerived D ℓ E X ⥤ sfStageDerived D ℓ L X :=
  (Mod.extendScalars
      (coefficientMap (Profinite.padicSubfieldRingObjMap ℓ h) X.left)).leftDerivedFunctor

/-- The Tate line `M_X(d)[2d]`, using the recorded rational line and internal signed
twist, with the regular module as the degree-zero unit.
Source: `sk-def-sp-tate-twist` and the Tate-line clause of
`def-sf-orientation.md` (blueprint: def-sf-orientation-stage-compatibility). -/
abbrev sfStageTate (D : FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : sfStageField ℓ) (X : sfStageScheme D) (d : ℤ) : sfStageDerived D ℓ E X :=
  (shiftFunctor _ (2 * d : ℤ)).obj
    (spInternalComplexTwist X.left
      (condensedRingObj (sfStageRing ℓ E) X.left)
      (spRationalTwist X.left ℓ E)
      ((DerivedCategory.singleFunctor _ 0).obj
        (Mod.regular (condensedRingObj (sfStageRing ℓ E) X.left))) d)

/-- The regular coefficient unit bundled in the finite-Tor constructible subcategory.
Its membership is the existing coefficient-unit construction used by the recorded
exceptional inverse image.
Source: `det-def-sf-operations` (blueprint: def-sf-orientation-stage-compatibility). -/
abbrev sfStageUnit (D : FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : sfStageField ℓ) (X : sfStageScheme D)
    [CompactSpace X.left] [QuasiSeparatedSpace X.left] :
    ConstantModelConstructibleFiniteTor (sfStageRing ℓ E) X.left :=
  ⟨𝟙_ (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
        (condensedRingObj (sfStageRing ℓ E) X.left))),
    condensedCoefficientUnit_mem (sfStageRing ℓ E) X.left⟩

/-- The exceptional object `Rf^! M_Y`, obtained by applying the recorded restricted
exceptional inverse image to the regular unit and returning its ambient object.
Source: `det-def-sf-operations` (blueprint: def-sf-orientation-stage-compatibility). -/
abbrev sfStageOmega (D : FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar D.k ≠ ℓ)] (E : sfStageField ℓ)
    {X Y : sfStageScheme D} (f : X ⟶ Y)
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [HasCompactification f.left] : sfStageDerived D ℓ E X :=
  letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  letI : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  letI : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  letI : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  let hE : IsLocalizingAdmissibleCoefficient ℓ (sfStageRing ℓ E) :=
    Or.inr (Or.inr (Or.inr (Or.inl ⟨E, ⟨Iso.refl _⟩⟩)))
  (ctfExceptionalInverseImage (sfStageRing ℓ E) ℓ D.k
      (BaseFieldFiniteCD.of_isAlgClosed ℓ D.k) f hE).obj
    (sfStageUnit D ℓ E Y) |>.obj

/-- The supplied ordinary pro-étale coefficient-stage orientation data.
The Tate and exceptional objects are the canonical constructions above; only the
orientation and coefficient-change isomorphisms are supplied data.
Source: the change-of-coefficients interface in `def-sf-orientation-stage-compatibility`
(blueprint: def-sf-orientation-stage-compatibility). -/
structure SfOrientationStageData (D : FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar D.k ≠ ℓ)] where
  orientation : ∀ (E : sfStageField ℓ) {X Y : sfStageScheme D}
    (f : X ⟶ Y) (d : ℕ)
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    [SmoothOfRelativeDimension d f.left] [HasCompactification f.left],
    sfStageTate D ℓ E X d ≅ sfStageOmega D ℓ E f
  twistChange : ∀ {E L : sfStageField ℓ} (h : E ≤ L)
    (X : sfStageScheme D) (d : ℤ)
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom],
    (sfStageExtension h X).obj (sfStageTate D ℓ E X d) ≅ sfStageTate D ℓ L X d
  exceptionalChange : ∀ {E L : sfStageField ℓ} (h : E ≤ L)
    {X Y : sfStageScheme D} (f : X ⟶ Y)
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    [HasCompactification f.left],
    (sfStageExtension h X).obj (sfStageOmega D ℓ E f) ≅ sfStageOmega D ℓ L f

/-! The final field is the square from the node.  Quantifying over all `h : E ≤ L`
includes `E = L` and the direct inclusion `E ≤ H` in every tower `E ≤ L ≤ H`. -/

/-- Stage compatibility of supplied condensed orientation data.

Source: the comparison square in the change-of-coefficients paragraph of
`def-sf-orientation.md` (blueprint: def-sf-orientation-stage-compatibility).
For every finite coefficient-field inclusion and every smooth separated finite-type map
of pure relative dimension `d`, the derived scalar extension of the `E`-orientation,
followed by the supplied exceptional comparison, equals the supplied Tate comparison
followed by the `L`-orientation.  This is only a predicate on supplied data; it asserts
neither existence of the comparison isomorphisms nor existence or compatibility of the
orientation families. -/
def sfOrientationStageCompatibility {D : FiniteFieldDatum.{u}} {ℓ : ℕ} [Fact ℓ.Prime]
    [Fact (ringChar D.k ≠ ℓ)]
    (S : SfOrientationStageData D ℓ) : Prop :=
  ∀ {E L : sfStageField ℓ} (h : E ≤ L) {X Y : sfStageScheme D}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) (d : ℕ) [IsSeparated f.left] [LocallyOfFiniteType f.left]
    [QuasiCompact f.left] [SmoothOfRelativeDimension d f.left]
    [HasCompactification f.left],
    (sfStageExtension h X).map (S.orientation E f d).hom ≫
        (S.exceptionalChange h f).hom =
      (S.twistChange h X d).hom ≫ (S.orientation L f d).hom

end WeilConjectures
