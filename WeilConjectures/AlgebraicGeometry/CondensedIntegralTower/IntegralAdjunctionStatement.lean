/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedIntegralTower.GeometricTowerStatement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SkPropSfExistence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPull
import Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.AlgebraicGeometry.CondensedIntegralTower.IntegralCoefficientIsomorphism

/-! # Integral tower adjunction and comparison with the Brown exceptional inverse image
Source: latest blueprint sk-prop-sp-integral-adjunction, opening paragraph and proof.
The unit and counit are specified as whole tower morphisms under reduction.
(blueprint: sk-prop-sp-integral-adjunction)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open CategoryTheory.InternalAbelianSheafModule
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedIntegralTower
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

set_option maxHeartbeats 800000 in
-- Check the coefficient topology and continuous finite-subfield transport together.
set_option synthInstance.maxHeartbeats 100000 in
/-- Integral coefficients are admissible for sk-prop-sf-existence. This is the
finite-subfield transport of the continuous integer-ring coefficients. The coefficient
isomorphism is constructed explicitly, with no postponed existence proof.
Source: the coefficient convention of sk-prop-sf-existence
(blueprint: sk-prop-sp-integral-adjunction). -/
abbrev integralAdmissible :
    IsLocalizingAdmissibleCoefficient l (DerivedNakayama.integerRing l E) := by
  obtain ⟨F, hF⟩ := integralCoefficientIso l E
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨F, hF⟩))))

/-- The proper coefficient map is the mate of the actual nonflat tensor/pullback
comparison. No flatness is imposed on the ell-power quotient.
Source: det-sp-integral-direct-image-tower(2), scalar comparison
(blueprint: sk-prop-sp-integral-adjunction). -/
def quotientPush (n : ℕ) {T U : Scheme.{u}} (g : T ⟶ U) :
    (CondensedRing.lowerStar (DerivedNakayama.integerRing l E) g).rightDerivedFunctor ⋙
      finiteReduction l E U n ⟶
    finiteReduction l E T n ⋙ (CondensedRing.lowerStar (finiteRing l E n) g).rightDerivedFunctor :=
  mateEquiv
    (CondensedRing.derivedUpperStarLowerStarAdjunction (DerivedNakayama.integerRing l E) g)
    (CondensedRing.derivedUpperStarLowerStarAdjunction (finiteRing l E n) g)
    (TwoSquare.mk _ _ _ _
      (CondensedRing.derivedUpperStarExtendScalarsIso (quotient l E n) g).inv)

/-- The compactification coefficient map: the proper tensor mate followed by the
unit-normalized open tensor isomorphism, for the actual quotient map.
Source: det-sp-integral-direct-image-tower(2)
(blueprint: sk-prop-sp-integral-adjunction). -/
def supportCoefficientMap {T U : Scheme.{u}} {g : T ⟶ U}
    (c : Compactification g) (n : ℕ) :
    CondensedRing.rightDerivedLowerShriekOfCompactification
      (DerivedNakayama.integerRing l E) c ⋙ finiteReduction l E U n ⟶
    finiteReduction l E T n ⋙
      CondensedRing.rightDerivedLowerShriekOfCompactification (finiteRing l E n) c :=
  (Functor.associator _ _ _).hom ≫
    whiskerLeft
      (CondensedRing.openImmersionLowerShriek (DerivedNakayama.integerRing l E)
        c.i).mapDerivedCategory (quotientPush l E n c.g) ≫
    (Functor.associator _ _ _).inv ≫
    whiskerRight (CondensedRing.derivedOpenImmersionShriekIso (quotient l E n) c.i).hom
      (CondensedRing.lowerStar (finiteRing l E n) c.g).rightDerivedFunctor ≫
    (Functor.associator _ _ _).hom

/-- The reduction Levels in section coordinates, with the section-equivalence counit.
Source: sk-lem-sp-tower (blueprint: sk-prop-sp-integral-adjunction). -/
def sectionLevels (T : Scheme.{u}) (D : Model l E T) (n : ℕ) :
    D.red ⋙ Ev l E T n ≅
      finiteReduction l E T n ⋙ (finiteSections l E T n).functor.mapDerivedCategory :=
  isoWhiskerLeft (D.red ⋙ Ev l E T n)
    (finiteSections l E T n).mapDerivedCategory.counitIso.symm ≪≫
      isoWhiskerRight (D.levels n) (finiteSections l E T n).functor.mapDerivedCategory

/-- The same actual coefficient map in the finite section coordinates.
Source: det-sp-integral-direct-image-tower(2)
(blueprint: sk-prop-sp-integral-adjunction). -/
def sectionSupportCoefficientMap {T U : Scheme.{u}} {g : T ⟶ U}
    (c : Compactification g) (n : ℕ) :
    CondensedRing.rightDerivedLowerShriekOfCompactification
        (DerivedNakayama.integerRing l E) c ⋙ finiteReduction l E U n ⋙
      (finiteSections l E U n).functor.mapDerivedCategory ⟶
    finiteReduction l E T n ⋙ (finiteSections l E T n).functor.mapDerivedCategory ⋙
      finiteSupport l E c n :=
  whiskerRight (supportCoefficientMap l E c n)
      (finiteSections l E U n).functor.mapDerivedCategory ≫
    whiskerLeft (finiteReduction l E T n)
      (isoWhiskerRight (finiteSections l E T n).mapDerivedCategory.unitIso
        (CondensedRing.rightDerivedLowerShriekOfCompactification (finiteRing l E n) c ⋙
          (finiteSections l E U n).functor.mapDerivedCategory)).hom

/-- The actual data retained from the Brown theorem, on Loc(Dctf).
Source: sk-prop-sf-existence (blueprint: sk-prop-sp-integral-adjunction). -/
structure BrownAdjunction {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification.BoundaryCompactification f) where
  closed : ∀ K, localizingClosureProEtale (DerivedNakayama.integerRing l E) X K →
    localizingClosureProEtale (DerivedNakayama.integerRing l E) Y
      ((CondensedRing.rightDerivedLowerShriekOfCompactification
        (DerivedNakayama.integerRing l E) c.obj.obj).obj K)
  right : (localizingClosureProEtale (DerivedNakayama.integerRing l E) Y).FullSubcategory ⥤
    (localizingClosureProEtale (DerivedNakayama.integerRing l E) X).FullSubcategory
  adjunction : CondensedRing.localizingLowerShriek
    (DerivedNakayama.integerRing l E) c.obj.obj closed ⊣ right

variable (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  (hk : Finite k ∨ IsAlgClosed k)
  (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- Finite type over a field gives the Noetherian hypothesis of sk-lem-sp-tower.
Source: standing scheme setting (blueprint: sk-prop-sp-integral-adjunction). -/
abbrev noetherianOverField (T : Scheme.{u}) [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))] :
    IsNoetherian T where
  toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (T ↘ Spec (.of k))
  toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (T ↘ Spec (.of k))

/-- Fix once the boundary compactification over the field, for both constructions.
Source: det-def-sfb-dc-setting (blueprint: sk-prop-sp-integral-adjunction). -/
def chosenCompactification : Compactification.BoundaryCompactification f :=
  letI := noetherianOverField k X
  ⟨⟨fieldCompactification k X Y f, inferInstance⟩⟩

/-- Reduction to constructible towers, obtained from the equivalence theorem.
Source: sk-lem-sp-tower (blueprint: sk-prop-sp-integral-adjunction). -/
def constructibleReduction (T : Scheme.{u}) [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))] :
    Dbc l E T ⥤ CtfTowers l E T :=
  letI := noetherianOverField k T
  ObjectProperty.lift _
    ((constantModelBoundedConstructible (DerivedNakayama.integerRing l E) T).ι ⋙
      (model l E T).red)
    (fun K ↦ ((boundedEquivalence l E T).redClosed K).1)

variable (d : ℕ) [SmoothOfRelativeDimension d f]

/-- The already defined integral compact-support construction, before restriction.
Source: det-sp-integral-direct-image-tower (blueprint: sk-prop-sp-integral-adjunction). -/
abbrev integralSupport : Integral l E X ⥤ Integral l E Y :=
  CondensedRing.rightDerivedLowerShriekOfCompactification (DerivedNakayama.integerRing l E)
    (chosenCompactification k X Y f).obj.obj

/-- Tower-reconstructed exceptional image H = Rlim_X G red_Y, before its closure theorem.
Source: sk-prop-sp-integral-adjunction, opening definition
(blueprint: sk-prop-sp-integral-adjunction). -/
def integralRight : Dbc l E Y ⥤ Integral l E X :=
  constructibleReduction l E k Y ⋙ (geometricAdjunction l E k X Y f d).right ⋙
    (ConstructibleTowers l E X).ι ⋙ (model l E X).rlim

/-- Restrict the actual integral support using only the output preservation proof.
Source: sk-prop-sp-integral-adjunction (blueprint: sk-prop-sp-integral-adjunction). -/
def supportRestriction
    (h : ∀ M : Dbc l E X, constantModelBoundedConstructible
      (DerivedNakayama.integerRing l E) Y ((integralSupport l E k X Y f).obj M.obj)) :
    Dbc l E X ⥤ Dbc l E Y :=
  ObjectProperty.lift _ ((constantModelBoundedConstructible
    (DerivedNakayama.integerRing l E) X).ι ⋙ integralSupport l E k X Y f) h

/-- Restrict H using the theorem's output closure proof.
Source: sk-prop-sp-integral-adjunction (blueprint: sk-prop-sp-integral-adjunction). -/
def rightRestriction
    (h : ∀ K : Dbc l E Y, constantModelBoundedConstructible
      (DerivedNakayama.integerRing l E) X ((integralRight l E k X Y f d).obj K)) :
    Dbc l E Y ⥤ Dbc l E X :=
  ObjectProperty.lift _ (integralRight l E k X Y f d) h

/-- Inclusion of Dbc in Loc(Dctf), after the integral finite-Tor criterion.
Source: lem-integral-ctf-equals-bc (blueprint: sk-prop-sp-integral-adjunction). -/
def localizingInclusion (T : Scheme.{u})
    (h : ∀ K : Dbc l E T, localizingClosureProEtale
      (DerivedNakayama.integerRing l E) T K.obj) :
    Dbc l E T ⥤ (localizingClosureProEtale
      (DerivedNakayama.integerRing l E) T).FullSubcategory :=
  ObjectProperty.lift _
    (constantModelBoundedConstructible (DerivedNakayama.integerRing l E) T).ι h

/-- The actual compact-support functor on the uniformly bounded tower category.
Source: sk-prop-sp-tower-geometric (blueprint: sk-prop-sp-integral-adjunction). -/
def constructibleSupport : CtfTowers l E X ⥤ CtfTowers l E Y :=
  ObjectProperty.lift _
    ((ConstructibleTowers l E X).ι ⋙
      (geometricAdjunction l E k X Y f d).construction.functor l E
        (chosenCompactification k X Y f).obj.obj)
    (geometricAdjunction l E k X Y f d).supportClosed

end AlgebraicGeometry.ProEtale.CondensedIntegralTower
