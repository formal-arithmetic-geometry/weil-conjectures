/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NormalizedUnitTrace.NormalizedUnitTrace
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek

/-!
# Specified coordinates for open unit traces

Source: smooth purity transport Steps 1--3, expanded in open normalization
Steps 1 and 5 (blueprint: def-pur-open-unit-trace-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.NormalizedUnitTrace
open Scheme CondensedRing PurityTransport ExplicitSmoothComparison

local instance bundledRingComm (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell) :
    IsCommMonObj (CommMon.toMon (c.bundled.{u} ell)).X := by
  change IsCommMonObj (c.obj ell)
  infer_instance

local instance bundledPulledRingComm (ell : ℕ) [Fact ell.Prime]
    (c : Coefficient ell) (X : Scheme.{u}) :
    IsCommMonObj (condensedRingObj (CommMon.toMon (c.bundled ell)).X X) := by
  change IsCommMonObj (condensedRingObj (c.obj ell) X)
  infer_instance

/-- The zero-dimensional line with its zero shift is the coefficient unit.
Source: the zero-twist convention
(blueprint: def-pur-open-unit-trace-coordinates). -/
def zeroLine (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell) (X : Scheme.{u}) :
    c.derivedLine ell X 0 ≅ 𝟙_ _ := by
  change ((shiftFunctor _ (0 : ℤ)).obj
    ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ _))) ≅ 𝟙_ _
  exact (shiftFunctorZero _ ℤ).app _ ≪≫
    DerivedCategory.singleFunctorObjUnitIso
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj (c.obj ell) X))

/-- Integer coefficients are on the admissible coefficient list.
Source: standing coefficients (blueprint: def-pur-open-unit-trace-coordinates). -/
abbrev integersAdmissible (ell : ℕ) [Fact ell.Prime] :
    IsLocalizingAdmissibleCoefficient ell ((Coefficient.integers : Coefficient ell).obj ell) :=
  Or.inr (Or.inl ⟨Iso.refl _⟩)

/-- The finite-subextension-valued closure is on the admissible coefficient list.
Source: standing coefficients (blueprint: def-pur-open-unit-trace-coordinates). -/
abbrev closureAdmissible (ell : ℕ) [Fact ell.Prime] :
    IsLocalizingAdmissibleCoefficient ell ((Coefficient.closure : Coefficient ell).obj ell) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩))))

/-- The derived identity direct image, conjugate to the specified identity pullback.
Source: the proper identity factor of the trivial compactification
(blueprint: def-pur-open-unit-trace-coordinates). -/
def identityPush (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell) (Y : Scheme.{u}) :
    (CondensedRing.lowerStar (c.obj ell) (𝟙 Y)).rightDerivedFunctor ≅ 𝟭 _ :=
  conjugateIsoEquiv (CondensedRing.derivedUpperStarLowerStarAdjunction (c.obj ell) (𝟙 Y))
    Adjunction.id (CondensedRing.leftDerivedUpperStarId (c.obj ell) Y).symm

/-- The literal integral-to-closure coefficient map.
Source: the listed composite through Q_ell
(blueprint: def-pur-open-unit-trace-coordinates). -/
def integralClosureMap (ell : ℕ) [Fact ell.Prime] :
    (Coefficient.integers : Coefficient ell).bundled.{u} ell ⟶
      (Coefficient.closure : Coefficient ell).bundled ell :=
  ⟨⟨(Coefficient.closure : Coefficient ell).integralMap ell⟩⟩

/-- The canonical scalar tensor-unit isomorphism, derived from the ordinary
balanced scalar tensorator on K-flat resolutions.
Source: scalar-six monoidal unit (blueprint: def-pur-open-unit-trace-coordinates). -/
def scalarUnitIso (ell : ℕ) [Fact ell.Prime] (X : Scheme.{u}) :
    (scalarSixChange (integralClosureMap ell) X).obj (𝟙_ _) ≅ 𝟙_ _ := by
  let phi := coefficientMap (integralClosureMap ell).hom.hom X
  letI := (Mod.exists_extendScalarsMonoidal phi).choose
  letI := Mod.extendScalars_preservesFlat phi
  letI := (Mod.extendRestrictAdjunction phi).isLeftAdjoint
  letI := (Mod.extendScalars phi).leftDerivedFunctorMonoidal
  exact (Functor.Monoidal.εIso (Mod.extendScalars phi).leftDerivedFunctor).symm

/-- Balanced scalar normalization fixes the zero tensor power to the scalar unit.
Source: the zero-power clause in scalar coefficient compatibility
(blueprint: def-pur-open-unit-trace-coordinates).
Proof: specialize the retained balanced tensor recursion to its zero case. -/
theorem scalarPowerZero_normalized (ell : ℕ) [Fact ell.Prime]
    {c c' : Coefficient ell} (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    (ha : c.integralMap ell ≫ a.hom.hom = c'.integralMap ell) (X : Scheme.{u})
    (p : ScalarLineCoordinates ell a ha X) :
    let phi := coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom X
    letI := (Mod.exists_extendScalarsMonoidal phi).choose
    HEq (p.power 0) (Functor.Monoidal.εIso (Mod.extendScalars phi)).symm := by
  let phi := coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom X
  exact p.power_normalized (Mod.exists_extendScalarsMonoidal phi).choose
    (Mod.exists_extendScalarsMonoidal phi).choose_spec 0

variable (ell : ℕ) [Fact ell.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The chosen-to-trivial compactification comparison evaluated on the unit.
Its common dense refinement normalization fixes the actual map.
Source: open normalization Step 1 (blueprint: def-pur-open-unit-trace-coordinates). -/
def openUnitComparison (c : Coefficient ell)
    (hc : IsLocalizingAdmissibleCoefficient ell (c.obj ell))
    (j : X ⟶ Y) [IsOpenImmersion j.left] :
    (CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj ell)
      (compactificationOverField j)).obj (𝟙_ _) ≅
        (actualOpen (c.obj ell) j.left).obj (𝟙_ _) := by
  letI : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
  letI : LocallyOfFiniteType (Y.left ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType Y.hom)
  letI : QuasiCompact (Y.left ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact Y.hom)
  letI : IsSeparated (Y.left ↘ Spec (.of k)) := inferInstanceAs (IsSeparated Y.hom)
  letI : QuasiCompact (j.left ≫ Y.hom) := by rw [j.w]; infer_instance
  letI : QuasiCompact j.left := QuasiCompact.of_comp j.left Y.hom
  exact (detSfCanonicalCompactificationComparison (c.obj ell) ell hc k j.left
      (compactificationOverField j) (.ofIsOpenImmersion j.left)).app
      ((inclusion ell c X.left).obj ⟨𝟙_ _, smoothTraceUnit_mem ell c X.left⟩) ≪≫
    (identityPush ell c Y.left).app _

/-- The ordinary open counit in chosen compactification coordinates.
Source: open normalization Step 1 (blueprint: def-pur-open-unit-trace-coordinates). -/
def ordinaryUnitTrace (c : Coefficient ell)
    (hc : IsLocalizingAdmissibleCoefficient ell (c.obj ell))
    (j : X ⟶ Y) [IsOpenImmersion j.left] :
    (CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj ell)
      (compactificationOverField j)).obj (𝟙_ _) ⟶ 𝟙_ _ :=
  (openUnitComparison ell c hc j).hom ≫
    (actualOpen (c.obj ell) j.left).map
      (CondensedRing.leftDerivedUpperStarUnitIso (c.obj ell) j.left).inv ≫
    ((CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction
      (c.obj ell) j.left).ofNatIsoRight
        (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
          (c.obj ell) j.left).symm).counit.app (𝟙_ _)

/-- The actual normalized smooth counit with zero-line and zero-shift coordinates
removed, so its domain is exactly Rj_! of the tensor unit.
Source: open normalization Steps 2--4 (blueprint: def-pur-open-unit-trace-coordinates). -/
def unitCounit (b : Family ell k) (c : Coefficient ell)
    (j : X ⟶ Y) [IsOpenImmersion j.left] :
    (CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj ell)
      (compactificationOverField j)).obj (𝟙_ _) ⟶ 𝟙_ _ :=
  (CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj ell)
      (compactificationOverField j)).map (zeroLine ell c X.left).inv ≫
    unitTrace ell b c (datum j 0)

/-- Ordinary scalar transport of a unit trace, in the specified open coordinates.
Every factor is an existing unit, scalar-open mate, or compactification comparison;
this function contains no chosen trace or purity isomorphism.
Source: open normalization Step 5 (blueprint: def-pur-open-unit-trace-coordinates). -/
def transportIntegralOpenTrace (j : X ⟶ Y) [IsOpenImmersion j.left]
    (t : (CondensedRing.rightDerivedLowerShriekOfCompactification
      ((Coefficient.integers : Coefficient ell).obj ell) (compactificationOverField j)).obj
        (𝟙_ _) ⟶ 𝟙_ _) :
    (CondensedRing.rightDerivedLowerShriekOfCompactification
      ((Coefficient.closure : Coefficient ell).obj ell) (compactificationOverField j)).obj
        (𝟙_ _) ⟶ 𝟙_ _ :=
  (openUnitComparison ell .closure (closureAdmissible ell) j).hom ≫
    (actualOpen ((Coefficient.closure : Coefficient ell).obj ell) j.left).map
      (scalarUnitIso ell X.left).inv ≫
    (CondensedRing.derivedOpenImmersionShriekIso
      (integralClosureMap ell).hom.hom j.left).inv.app (𝟙_ _) ≫
    (scalarSixChange (integralClosureMap ell) Y.left).map
      ((openUnitComparison ell .integers (integersAdmissible ell) j).inv ≫ t) ≫
    (scalarUnitIso ell Y.left).hom

/-- The published exceptional open-unit counit, read in the ambient compact-support
coordinates. No smooth orientation occurs in this definition.
Source: open normalization Steps 1 and 6
(blueprint: def-pur-open-unit-trace-coordinates). -/
def boundedOpenUnitTrace (j : X ⟶ Y) [IsOpenImmersion j.left] :
    (CondensedRing.rightDerivedLowerShriekOfCompactification
      ((Coefficient.closure : Coefficient ell).obj ell) (compactificationOverField j)).obj
        (𝟙_ _) ⟶ 𝟙_ _ :=
  (boundedConstructibleLowerShriekOfCompactificationCompatibility ell
      (compactificationOverField j)).inv.app (𝟙_ _) ≫
    ((boundedConstructibleLowerShriek ell j).map
        (boundedConstructibleUpperShriekUnitIso_padicAlgCl ell j).inv ≫
      (boundedConstructibleUpperShriekAdjunction ell j).counit.app (𝟙_ _)).hom

/-- Recover the zero-dimensional closure trace from its unit coordinates.
Source: cancellation of the zero line comparison
(blueprint: def-pur-open-unit-trace-coordinates).
Proof: the closure-line equality at zero is reflexive. Cancel the zero-line
isomorphism followed by its inverse under compact support. -/
theorem closureTrace_zero (j : X ⟶ Y) [IsOpenImmersion j.left] :
    closureTrace ell j 0 =
      (CondensedRing.rightDerivedLowerShriekOfCompactification
        (Profinite.padicAlgClRingObj ell) (compactificationOverField j)).map
          (zeroLine ell .closure X.left).hom ≫
        unitCounit ell (family ell k) .closure j := by
  let F := CondensedRing.rightDerivedLowerShriekOfCompactification
    (Profinite.padicAlgClRingObj ell) (compactificationOverField j)
  change F.map (𝟙 _) ≫ unitTrace ell (family ell k) .closure (datum j 0) =
    F.map (zeroLine ell .closure X.left).hom ≫
      F.map (zeroLine ell .closure X.left).inv ≫
        unitTrace ell (family ell k) .closure (datum j 0)
  simp only [← F.map_comp_assoc, Iso.hom_inv_id, F.map_id, Category.id_comp]

end AlgebraicGeometry.ProEtale.NormalizedUnitTrace
