/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NormalizedKummerGeneratorArrows
/-! Definitions for normalized Kummer stalks.
Source: blueprint latest, relative Kummer calculation, Step 2.
(blueprint: def-pur-relative-kummer-normalized-stalk-data). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

section Geometry
variable (A : Type (u + 1)) [CommRing A] (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
  {k : Type u} [Field k] (hmk : IsUnit (m : k)) {ζ : k} (hζ : IsPrimitiveRoot ζ m)
  {B : Scheme.{u}} (p : B ⟶ Spec (.of k)) (b : Bool)
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ B)

/-- The strict-local family, the actual pullback C_B times_B S.
Source: blueprint Step 2 (blueprint: def-pur-relative-kummer-normalized-stalk-data). -/
abbrev normalizedKummerStrictFamily :=
  pullback (normalizedKummerProjection p b) (Scheme.strictHenselizationStructuralMap s)

/-- Projection v to C_B.
Source: blueprint Step 2 (blueprint: def-pur-relative-kummer-normalized-stalk-data). -/
abbrev normalizedKummerStrictV :=
  pullback.fst (normalizedKummerProjection p b) (Scheme.strictHenselizationStructuralMap s)

/-- Projection h to C.
Source: blueprint Step 2 (blueprint: def-pur-relative-kummer-normalized-stalk-data). -/
abbrev normalizedKummerStrictH :=
  normalizedKummerStrictV p b s ≫ pullback.fst (KummerLine.structureMap k b) p

/-- The strict-local family's k-structure.
Source: blueprint Step 2 (blueprint: def-pur-relative-kummer-normalized-stalk-data). -/
abbrev normalizedKummerStrictStructure :=
  normalizedKummerStrictV p b s ≫ normalizedKummerStructure p b

/-- The canonical pullback h* with its normalized root-line coefficient comparison.
Source: blueprint Step 2 (blueprint: def-pur-relative-kummer-normalized-stalk-data). -/
@[irreducible]
def normalizedKummerH :=
  relativeKummerGlobalPullback A m hm hA (normalizedKummerStrictH p b s)
    (relativeKummerExponentUnit m hmk _ (KummerLine.structureMap k b))
    (relativeKummerExponentUnit m hmk _ (normalizedKummerStrictStructure p b s))

/-- The canonical pullback v* on global cohomology.
Source: blueprint Step 2 (blueprint: def-pur-relative-kummer-normalized-stalk-data). -/
@[irreducible]
def normalizedKummerV :=
  relativeKummerGlobalPullback A m hm hA (normalizedKummerStrictV p b s)
    (relativeKummerExponentUnit m hmk _ (normalizedKummerStructure p b))
    (relativeKummerExponentUnit m hmk _ (normalizedKummerStrictStructure p b s))

/-- The specified strict-local comparison: restriction, exchange and Leray.
Source: Stacks Tag 03Q9 (blueprint: def-pur-relative-kummer-normalized-stalk-data). -/
@[irreducible]
def normalizedKummerTheta :=
  moduleStrictLocalTheta A (normalizedKummerProjection p b) s
    (relativeKummerLinePlus A m hA _) (relativeKummerLinePlus A m hA _)
    (relativeKummerLinePullback A m hm hA (normalizedKummerStrictV p b s)
      (relativeKummerExponentUnit m hmk _ (normalizedKummerStructure p b))
      (relativeKummerExponentUnit m hmk _ (normalizedKummerStrictStructure p b s)))

set_option linter.defProp false in
/-- The specified derived comparison, all edge classes and the unit normalization.
Source: blueprint Step 2 (blueprint: def-pur-relative-kummer-normalized-stalk-data). -/
@[irreducible]
def RelativeKummerNormalizedStalk : Prop :=
  IsIso (normalizedKummerH A m hm hA hmk p b s) ∧
  ∃ Φ : ((Scheme.pointSmallEtale s).sheafFiber
      (A := ModuleCat.{u + 1} A)).mapDerivedCategoryPlus.obj
        (normalizedKummerImage A m hA (normalizedKummerProjection p b)) ≅
        normalizedKummerGlobal A m hA (KummerLine.curve k b),
    Φ.hom ≫ normalizedKummerH A m hm hA hmk p b s =
      normalizedKummerTheta A m hm hA hmk p b s ∧
    (∀ q : ℕ,
      (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
          (normalizedKummerEdgeGerm A m hA (normalizedKummerProjection p b) s) ≫
        (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map Φ.hom ≫
        (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
          (normalizedKummerH A m hm hA hmk p b s) =
        (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
          (normalizedKummerV A m hm hA hmk p b s)) ∧
    normalizedKummerUnitGerm A m hm hA hζ p (normalizedKummerProjection p b)
        (relativeKummerExponentUnit m hmk B p)
        (relativeKummerExponentUnit m hmk _ (normalizedKummerStructure p b)) s ≫ Φ.hom =
      normalizedKummerGlobalSection A m hA _
        (normalizedKummerConstantMap A m hm hA hζ _ (KummerLine.structureMap k b)) ∧
    (match b, Φ with
    | false, _ => True
    | true, Ψ =>
      normalizedKummerGeneratorPlusMap A m hA _
          (relativeKummerExponentUnit m hmk _ (normalizedKummerStructure p true))
          (Units.map (pullback.fst (KummerLine.structureMap k true) p).appTop.hom.toMonoidHom
            (KummerLine.coordinateUnit k)) ≫
        (DerivedCategory.Plus.homologyFunctor _ 1).map
          (normalizedKummerEdgeGerm A m hA (normalizedKummerProjection p true) s) ≫
        (DerivedCategory.Plus.homologyFunctor _ 1).map Ψ.hom =
      normalizedKummerGeneratorPlusMap A m hA _
        (relativeKummerExponentUnit m hmk _ (KummerLine.structureMap k true))
        (KummerLine.coordinateUnit k))

end Geometry
end AlgebraicGeometry.Etale
