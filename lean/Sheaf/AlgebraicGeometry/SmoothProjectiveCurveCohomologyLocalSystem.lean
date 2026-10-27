/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
public import Sheaf.AlgebraicGeometry.PointedEtaleStalk
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
public import WeilConjectures.SixFunctors.Etale.Derived.Point
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
import Sheaf.TraceFormula.ProjectiveBundleProper
import Sheaf.AlgebraicGeometry.SmoothProperFiniteCohomologyLocalSystem
import Sheaf.SixFunctors.ProperBaseChangeModules
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.AlgebraicGeometry.PullbackConstantModule
import Sheaf.AlgebraicGeometry.GeometricPointCanonicalGerm
import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import WeilConjectures.AlgebraicGeometry.Curve.Estimate
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk

/-! # First cohomology of a smooth projective curve family

Source: Stacks Project, Tags 0GLI, 095T and 03RQ
(blueprint: lem-sfb-smooth-projective-curve-cohomology-local-system).

The helpers spell out the degree-one exchange and its geometric-stalk identification.
All coefficients and all arrows retain their module structure. The coefficient lift is
only a universe lift of the prime field.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The constant-coefficient first higher direct image, with its module structure.
Source: Stacks Project, Tag 095T
(blueprint: lem-sfb-smooth-projective-curve-cohomology-local-system). -/
noncomputable def curveFirstCohomology (ell : ℕ) {X T : Scheme.{u}} (f : X ⟶ T) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) :=
  (DerivedCategory.Plus.homologyFunctor _ 1).obj
    ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) f).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((constantSheaf X.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))).obj
            (ModuleCat.of _ (ULift.{u + 1} (ZMod ell))))))

/-- Degree one of the specified derived exchange, followed by the canonical identification
of the inverse image of the constant coefficients. No properness is needed to define it.
Source: Stacks Project, Tag 095T
(blueprint: lem-sfb-smooth-projective-curve-cohomology-local-system). -/
noncomputable def curveFirstBaseChange (ell : ℕ) {X T T' : Scheme.{u}}
    (f : X ⟶ T) (v : T' ⟶ T) :
    (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) v).obj
        (curveFirstCohomology ell f) ⟶
      curveFirstCohomology ell (pullback.snd f v) :=
  let A := ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))
  let F := (constantSheaf X.smallEtaleTopology A).obj
    (ModuleCat.of _ (ULift.{u + 1} (ZMod ell)))
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  (((upperStar A v).mapDerivedCategoryPlusHomologyFunctorIso 1).app
      ((rightDerivedLowerStarPlus A f).obj K)).hom ≫
    (DerivedCategory.Plus.homologyFunctor _ 1).map
      ((derivedBaseChangeMapPlus A (IsPullback.of_hasPullback f v).toCommSq).app K) ≫
    (DerivedCategory.Plus.homologyFunctor _ 1).map
      ((rightDerivedLowerStarPlus A (pullback.snd f v)).map
        ((((upperStar A (pullback.fst f v)).mapDerivedCategoryPlusSingleFunctor 0).app F).hom ≫
          (DerivedCategory.Plus.singleFunctor _ 0).map
            (((constantSheafCompUpperStarIso (ULift.{u + 1} (ZMod ell))
              (pullback.fst f v)).app (ModuleCat.of _ (ULift.{u + 1} (ZMod ell)))).hom)))

/-- The canonical global-sections identification of a point pullback with the geometric
stalk: the identity-point germ followed by inverse-image compatibility of stalks.
Source: Stacks Project, Tags 04JN and 04JQ
(blueprint: lem-sfb-smooth-projective-curve-cohomology-local-system). -/
noncomputable def curvePointPullbackStalkIso (ell : ℕ) {T : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))) :
    (Sheaf.Γ (Spec (.of Ω)).smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))).obj
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) t).obj F) ≅
      pointedEtaleStalk F t :=
  ΓIsoSheafFiberOfIsSepClosed _ ≪≫
    (upperStarCompSheafFiberIso (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))
      t (𝟙 (Spec (.of Ω)))).app F ≪≫
    eqToIso (congrArg (fun s ↦ pointedEtaleStalk F s) (Category.id_comp t))

/-- Over an algebraically closed field, exact global sections commute with first
cohomology of the direct image. Leray then identifies it with cohomology of the curve.
Source: Stacks Project, Tags 04JQ and 095T
(blueprint: lem-sfb-smooth-projective-curve-cohomology-local-system). -/
noncomputable def curveFirstSectionsIso (ell : ℕ) {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] {Y : Scheme.{u}} (h : Y ⟶ Spec (.of Ω)) :
    (Sheaf.Γ (Spec (.of Ω)).smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))).obj
        (curveFirstCohomology ell h) ≅
      (cohomology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) Y 1).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf Y.smallEtaleTopology
            (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))).obj
              (ModuleCat.of _ (ULift.{u + 1} (ZMod ell))))) :=
  let A := ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))
  let F := (constantSheaf Y.smallEtaleTopology A).obj
    (ModuleCat.of _ (ULift.{u + 1} (ZMod ell)))
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  let L := (lowerStar A h).rightDerivedFunctor.obj K.obj
  (Sheaf.Γ (Spec (.of Ω)).smallEtaleTopology A).mapIso
      ((_root_.DerivedCategory.homologyFunctor _ 1).mapIso
        ((lowerStar A h).rightDerivedFunctorPlusCompatibility.app K)) ≪≫
    ((homologyRightDerivedGlobalSectionsIsoOfIsSepClosed (Λ := ULift.{u + 1} (ZMod ell))
      (k := Ω) 1).app L).symm ≪≫
    (_root_.DerivedCategory.homologyFunctor _ 1).mapIso
      ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso A h).app K.obj)

/-- The stalk-to-fibre cohomology arrow induced by the very same degree-one base-change
map, using canonical germs, exact sections over the point, and Leray.
Source: Stacks Project, Tags 095T, 04JN and 04JQ
(blueprint: lem-sfb-smooth-projective-curve-cohomology-local-system). -/
noncomputable def curveFirstStalkMap (ell : ℕ) {X T : Scheme.{u}} (f : X ⟶ T)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    pointedEtaleStalk (curveFirstCohomology ell f) t ⟶
      (cohomology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) (pullback f t) 1).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf (pullback f t).smallEtaleTopology
            (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))).obj
              (ModuleCat.of _ (ULift.{u + 1} (ZMod ell))))) :=
  (curvePointPullbackStalkIso ell t (curveFirstCohomology ell f)).inv ≫
    (Sheaf.Γ (Spec (.of Ω)).smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))).map (curveFirstBaseChange ell f t) ≫
    (curveFirstSectionsIso ell (pullback.snd f t)).hom

/-- First cohomology of a smooth projective genus-g curve family is locally free constant
of rank 2g, commutes with every base change, and has the specified fibre-cohomology stalks.
Source: Stacks Project, Tags 0GLI, 095T and 03RQ
(blueprint: lem-sfb-smooth-projective-curve-cohomology-local-system).

Proof:
1. Projective-bundle properness (`lem-trf-projective-bundle-proper`) makes f proper.
   Apply `lem-sfb-smooth-proper-finite-cohomology-local-system` to the constant prime-field
   sheaf in degree one. It has finite-dimensional constant local models on an etale cover.
2. Apply `det-properbasechange-modules` to the degree-zero constant sheaf. Its homology
   is killed by ell, hence torsion. Exact inverse image (`lem-pe-constant-left-module-...`)
   and `lem-kun-pullback-constant` give exactly `curveFirstBaseChange`, hence its invertibility.
3. Take this base change along t. The point pullback is the stalk by
   `lem-weil-pbc-geometric-point-pullback-stalk`; exact global sections over Spec Omega
   and Leray identify the target with fibre cohomology. These are precisely the composites
   defining `curveFirstStalkMap`, not arbitrarily chosen cohomology identifications.
4. Properness survives base change (`lem-pc-proper-base-change`). Choose a primitive ell-th
   root only in Omega (`lem-sc-primitive-root`). The Kummer computation
   `thm-sc-proper-cohomology` identifies the fibre H1 with A^(2g). Additive maps are A-linear
   since A is a prime field. This gives the stalk dimension 2g.
5. In each nonempty trivializing chart take a geometric point. Inverse-image stalks
   (`lem-weil-pbc-inverse-image-stalk-germ`) and constant-sheaf stalks
   (`lem-weil-pbc-constant-sheaf-geometric-stalk`) identify its local model with A^(2g).
   Empty charts are harmless; for empty T use the empty cover. This includes g=0,
   ell=2 and disconnected bases, without a Noetherian hypothesis or a root on T.
-/
theorem localSystem_firstCohomology_smooth_projective_curve
    {X T : Scheme.{u}} (f : X ⟶ T) [Smooth f] (hprojective : IsProjectiveBundle f)
    (g ell : ℕ) [Fact ell.Prime]
    (hunit : ∀ t : T, IsUnit (ell : T.presheaf.stalk t))
    (hfibre : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T),
      IsConnectedCurve (pullback.snd f t) ∧ Smooth (pullback.snd f t) ∧
        IsProjectiveBundle (pullback.snd f t) ∧ (pullback.snd f t).genus = g) :
    (∃ 𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage T, ∀ i : 𝒰.I₀,
      Nonempty ((curveFirstCohomology ell f).over (𝒰.etalePrecoverageToEtale i) ≅
        (constantSheaf (T.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i))
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))).obj
            (ModuleCat.of _ (Fin (2 * g) → ULift.{u + 1} (ZMod ell))))) ∧
    (∀ (T' : Scheme.{u}) (v : T' ⟶ T), IsIso (curveFirstBaseChange ell f v)) ∧
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T),
      IsIso (curveFirstStalkMap ell f t) ∧
        Module.finrank (ULift.{u + 1} (ZMod ell))
          (pointedEtaleStalk (A := ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))
            (curveFirstCohomology ell f) t) = 2 * g) := by
  sorry

end AlgebraicGeometry.Etale
