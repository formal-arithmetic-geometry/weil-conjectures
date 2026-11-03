/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.FiniteRingTrace.TraceFormulaDualizingComplexComposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
public import WeilConjectures.Mathlib.CategoryTheory.Conj
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import WeilConjectures.CategoryTheory.ModuleObjects.Linear
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Linear

/-! # Finite-coefficient Borel–Moore sections and proper pushforward

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-lefschetz-verdier/
sec-trace-classes-and-the-lefschetz-verdier-formula/sk-d-proper-pushforward/sk-d-integral/
def-trf-borel-moore-pushforward.md (blueprint: def-trf-borel-moore-pushforward).

The underlying objects and arrows are in the ordinary module-derived category.
The exceptional counit and dualizing comparison are read through its full constructible
subcategory. Scalars act by actual constant sections of the pulled-back coefficient ring.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace WeilConjectures.FiniteRingTrace

variable (A : Type) [CommRing A] [Finite A]
  (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
  (hell : ell ≠ D.p) (hA : ∃ n : ℕ, 0 < n ∧ ∀ a : A, (ell ^ n) • a = 0)

/-- Multiplication by a constant scalar on A_T in degree zero.
Source: the A-module of sections (blueprint: def-trf-borel-moore-pushforward). -/
def borelMooreScalars (T : Scheme.{u}) :
    A →+* End (constantCoefficientObject (coefficient A) T) := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := discreteTopology_bot A
  letI : IsTopologicalRing A := DiscreteTopology.topologicalRing
  exact ((DerivedCategory.singleFunctor _ 0).mapEndRingHom _).comp
    ((Mod.regularEndRingHom (R := condensedRingObj (coefficient A) T)).comp
      ((condensedRingScalarSections (coefficient A) T).comp
        (Profinite.continuousMapConstRingHom A)))

/-- Hom(A_T,-) with the A-action by precomposition with scalar multiplication.
Source: Hom(A_T,omega_T) as an A-module
(blueprint: def-trf-borel-moore-pushforward). -/
def borelMooreSectionsFunctor (T : Scheme.{u}) : Ambient A T ⥤ ModuleCat.{u + 1} A :=
  preadditiveCoyonedaObj (constantCoefficientObject (coefficient A) T) ⋙
    ModuleCat.restrictScalars
      ((borelMooreScalars A T).op.comp (RingEquiv.toOpposite A).toRingHom)

/-- The ordinary ambient morphisms A_T -> omega_T, with their constant A-action.
Source: first display and its A-module clause
(blueprint: def-trf-borel-moore-pushforward). -/
def BorelMooreSections (T : Over (Spec (.of D.k)))
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom] :
    ModuleCat.{u + 1} A :=
  (borelMooreSectionsFunctor A T.left).obj (dualizingComplex A D ell hell hA T)

variable {T U : Over (Spec (.of D.k))}
  [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]

/-- The canonical identification Lh* A_U = A_T, using the derived monoidal unit.
Source: the ordinary-unit arrow (blueprint: def-trf-borel-moore-pushforward). -/
def borelMoorePullbackCoefficient (h : T ⟶ U) :
    (upperStar (coefficient A) h.left).leftDerivedFunctor.obj
        (constantCoefficientObject (coefficient A) U.left) ≅
      constantCoefficientObject (coefficient A) T.left :=
  (upperStar (coefficient A) h.left).leftDerivedFunctor.mapIso
      (DerivedCategory.singleFunctorObjUnitIso _ ) ≪≫
    leftDerivedUpperStarUnitIso (coefficient A) h.left ≪≫
    (DerivedCategory.singleFunctorObjUnitIso _).symm

/-- Proper compact support is the ordinary direct image. Compare the chosen model to
h's own proper compactification, then remove extension by zero along the identity.
The initial equality is the actual Brown restriction's lower_eq, not an arbitrary map.
Source: the proper comparison arrow (blueprint: def-trf-borel-moore-pushforward). -/
def borelMooreProperComparison (h : T ⟶ U) [IsProper h.left] (K : Ctf A T.left) :
    ((compositionData A D ell hell hA h).lower.obj K).obj ≅
      (lowerStar (coefficient A) h.left).rightDerivedFunctor.obj K.obj := by
  let H := compositionCoherence A D ell hell hA
  let J : (localizingClosureProEtale (coefficient A) T.left).FullSubcategory :=
    ⟨K.obj, fun _P _hP hS ↦ hS K.obj K.property⟩
  exact eqToIso (congrArg (fun F ↦ F.obj K)
      (compositionData A D ell hell hA h).lower_eq) ≪≫
    (H.comparison (SepFinType.homMk h) (compactificationOverField h)
      (Compactification.ofIsProper h.left)).app J ≪≫
    (Functor.isoWhiskerRight (derivedOpenImmersionLowerShriekId (coefficient A) T.left)
      (lowerStar (coefficient A) h.left).rightDerivedFunctor).app K.obj ≪≫
    (Functor.leftUnitor _).app K.obj

/-- The specified pushforward of every ambient Borel–Moore section. The middle
constructible maps are forgotten through the full inclusion; no condition is imposed on alpha.
Source: the displayed composite and its three arrow explanations
(blueprint: def-trf-borel-moore-pushforward). -/
def borelMoorePushforward (h : T ⟶ U) [IsProper h.left]
    (α : BorelMooreSections A D ell hell hA T) : BorelMooreSections A D ell hell hA U :=
  (derivedUpperStarLowerStarAdjunction (coefficient A) h.left).unit.app
      (constantCoefficientObject (coefficient A) U.left) ≫
    (lowerStar (coefficient A) h.left).rightDerivedFunctor.map
      ((borelMoorePullbackCoefficient A D h).hom ≫ α) ≫
    (borelMooreProperComparison A D ell hell hA h
      (compositionOmega A D ell hell hA T)).inv ≫
    ((compositionData A D ell hell hA h).lower.map
      (dualizingComposition A D ell hell hA h).inv).hom ≫
    ((compositionData A D ell hell hA h).adjunction.counit.app
      (compositionOmega A D ell hell hA U)).hom

private def scalarRing (W : Scheme.{u}) :
    A →+* CategoryTheory.MonObj.Γ (condensedRingObj (coefficient A) W) := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := discreteTopology_bot A
  letI : IsTopologicalRing A := DiscreteTopology.topologicalRing
  exact (condensedRingScalarSections (coefficient A) W).comp
    (Profinite.continuousMapConstRingHom A)

omit [Finite A] in
private theorem regular_scalar (W : Scheme.{u}) (a : A) :
    letI := Mod.linearOfRingHom (scalarRing A W)
    Mod.regularEndRingHom (scalarRing A W a) =
      a • 𝟙 (Mod.regular (condensedRingObj (coefficient A) W)) := by
  let := Mod.linearOfRingHom (scalarRing A W)
  rw [Mod.linearOfRingHom_smul_id]
  apply Mod.hom_ext
  change (ρ_ (condensedRingObj (coefficient A) W)).inv ≫
      condensedRingObj (coefficient A) W ◁ (scalarRing A W a).hom ≫
        MonObj.mul (X := condensedRingObj (coefficient A) W) =
    (λ_ (condensedRingObj (coefficient A) W)).inv ≫
      (scalarRing A W a).hom ▷ condensedRingObj (coefficient A) W ≫
        MonObj.mul (X := condensedRingObj (coefficient A) W)
  exact Mod.rightUnitor_inv_whiskerLeft_mul_eq _

private theorem scalarSections_pushforward
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) (s : MonObj.Γ Λ) :
    (condensedRingScalarSections Λ Y s).hom ≫ condensedPushforwardHom Λ f =
      Functor.LaxMonoidal.ε (ProEtale.lowerStar Ab.{u + 1} f) ≫
        (ProEtale.lowerStar Ab.{u + 1} f).map (condensedRingScalarSections Λ X s).hom := by
  change (Functor.LaxMonoidal.ε (upperStarFromPoint Y) ≫
      (upperStarFromPoint Y).map s.hom) ≫
      ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app
        (condensedRingObj Λ Y) ≫
        (ProEtale.lowerStar Ab.{u + 1} f).map
          ((upperStarFromPointComp f).hom.app Λ)) = _
  simpa only [condensedRingScalarSections, MonObj.Γ.mapFunctor_hom, Category.assoc] using
    (CategoryTheory.Adjunction.ε_comp_map_comp_unit_app_comp_map
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f)
      (upperStarFromPoint Y) (upperStarFromPoint X) (upperStarFromPointComp f).hom s.hom)

omit [Finite A] [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] in
private theorem lowerStar_linear (h : T ⟶ U) :
    let := Mod.linearOfRingHom (scalarRing A T.left)
    let := Mod.linearOfRingHom (scalarRing A U.left)
    (lowerStar (coefficient A) h.left).Linear A := by
  apply Mod.linear_mapMod_comp_comap
    (ProEtale.lowerStar Ab.{u + 1} h.left) (condensedPushforwardHom (coefficient A) h.left)
    (scalarRing A T.left) (scalarRing A U.left)
  intro a
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := discreteTopology_bot A
  let : IsTopologicalRing A := DiscreteTopology.topologicalRing
  exact scalarSections_pushforward (coefficient A) h.left
    (Profinite.continuousMapConstRingHom A a)

omit [Finite A] in
private theorem scalar_eq (W : Scheme.{u}) (a : A) :
    let := Mod.linearOfRingHom (scalarRing A W)
    borelMooreScalars A W a =
      a • 𝟙 (constantCoefficientObject (coefficient A) W) := by
  let := Mod.linearOfRingHom (scalarRing A W)
  change (DerivedCategory.singleFunctor _ 0).map
    (Mod.regularEndRingHom (scalarRing A W a)) = _
  calc
    _ = (DerivedCategory.singleFunctor _ 0).map (a • 𝟙 _) :=
      congrArg _ (regular_scalar A W a)
    _ = a • (DerivedCategory.singleFunctor _ 0).map (𝟙 _) :=
      CategoryTheory.Functor.map_smul _ _ _
    _ = _ := congrArg (fun f ↦ a • f) (CategoryTheory.Functor.map_id _ _)

private def ambientScalar (R : Type*) [CommRing R]
    {C : Type*} [Category C] [Preadditive C] [CategoryTheory.Linear R C]
    {X Y : C} (a : R) (f : X ⟶ Y) : X ⟶ Y := a • f

private theorem section_smul (W : Over (Spec (.of D.k)))
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    (a : A) (α : BorelMooreSections A D ell hell hA W) :
    let := Mod.linearOfRingHom (scalarRing A W.left)
    (a • α : BorelMooreSections A D ell hell hA W) =
      ambientScalar A a (α : constantCoefficientObject (coefficient A) W.left ⟶
        dualizingComplex A D ell hell hA W) := by
  let := Mod.linearOfRingHom (scalarRing A W.left)
  change borelMooreScalars A W.left a ≫ α = _
  rw [scalar_eq]
  exact (Linear.smul_comp _ _ _ a (𝟙 _) α).trans
    (congrArg (fun f ↦ a • f) (Category.id_comp α))

private def compositeLinearMap (R : Type*) [CommRing R]
    {C D' : Type*} [Category C] [Category D'] [Preadditive C] [Preadditive D']
    [CategoryTheory.Linear R C] [CategoryTheory.Linear R D']
    (F : C ⥤ D') [F.Additive] [F.Linear R]
    {X X' Y : C} {Z W : D'} (c : X ⟶ X') (p : Z ⟶ F.obj X)
    (q : F.obj Y ⟶ W) : (X' ⟶ Y) →ₗ[R] (Z ⟶ W) :=
  (Linear.leftComp R W p).comp
    ((Linear.rightComp R (F.obj X) q).comp
      ((F.mapLinearMap R).comp (Linear.leftComp R Y c)))

/-- Additivity and A-linearity of precisely the displayed pushforward.
Source: final sentence (blueprint: def-trf-borel-moore-pushforward).

Proof: composition is bilinear and the ordinary derived direct image is additive.
For a constant scalar a, the canonical pullback coefficient isomorphism intertwines
multiplication by a on A_U and A_T. Naturality of the ordinary adjunction unit moves
this multiplication across the first two arrows. Functoriality moves it across the
image of alpha. All later arrows are fixed, so their compositions retain that same
scalar. This proves the second equality for the constant-section action defining
borelMooreSectionsFunctor; the first follows from additivity of image and composition. -/
theorem borelMoorePushforward_linear (h : T ⟶ U) [IsProper h.left] :
    (∀ α β : BorelMooreSections A D ell hell hA T,
      borelMoorePushforward A D ell hell hA h (α + β) =
        borelMoorePushforward A D ell hell hA h α +
          borelMoorePushforward A D ell hell hA h β) ∧
    (∀ (a : A) (α : BorelMooreSections A D ell hell hA T),
      borelMoorePushforward A D ell hell hA h (a • α) =
        a • borelMoorePushforward A D ell hell hA h α) := by
  let := Mod.linearOfRingHom (scalarRing A T.left)
  let := Mod.linearOfRingHom (scalarRing A U.left)
  let := lowerStar_linear A D h
  let L := compositeLinearMap A (lowerStar (coefficient A) h.left).rightDerivedFunctor
    (borelMoorePullbackCoefficient A D h).hom
    ((derivedUpperStarLowerStarAdjunction (coefficient A) h.left).unit.app
      (constantCoefficientObject (coefficient A) U.left))
    ((borelMooreProperComparison A D ell hell hA h
        (compositionOmega A D ell hell hA T)).inv ≫
      ((compositionData A D ell hell hA h).lower.map
        (dualizingComposition A D ell hell hA h).inv).hom ≫
      ((compositionData A D ell hell hA h).adjunction.counit.app
        (compositionOmega A D ell hell hA U)).hom)
  constructor
  · intro α β
    exact L.map_add α β
  · intro a α
    calc
      borelMoorePushforward A D ell hell hA h (a • α) =
          L (ambientScalar A a (α : constantCoefficientObject (coefficient A) T.left ⟶
            dualizingComplex A D ell hell hA T)) :=
        congrArg L (section_smul A D ell hell hA T a α)
      _ = ambientScalar A a (L α) := L.map_smul a α
      _ = (a • borelMoorePushforward A D ell hell hA h α :
          BorelMooreSections A D ell hell hA U) :=
        (section_smul A D ell hell hA U a
          (borelMoorePushforward A D ell hell hA h α)).symm

/-- The A-linear proper pushforward, with data the prescribed composite.
Source: the final A-linearity clause (blueprint: def-trf-borel-moore-pushforward). -/
def borelMoorePushforwardLinearMap (h : T ⟶ U) [IsProper h.left] :
    BorelMooreSections A D ell hell hA T →ₗ[A] BorelMooreSections A D ell hell hA U where
  toFun := borelMoorePushforward A D ell hell hA h
  map_add' := (borelMoorePushforward_linear A D ell hell hA h).1
  map_smul' := (borelMoorePushforward_linear A D ell hell hA h).2

/-- The source definition at the specified positive DVR-quotient stage. A ring
isomorphism allows the finite ring to be presented in the small universe used by
continuous condensed coefficients; it retains the entire quotient ring, including
nonreduced stages. Finite and primary witnesses are the coefficient conventions.
Source: A = A_{E,n} and the displayed proper pushforward
(blueprint: def-trf-borel-moore-pushforward). -/
def finiteStageBorelMoorePushforward
    (E : Type u) [Field E] [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    (n : ℕ) (_hn : 1 ≤ n) (_stage : A ≃+* Padic.coefficientExtensionRing ell E n)
    (h : T ⟶ U) [IsProper h.left] :
    BorelMooreSections A D ell hell hA T →ₗ[A] BorelMooreSections A D ell hell hA U :=
  borelMoorePushforwardLinearMap A D ell hell hA h

end WeilConjectures.FiniteRingTrace
