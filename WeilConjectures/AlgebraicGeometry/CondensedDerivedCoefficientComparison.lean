/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedOrdinaryCompactSections
public import WeilConjectures.AlgebraicGeometry.GlobalGeometricFrobenius
public import WeilConjectures.TraceFormula.PointFiberFunctor
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
public import WeilConjectures.CategoryTheory.Preadditive.CoyonedaSectionsExtendScalars
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import WeilConjectures.AlgebraicGeometry.FrobeniusDetailed
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryNatTrans
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalIso
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.AlgebraicGeometry.GeometricHypotheses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsRegularEnd
public import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange

import WeilConjectures.AlgebraicGeometry.CondensedPointCoefficients
import WeilConjectures.SixFunctors.FrobeniusSquareCartesian
import WeilConjectures.CategoryTheory.Sites.ContractibleDerivedSectionsTensor
import WeilConjectures.AlgebraicGeometry.CondensedCoefficientCompatibility
import WeilConjectures.AlgebraicGeometry.CondensedPullIsoBalancedComparison
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleTensorPreservation
import WeilConjectures.AlgebraicGeometry.ScalarGeometricExchangeRectangle
import WeilConjectures.AlgebraicGeometry.PointProEtaleSectionsExactOfUniverses
import WeilConjectures.AlgebraicGeometry.SfWeilSheafComplex
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.RingTheory.ProEtale.WContractible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeOfFinitelyPresented.Sections
import WeilConjectures.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility

/-! # The canonical derived condensed coefficient comparison

Source: Weil blueprint, lem-sfb-qlbar-push-iso-proper, and the coefficient-extension
clause used in prop-arithmetic-roots
(blueprint: lem-weil-condensed-derived-coefficient-comparison).

The closure is presented by the native finite-subextension-valued condensed ring.
An algebra isomorphism transports its scalar action to any specified algebraic closure.
The base field is universe-lifted, so both ordinary coefficient module categories have
room for the independent universe of that closure.
The section and Frobenius helpers belong to this comparison; the recorded ordinary,
compact-support and global-Frobenius dependency interfaces remain publicly imported.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilConjectures

/-- Restriction of scalars is exact even when the target ring is not commutative.
Kernels and images have the same underlying additive groups. -/
private theorem condensedRestrictScalarsExact
    {A : Type u} {B : Type v} [Ring A] [Ring B] (f : A →+* B) :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{w} f) ∧
      PreservesFiniteColimits (ModuleCat.restrictScalars.{w} f) := by
  apply ((Functor.exact_tfae (ModuleCat.restrictScalars.{w} f)).out 1 3).mp
  intro T hT
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hT ⊢
  exact hT

section CoefficientSectionHelpers

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  (R : Type v) [CommRing R] (c : R →+* Γ Λ)

/-- Actual sections of internal coefficient modules, with their coefficient action.
The final ULift changes only the containing universe, allowing arbitrary coefficient size.
Source: HRS (3.1) (blueprint: lem-weil-condensed-derived-coefficient-comparison). -/
def condensedSections (X : Scheme.{u}) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ⥤
      ModuleCat.{max (u + 1) v} R :=
  CondensedRing.condensedRingCoefficientSections Λ X ⋙
    ModuleCat.restrictScalars c ⋙
      ModuleCat.uliftFunctor.{v} R

/-- Sections are additive. Source: HRS (3.1)
(blueprint: lem-weil-condensed-derived-coefficient-comparison). -/
instance condensedSections_additive (X : Scheme.{u}) : (condensedSections Λ R c X).Additive :=
  inferInstanceAs ((CondensedRing.condensedRingCoefficientSections Λ X ⋙
    ModuleCat.restrictScalars c ⋙ ModuleCat.uliftFunctor R).Additive)

/-- Sections preserve finite limits, computed on the underlying abelian groups.
Source: HRS (3.1) (blueprint: lem-weil-condensed-derived-coefficient-comparison).
Proof: representable Hom preserves limits. Restriction of scalars does not change
underlying groups and their limit cones, and ULift preserves finite limits. -/
@[instance] theorem condensedSections_leftExact (X : Scheme.{u}) :
    PreservesFiniteLimits (condensedSections Λ R c X) := by
  let d : Γ Λ →+* (End (Mod.regular (condensedRingObj Λ X)))ᵐᵒᵖ :=
    (Mod.regularEndRingHom.op).comp
      ((RingEquiv.toOpposite _).toRingHom.comp
        (CondensedRing.condensedRingScalarSections Λ X))
  have := (condensedRestrictScalarsExact.{u + 1, u + 1, u + 1} d).1
  dsimp only [condensedSections, CondensedRing.condensedRingCoefficientSections,
    coyonedaSections]
  exact comp_preservesFiniteLimits _ _

/-- Sections over a separably closed field are exact: the regular module is projective.
Source: HRS Lemma 4.1(1) (blueprint: lem-weil-condensed-derived-coefficient-comparison).
Proof: the terminal pro-etale object is weakly contractible; Hom from the regular
module therefore preserves epimorphisms. -/
@[instance] theorem condensedSections_pointExact (k : Type u) [Field k] [IsSepClosed k] :
    PreservesFiniteColimits (condensedSections Λ R c (Spec (.of k))) := by
  let d : Γ Λ →+* (End (Mod.regular (condensedRingObj Λ (Spec (.of k)))))ᵐᵒᵖ :=
    (Mod.regularEndRingHom.op).comp
      ((RingEquiv.toOpposite _).toRingHom.comp
        (CondensedRing.condensedRingScalarSections Λ (Spec (.of k))))
  have := (condensedRestrictScalarsExact.{u + 1, u + 1, u + 1} d).2
  dsimp only [condensedSections, CondensedRing.condensedRingCoefficientSections,
    coyonedaSections]
  exact comp_preservesFiniteColimits _ _

variable [HasDerivedCategory.{max (u + 1) v} (ModuleCat.{max (u + 1) v} R)]

/-- Ordinary derived sections of the actual condensed module category, with no
completeness condition or adic-system replacement.
Source: HRS (3.1) (blueprint: lem-weil-condensed-derived-coefficient-comparison). -/
def condensedDerivedSections (X : Scheme.{u}) :=
  (condensedSections Λ R c X).rightDerivedFunctor

/-- RΓ(X,K) is exact point evaluation of Ra_*K, for a : X → Spec k.
Source: HRS (3.1) (blueprint: lem-weil-condensed-derived-coefficient-comparison). -/
def condensedOrdinaryCohomology (k : Type u) [Field k] [IsSepClosed k]
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) :=
  (CondensedRing.lowerStar Λ a).rightDerivedFunctor ⋙
    (condensedSections Λ R c (Spec (.of k))).mapDerivedCategory

end CoefficientSectionHelpers

section FrobeniusHelpers

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  (R : Type v) [CommRing R] (c : R →+* Γ Λ)

set_option maxHeartbeats 1000000 in
-- Kernel checking unfolds the concrete pro-etale monoidal comparisons.
/-- Constant scalar sections commute with the monoidal pullback comparison. -/
private theorem condensedConstantScalar_pull {X Y : Scheme.{u}} (g : X ⟶ Y) (s : Γ Λ) :
    Γ.map (condensedPullbackHom Λ g)
      (Γ.mapFunctor (ProEtale.upperStar Ab.{u + 1} g)
        (CondensedRing.condensedRingScalarSections Λ Y s)) =
      CondensedRing.condensedRingScalarSections Λ X s := by
  ext1
  change (Functor.LaxMonoidal.ε (ProEtale.upperStar Ab.{u + 1} g) ≫
      (ProEtale.upperStar Ab.{u + 1} g).map
        (Functor.LaxMonoidal.ε (upperStarFromPoint Y) ≫
          (upperStarFromPoint Y).map s.hom)) ≫
      (upperStarFromPointComp g).hom.app Λ =
    Functor.LaxMonoidal.ε (upperStarFromPoint X) ≫
      (upperStarFromPoint X).map s.hom
  rw [Functor.map_comp]
  simp only [Category.assoc]
  have hn := (upperStarFromPointComp g).hom.naturality s.hom
  simp only [Functor.comp_map] at hn
  rw [hn]
  simp only [← Category.assoc]
  rw [← Functor.LaxMonoidal.comp_ε, NatTrans.IsMonoidal.unit]

set_option maxHeartbeats 1000000 in
-- Kernel checking unfolds the concrete pro-etale monoidal comparisons.
/-- The actual monoidal pullback unit is the inverse regular-module comparison. -/
private theorem condensedPullUnit {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (CondensedRing.monoidal_upperStar Λ g).toLaxMonoidal.ε =
      (CondensedRing.upperStarObjRegularIso Λ g).inv := by
  apply Mod.hom_ext
  change (inv (condensedPullbackHom Λ g) ≫
      ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ g)).inv.app
        (Mod.regular _)).hom) ≫
      ((Mod.extendScalars (condensedPullbackHom Λ g)).map (𝟙 (Mod.regular _))).hom =
    inv (condensedPullbackHom Λ g) ≫
      ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ g)).inv.app
        (Mod.regular _)).hom
  erw [CategoryTheory.Functor.map_id, Mod.id_hom', Category.comp_id]

set_option maxHeartbeats 1000000 in
-- Kernel checking unfolds the concrete pro-etale monoidal comparisons.
/-- Pullback carries multiplication by a constant scalar to the same scalar action. -/
private theorem condensedPull_regularEnd {X Y : Scheme.{u}} (g : X ⟶ Y) (s : Γ Λ) :
    (CondensedRing.monoidal_upperStar Λ g).toLaxMonoidal.ε ≫
      (CondensedRing.upperStar Λ g).map (Mod.regularEndRingHom
        (CondensedRing.condensedRingScalarSections Λ Y s)) =
      Mod.regularEndRingHom (CondensedRing.condensedRingScalarSections Λ X s) ≫
        (CondensedRing.monoidal_upperStar Λ g).toLaxMonoidal.ε := by
  have h := CondensedRing.restrictEnd_regularEndRingHom Λ g
    (CondensedRing.condensedRingScalarSections Λ Y s)
  rw [condensedConstantScalar_pull Λ g s, CondensedRing.restrictEnd_apply] at h
  rw [condensedPullUnit Λ g, ← cancel_mono (CondensedRing.upperStarObjRegularIso Λ g).hom]
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h

set_option maxHeartbeats 1000000 in
-- Kernel checking unfolds the concrete pro-etale monoidal comparisons.
/-- Pulling back a section is linear for the fixed constant coefficient action.
Source: the point transport in the global Frobenius definition
(blueprint: lem-weil-condensed-derived-coefficient-comparison).
Proof: multiply the section by a constant r before pulling back. Naturality of the
pullback-from-point coefficient comparison identifies its pullback with the same
constant r. Monoidality of the pullback and its unit comparison then give the
same result as multiplying the pulled-back section. ULift does not change the equation. -/
theorem condensedSectionsPull_smul {X Y : Scheme.{u}} (g : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (r : R) (m : (condensedSections Λ R c Y).obj M) :
    (ULift.up ((CondensedRing.monoidal_upperStar Λ g).toLaxMonoidal.ε ≫
      (CondensedRing.upperStar Λ g).map (r • m).down) :
        (condensedSections Λ R c X).obj ((CondensedRing.upperStar Λ g).obj M)) =
      r • (ULift.up ((CondensedRing.monoidal_upperStar Λ g).toLaxMonoidal.ε ≫
        (CondensedRing.upperStar Λ g).map m.down) :
          (condensedSections Λ R c X).obj ((CondensedRing.upperStar Λ g).obj M)) := by
  apply ULift.ext
  change (CondensedRing.monoidal_upperStar Λ g).toLaxMonoidal.ε ≫
      (CondensedRing.upperStar Λ g).map
        (Mod.regularEndRingHom
          (CondensedRing.condensedRingScalarSections Λ Y (c r)) ≫ m.down) =
    Mod.regularEndRingHom (CondensedRing.condensedRingScalarSections Λ X (c r)) ≫
      ((CondensedRing.monoidal_upperStar Λ g).toLaxMonoidal.ε ≫
        (CondensedRing.upperStar Λ g).map m.down)
  rw [Functor.map_comp, ← Category.assoc, condensedPull_regularEnd Λ g (c r), Category.assoc]

/-- Restriction of actual sections followed by the inverse-image coprojection,
with the canonical coefficient identification.
Source: the first arrow of the global Frobenius composite
(blueprint: lem-weil-condensed-derived-coefficient-comparison). -/
def condensedSectionsPull {X Y : Scheme.{u}} (g : X ⟶ Y) :
    condensedSections Λ R c Y ⟶ CondensedRing.upperStar Λ g ⋙ condensedSections Λ R c X where
  app M := ModuleCat.ofHom
    { toFun := fun m ↦ ULift.up
        ((CondensedRing.monoidal_upperStar Λ g).toLaxMonoidal.ε ≫
          (CondensedRing.upperStar Λ g).map m.down)
      map_add' := by
        intro m n
        apply ULift.ext
        change _ ≫ (CondensedRing.upperStar Λ g).map (m.down + n.down) = _
        rw [Functor.map_add, Preadditive.comp_add]
        rfl
      map_smul' := condensedSectionsPull_smul Λ R c g M }
  naturality M N f := by
    ext m
    apply ULift.ext
    dsimp [condensedSections, CondensedRing.condensedRingCoefficientSections,
      coyonedaSections, preadditiveCoyonedaObj, ModuleCat.uliftFunctor,
      ModuleCat.restrictScalars, ModuleCat.RestrictScalars.map', ULift.moduleEquiv]
    change (CondensedRing.monoidal_upperStar Λ g).toLaxMonoidal.ε ≫
      (CondensedRing.upperStar Λ g).map (m.down ≫ f) =
        ((CondensedRing.monoidal_upperStar Λ g).toLaxMonoidal.ε ≫
          (CondensedRing.upperStar Λ g).map m.down) ≫
            (CondensedRing.upperStar Λ g).map f
    rw [Functor.map_comp, Category.assoc]

variable [HasDerivedCategory.{max (u + 1) v} (ModuleCat.{max (u + 1) v} R)]

/-- Exact point transport Γ_s M → Γ_s Lh* M, on all unbounded complexes.
Source: the point part of the first Frobenius arrow
(blueprint: lem-weil-condensed-derived-coefficient-comparison). -/
def condensedPointTransport (k : Type u) [Field k] [IsSepClosed k]
    (h : Spec (.of k) ⟶ Spec (.of k)) :
    (condensedSections Λ R c (Spec (.of k))).mapDerivedCategory ⟶
      (CondensedRing.upperStar Λ h).leftDerivedFunctor ⋙
        (condensedSections Λ R c (Spec (.of k))).mapDerivedCategory :=
  Functor.mapDerivedCategoryNatTrans (condensedSectionsPull Λ R c h) ≫
    (Functor.mapDerivedCategoryCompIso _ _).hom ≫
    Functor.whiskerRight
      (CondensedRing.upperStar Λ h).leftDerivedFunctorIsoMapDerivedCategory.inv _

/-- The derived unit--square--counit exchange of the specified commutative square.
Source: the exchange in the first Frobenius arrow
(blueprint: lem-weil-condensed-derived-coefficient-comparison). -/
def condensedFrobeniusExchange {X s : Scheme.{u}} (a : X ⟶ s)
    (g : X ⟶ X) (h : s ⟶ s) (w : g ≫ a = a ≫ h) :
    (CondensedRing.lowerStar Λ a).rightDerivedFunctor ⋙
        (CondensedRing.upperStar Λ h).leftDerivedFunctor ⟶
      (CondensedRing.upperStar Λ g).leftDerivedFunctor ⋙
        (CondensedRing.lowerStar Λ a).rightDerivedFunctor :=
  Adjunction.exchangeRight (CondensedRing.derivedUpperStarLowerStarAdjunction Λ a)
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ a)
    ((CondensedRing.leftDerivedUpperStarComp Λ a h).symm ≪≫
      eqToIso (congrArg (fun f ↦ (CondensedRing.upperStar Λ f).leftDerivedFunctor) w.symm) ≪≫
      CondensedRing.leftDerivedUpperStarComp Λ g a)

/-- The specified ordinary global geometric Frobenius of a Weil pair (K,theta).
It is point transport, followed by the geometric exchange, followed by RΓ(theta).
Source: the first displayed composite of def-weil-global-geometric-frobenius
(blueprint: lem-weil-condensed-derived-coefficient-comparison). -/
def condensedGlobalGeometricFrobenius (k : Type u) [Field k] [IsSepClosed k]
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k))
    (g : X ⟶ X) (h : Spec (.of k) ⟶ Spec (.of k)) (w : g ≫ a = a ≫ h)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (theta : (CondensedRing.upperStar Λ g).leftDerivedFunctor.obj K ⟶ K) :
    End ((condensedOrdinaryCohomology Λ R c k a).obj K) :=
  (condensedPointTransport Λ R c k h).app
      ((CondensedRing.lowerStar Λ a).rightDerivedFunctor.obj K) ≫
    (condensedSections Λ R c (Spec (.of k))).mapDerivedCategory.map
      ((condensedFrobeniusExchange Λ a g h w).app K ≫
        (CondensedRing.lowerStar Λ a).rightDerivedFunctor.map theta)

/-- The fixed algebraic closure in the finite-field datum is separably closed.
Source: the finite-field datum used by the Frobenius definition
(blueprint: lem-weil-condensed-derived-coefficient-comparison). -/
instance condensedDatumIsSepClosed (D : FiniteFieldDatum.{u}) : IsSepClosed D.k := by
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  infer_instance

/-- Canonical constant-coefficient Weil action for the geometric Galois Frobenius.
The coefficient unit comparison is the canonical Weil structure, and the square
comes from the second projection of the actual geometric-fibre base change.
Source: the constant-coefficient case of the blueprint definition
(blueprint: lem-weil-condensed-derived-coefficient-comparison). -/
def condensedConstantGlobalGeometricFrobenius (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    End ((condensedOrdinaryCohomology Λ R c D.k (D.geometricFiber X₀).hom).obj (𝟙_ _)) :=
  letI := Fintype.ofFinite D.k₀
  let sigma := FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k
  condensedGlobalGeometricFrobenius Λ R c D.k (D.geometricFiber X₀).hom
    (D.galoisMap X₀.hom sigma) (Spec.map (CommRingCat.ofHom sigma.toRingHom))
    (D.galoisMap_projections X₀.hom sigma).2 (𝟙_ _)
    (CondensedRing.leftDerivedUpperStarUnitIso Λ (D.galoisMap X₀.hom sigma)).hom

end FrobeniusHelpers

section ScalarComparison

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]
  {R S : Type v} [CommRing R] [CommRing S]
  (cR : R →+* Γ Λ) (cS : S →+* Γ Λ') (phi : R →+* S)
  (hc : (Γ.map a).comp cR = cS.comp phi)

/-- The native internal scalar extension with its sheaf category made explicit.
This is only a specialization of Mod.extendScalars, fixing universe inference.
Source: definition of T^X in the item
(blueprint: lem-weil-condensed-derived-coefficient-comparison). -/
abbrev condensedInternalScalarExtension (X : Scheme.{u}) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X) :=
  Mod.extendScalars (coefficientMap a X)

/-- Additivity of the evaluated scalar unit.
Source: the balanced point comparison, HRS Lemma 4.1(1)
(blueprint: lem-weil-condensed-derived-coefficient-comparison).
Proof: extension of scalars is additive, composition is additive, and ULift preserves
addition. Apply these facts to the displayed section formula. -/
theorem condensedSectionScalarMap_add (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (m n : (condensedSections Λ R cR X).obj M) :
    (ULift.up ((Mod.extendScalarsObjRegularIso (coefficientMap a X)).inv ≫
      (condensedInternalScalarExtension a X).map (m + n).down) :
        (condensedSections Λ' S cS X).obj ((condensedInternalScalarExtension a X).obj M)) =
      (ULift.up ((Mod.extendScalarsObjRegularIso (coefficientMap a X)).inv ≫
        (condensedInternalScalarExtension a X).map m.down) :
          (condensedSections Λ' S cS X).obj ((condensedInternalScalarExtension a X).obj M)) +
      (ULift.up ((Mod.extendScalarsObjRegularIso (coefficientMap a X)).inv ≫
        (condensedInternalScalarExtension a X).map n.down) :
          (condensedSections Λ' S cS X).obj ((condensedInternalScalarExtension a X).obj M)) := by
  apply ULift.ext
  change (Mod.extendScalarsObjRegularIso (coefficientMap a X)).inv ≫
      (condensedInternalScalarExtension a X).map (m.down + n.down) =
      ((Mod.extendScalarsObjRegularIso (coefficientMap a X)).inv ≫
        (condensedInternalScalarExtension a X).map m.down) +
      ((Mod.extendScalarsObjRegularIso (coefficientMap a X)).inv ≫
        (condensedInternalScalarExtension a X).map n.down)
  rw [Functor.map_add, Preadditive.comp_add]

/-- The evaluated scalar unit is linear for the coefficient inclusion.
Source: HRS Lemma 4.1(1), the tensor-generator formula for the point comparison
(blueprint: lem-weil-condensed-derived-coefficient-comparison).
Proof: extension carries multiplication by r on the regular module to multiplication
by its coefficient image. Apply extendScalarsObjRegularIso_inv_comp_map and hc,
then use naturality of the scalar-extension unit. -/
theorem condensedSectionScalarMap_smul
    (hc : (Γ.map a).comp cR = cS.comp phi) (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (r : R) (m : (condensedSections Λ R cR X).obj M) :
    (ULift.up ((Mod.extendScalarsObjRegularIso (coefficientMap a X)).inv ≫
      (condensedInternalScalarExtension a X).map (r • m).down) :
        (condensedSections Λ' S cS X).obj ((condensedInternalScalarExtension a X).obj M)) =
      phi r • (ULift.up ((Mod.extendScalarsObjRegularIso (coefficientMap a X)).inv ≫
        (condensedInternalScalarExtension a X).map m.down) :
          (condensedSections Λ' S cS X).obj
            ((condensedInternalScalarExtension a X).obj M)) := by
  have h : Γ.map (coefficientMap a X)
      (CondensedRing.condensedRingScalarSections Λ X (cR r)) =
      CondensedRing.condensedRingScalarSections Λ' X (cS (phi r)) := by
    have hr : Γ.map a (cR r) = cS (phi r) := DFunLike.congr_fun hc r
    change Γ.map ((upperStarFromPoint X).map a)
        (Γ.mapFunctor (upperStarFromPoint X) (cR r)) =
      Γ.mapFunctor (upperStarFromPoint X) (cS (phi r))
    rw [← hr]
    ext1
    rw [Γ.map_hom, Γ.mapFunctor_hom, Γ.mapFunctor_hom, Γ.map_hom,
      Category.assoc, Functor.map_comp]
  apply ULift.ext
  change (Mod.extendScalarsObjRegularIso (coefficientMap a X)).inv ≫
      (Mod.extendScalars (coefficientMap a X)).map
        (Mod.regularEndRingHom
          (CondensedRing.condensedRingScalarSections Λ X (cR r)) ≫ m.down) =
    Mod.regularEndRingHom
        (CondensedRing.condensedRingScalarSections Λ' X (cS (phi r))) ≫
      ((Mod.extendScalarsObjRegularIso (coefficientMap a X)).inv ≫
        (Mod.extendScalars (coefficientMap a X)).map m.down)
  rw [Functor.map_comp, ← Category.assoc,
    Mod.extendScalarsObjRegularIso_inv_comp_map, h, Category.assoc]

/-- The actual evaluated unit m ↦ 1 tensor m as a linear map.
Source: the balanced point comparison, HRS Lemma 4.1(1)
(blueprint: lem-weil-condensed-derived-coefficient-comparison). -/
def condensedSectionScalarLinearMap (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (condensedSections Λ R cR X).obj M ⟶
      (condensedInternalScalarExtension a X ⋙ condensedSections Λ' S cS X ⋙
        ModuleCat.restrictScalars phi).obj M :=
  ModuleCat.ofHom (X := (condensedSections Λ R cR X).obj M)
    (Y := (condensedInternalScalarExtension a X ⋙ condensedSections Λ' S cS X ⋙
      ModuleCat.restrictScalars phi).obj M)
    { toFun := fun m ↦ ULift.up
        ((Mod.extendScalarsObjRegularIso (coefficientMap a X)).inv ≫
          (condensedInternalScalarExtension a X).map m.down)
      map_add' := condensedSectionScalarMap_add a cR cS X M
      map_smul' := condensedSectionScalarMap_smul a cR cS phi hc X M }

/-- Naturality of the actual evaluated scalar unit.
Source: the balanced point comparison, HRS Lemma 4.1(1)
(blueprint: lem-weil-condensed-derived-coefficient-comparison).
Proof: evaluate on a section m. On either side the underlying section is the regular
unit inverse followed by extension of m and then extension of f. Functoriality and
associativity identify the two expressions. -/
theorem condensedSectionScalarLinearMap_naturality (X : Scheme.{u})
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (f : M ⟶ N) :
    (condensedSections Λ R cR X).map f ≫
        condensedSectionScalarLinearMap a cR cS phi hc X N =
      condensedSectionScalarLinearMap a cR cS phi hc X M ≫
        (condensedInternalScalarExtension a X ⋙ condensedSections Λ' S cS X ⋙
          ModuleCat.restrictScalars phi).map f := by
  ext m
  apply ULift.ext
  change (Mod.extendScalarsObjRegularIso (coefficientMap a X)).inv ≫
      (condensedInternalScalarExtension a X).map (m.down ≫ f) =
    ((Mod.extendScalarsObjRegularIso (coefficientMap a X)).inv ≫
      (condensedInternalScalarExtension a X).map m.down) ≫
        (condensedInternalScalarExtension a X).map f
  rw [Functor.map_comp, Category.assoc]

/-- The evaluated unit m ↦ 1 tensor m, before the ordinary scalar adjunction.
Source: HRS Lemma 4.1(1)
(blueprint: lem-weil-condensed-derived-coefficient-comparison). -/
def condensedSectionScalarMap (X : Scheme.{u}) :
    condensedSections Λ R cR X ⟶ condensedInternalScalarExtension a X ⋙
      condensedSections Λ' S cS X ⋙ ModuleCat.restrictScalars phi where
  app := condensedSectionScalarLinearMap a cR cS phi hc X
  naturality := condensedSectionScalarLinearMap_naturality a cR cS phi hc X

/-- The balanced tensor comparison, adjoint to the actual evaluated scalar unit.
Its formula is omega tensor x ↦ omega tensor x in the extended internal module.
Source: HRS Lemma 4.1(1)
(blueprint: lem-weil-condensed-derived-coefficient-comparison). -/
def condensedSectionScalarComparison (X : Scheme.{u}) :
    condensedSections Λ R cR X ⋙ ModuleCat.extendScalars.{v, v, max (u + 1) v} phi ⟶
      condensedInternalScalarExtension a X ⋙ condensedSections Λ' S cS X where
  app M := ((ModuleCat.extendRestrictScalarsAdj phi).homEquiv _ _).symm
    ((condensedSectionScalarMap a cR cS phi hc X).app M)
  naturality M N f := by
    rw [Functor.comp_map, ← Adjunction.homEquiv_naturality_left_symm,
      (condensedSectionScalarMap a cR cS phi hc X).naturality]
    exact (ModuleCat.extendRestrictScalarsAdj phi).homEquiv_naturality_right_symm _ _

variable [HasDerivedCategory.{max (u + 1) v} (ModuleCat.{max (u + 1) v} R)]
  [HasDerivedCategory.{max (u + 1) v} (ModuleCat.{max (u + 1) v} S)]
  [∀ X : Scheme.{u}, PreservesFiniteLimits (condensedInternalScalarExtension a X)]
  [PreservesFiniteLimits (ModuleCat.extendScalars.{v, v, max (u + 1) v} phi)]

/-- The canonical point tensor comparison rho, derived from its balanced section map.
The internal extension is identified with its termwise model by the canonical
left-derived computation comparison.
Source: HRS Lemma 4.1(1)
(blueprint: lem-weil-condensed-derived-coefficient-comparison). -/
def condensedPointScalarComparison (k : Type u) [Field k] [IsSepClosed k] :
    (condensedSections Λ R cR (Spec (.of k))).mapDerivedCategory ⋙
        (ModuleCat.extendScalars.{v, v, max (u + 1) v} phi).mapDerivedCategory ⟶
      (condensedInternalScalarExtension a (Spec (.of k))).leftDerivedFunctor ⋙
        (condensedSections Λ' S cS (Spec (.of k))).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).inv ≫
    Functor.mapDerivedCategoryNatTrans (condensedSectionScalarComparison a cR cS phi hc _) ≫
    (Functor.mapDerivedCategoryCompIso _ _).hom ≫
    Functor.whiskerRight
      (Functor.leftDerivedFunctorIsoMapDerivedCategory
        (condensedInternalScalarExtension a (Spec (.of k)))).inv _

end ScalarComparison

section PadicComparison

variable (l : ℕ) [Fact l.Prime]

/-- The degree-one finite subextension representing L = Q_l, with no choice.
Source: the E=L specialization of lem-sfb-qlbar-push-iso-proper
(blueprint: lem-weil-condensed-derived-coefficient-comparison). -/
def condensedComparisonBaseStage : PadicAlgCl.FiniteIntermediateField l :=
  ⟨⊥, inferInstance⟩

/-- Q_l in the universe containing the chosen closure. The bottom intermediate field
is canonically Q_l, and ULift changes only its universe.
Source: the coefficient convention of the item
(blueprint: lem-weil-condensed-derived-coefficient-comparison). -/
abbrev condensedComparisonBaseField := ULift.{v} (condensedComparisonBaseStage l).val

variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Transport the fixed native algebraic-closure presentation to the chosen closure.
Source: the chosen algebraic closure in the item; Stacks 09GV
(blueprint: lem-weil-condensed-derived-coefficient-comparison). -/
def condensedComparisonClosureEquiv : PadicAlgCl l ≃ₐ[Padic l] Ω :=
  IsAlgClosure.equiv (Padic l) (PadicAlgCl l) Ω

/-- The inclusion L → Ω in the native bottom-stage presentation.
Source: the coefficient inclusion of the item
(blueprint: lem-weil-condensed-derived-coefficient-comparison). -/
def condensedComparisonInclusion : condensedComparisonBaseField.{v} l →+* Ω :=
  (condensedComparisonClosureEquiv l Ω).toRingHom.comp
    ((condensedComparisonBaseStage l).val.val.toRingHom.comp ULift.ringEquiv.toRingHom)

/-- Constant L-sections of the condensed bottom-stage ring.
Source: HRS (3.1) (blueprint: lem-weil-condensed-derived-coefficient-comparison). -/
def condensedComparisonBaseConstants :
    condensedComparisonBaseField.{v} l →+*
      Γ (Profinite.continuousMapRingObj.{u} (condensedComparisonBaseStage l)) :=
  (Profinite.continuousMapConstRingHom (condensedComparisonBaseStage l)).comp
    ULift.ringEquiv.toRingHom

/-- Constant Ω-sections of the native condensed closure, transported by the fixed
algebra equivalence. The ring itself retains the finite-subextension-valued sections.
Source: HRS (3.1) (blueprint: lem-weil-condensed-derived-coefficient-comparison). -/
def condensedComparisonClosureConstants : Ω →+* Γ (Profinite.padicAlgClRingObj.{u} l) :=
  (Profinite.PadicAlgCl.constRingHom l).comp
    (condensedComparisonClosureEquiv l Ω).symm.toRingHom

/-- Constant sections commute with the native coefficient inclusion.
Source: HRS (3.1) and the coefficient-map definition
(blueprint: lem-weil-condensed-derived-coefficient-comparison).
Proof: evaluation of either side on any profinite test object sends r to the
constant function with value its image in the chosen closure. The closure equivalence
and its inverse cancel, and the sheafification adjunction preserves this equality. -/
theorem condensedComparisonConstants_commute :
    (Γ.map (Profinite.padicSubfieldRingObjToPadicAlgCl.{u} l
      (condensedComparisonBaseStage l))).comp
        (condensedComparisonBaseConstants.{u, v} l) =
      (condensedComparisonClosureConstants.{u} l Ω).comp
        (condensedComparisonInclusion l Ω) := by
  apply RingHom.ext
  intro r
  change Γ.map (Profinite.padicSubfieldRingObjToPadicAlgCl l
      (condensedComparisonBaseStage l))
      (Profinite.continuousMapConstRingHom (condensedComparisonBaseStage l) r.down) =
    Profinite.PadicAlgCl.constRingHom l
      ((condensedComparisonClosureEquiv l Ω).symm
        ((condensedComparisonClosureEquiv l Ω) r.down.val))
  rw [AlgEquiv.symm_apply_apply]
  exact Sheaf.Γ_map_ringHomΓSheafCompose _
    (Profinite.padicSubfieldCondensedRingToPadicAlgCl l (condensedComparisonBaseStage l)) _
    (fun _ _ ↦ rfl) _ (fun _ _ ↦ rfl) fun _ ↦ rfl

/-- Ordinary scalar extension along a field inclusion is exact.
Source: the flat coefficient inclusion of lem-sfb-qlbar-push-iso-proper
(blueprint: lem-weil-condensed-derived-coefficient-comparison).
Proof: every module over a field is flat, so tensoring with Ω is exact. -/
@[instance] theorem condensedComparisonInclusion_exact :
    PreservesFiniteLimits
      (ModuleCat.extendScalars.{v, v, w} (condensedComparisonInclusion l Ω)) := by
  let := (condensedComparisonInclusion l Ω).toAlgebra
  have h : (ModuleCat.extendScalars.{v, v, w}
      (condensedComparisonInclusion l Ω)).PreservesHomology := by
    apply Functor.preservesHomology_of_map_exact
    intro T hT
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hT ⊢
    exact Module.Flat.lTensor_exact Ω hT
  exact Functor.preservesFiniteLimits_of_preservesHomology _

variable [HasDerivedCategory.{max (u + 1) v}
    (ModuleCat.{max (u + 1) v} (condensedComparisonBaseField.{v} l))]
  [HasDerivedCategory.{max (u + 1) v} (ModuleCat.{max (u + 1) v} Ω)]

/-- The derived regular-unit identification T^X L_X ≅ Ω_X.
Source: the unit normalization in the item
(blueprint: lem-weil-condensed-derived-coefficient-comparison). -/
def condensedComparisonUnitIso (X : Scheme.{u}) :
    (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X l
      (condensedComparisonBaseStage l))).leftDerivedFunctor.obj (𝟙_ _) ≅ 𝟙_ _ :=
  asIso ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X l
    (condensedComparisonBaseStage l))).leftDerivedFunctorCounit.app (𝟙_ _)) ≪≫
      DerivedCategory.Qh.mapIso
        (((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X l
          (condensedComparisonBaseStage l))).mapHomotopyCategoryFactors (.up ℤ)).app (𝟙_ _) ≪≫
          (HomotopyCategory.quotient _ _).mapIso
            ((HomologicalComplex.singleMapHomologicalComplex
              (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X l
                (condensedComparisonBaseStage l))) (.up ℤ) 0).app (𝟙_ _) ≪≫
              (HomologicalComplex.single _ _ 0).mapIso
                (Mod.extendScalarsObjRegularIso (padicSubfieldRingObjToPadicAlgCl X l
                  (condensedComparisonBaseStage l)))))

/-- The specified canonical comparison b_X: rho at Ra_*L_X, followed by evaluation
of (Push), followed by T^XL_X ≅ Ω_X. No arbitrary isomorphism is selected.
Source: lem-sfb-qlbar-push-iso-proper, the construction in the item
(blueprint: lem-weil-condensed-derived-coefficient-comparison). -/
def condensedDerivedCoefficientComparison (k : Type u) [Field k] [IsSepClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    (ModuleCat.extendScalars.{v, v, max (u + 1) v}
      (condensedComparisonInclusion l Ω)).mapDerivedCategory.obj
      ((condensedOrdinaryCohomology
        (Profinite.continuousMapRingObj (condensedComparisonBaseStage l))
        (condensedComparisonBaseField.{v} l) (condensedComparisonBaseConstants l) k f).obj
          (𝟙_ _)) ⟶
      (condensedOrdinaryCohomology (Profinite.padicAlgClRingObj l) Ω
        (condensedComparisonClosureConstants l Ω) k f).obj (𝟙_ _) :=
  (condensedPointScalarComparison
    (Profinite.padicSubfieldRingObjToPadicAlgCl l (condensedComparisonBaseStage l))
    (condensedComparisonBaseConstants l) (condensedComparisonClosureConstants l Ω)
    (condensedComparisonInclusion l Ω) (condensedComparisonConstants_commute l Ω) k).app
      ((Functor.rightDerivedFunctor (CondensedRing.lowerStar
        (Profinite.continuousMapRingObj (condensedComparisonBaseStage l)) f)).obj (𝟙_ _)) ≫
    (condensedSections (Profinite.padicAlgClRingObj l) Ω
      (condensedComparisonClosureConstants l Ω) (Spec (.of k))).mapDerivedCategory.map
        ((CondensedRing.derivedPushHom
          (Profinite.padicSubfieldRingObjToPadicAlgCl l (condensedComparisonBaseStage l)) f).app
            (𝟙_ _) ≫
          (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) f).rightDerivedFunctor.map
            (condensedComparisonUnitIso l X).hom)


/-- Underived point-section scalar comparison for one coefficient module.
The underived map is the balanced tensor comparison on sections. Proving its
invertibility is the first, strictly underived, part of the point comparison.
Source: Hemo--Richarz--Scholbach, Section 3 (3.1)-(3.2) and Lemma 4.1(1).
(blueprint: new-weil-condensed-point-section-scalar-comparison)

Proof: the separably closed point is w-contractible, so every pro-etale covering of it
has a section and every covering sieve of it is maximal. Hence sections at the point do
not change under sheafification and commute with colimits and tensor products of
presheaves. The internal extension is a coequalizer of sheafified tensors, so its
sections are Omega tensored over L with the sections of M, the coefficient rings
evaluating to L and Omega at the point. Under this identification the comparison is the
symmetry x tensor omega to omega tensor x, which is bijective.
-/
theorem condensedPointSectionScalarComparison_isIso_aux
    (k : Type u) [Field k] [IsSepClosed k]
    (M : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj (condensedComparisonBaseStage l))
        (Spec (.of k)))) :
    IsIso ((condensedSectionScalarComparison
      (Profinite.padicSubfieldRingObjToPadicAlgCl l (condensedComparisonBaseStage l))
      (condensedComparisonBaseConstants l) (condensedComparisonClosureConstants l Ω)
      (condensedComparisonInclusion l Ω) (condensedComparisonConstants_commute l Ω)
      (Spec (.of k))).app M)   := by
  sorry

omit [HasDerivedCategory.{max (u + 1) v}
  (ModuleCat.{max (u + 1) v} (condensedComparisonBaseField.{v} l))] in
/-- Derived point scalar comparison from the underived section comparison.
This is the localization step: exactness of the section and scalar-extension functors
lifts the underived isomorphisms to every homology object, and the derived natural
transformation criterion gives the displayed component.
Source: Hemo--Richarz--Scholbach, Lemma 4.1(1), derived localization step.
(blueprint: new-weil-condensed-derived-point-scalar-comparison)
-/
theorem condensedPointScalarComparison_map_isIso_aux
    (k : Type u) [Field k] [IsSepClosed k]
    (hsec : ∀ M : Mod
      (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj (condensedComparisonBaseStage l))
        (Spec (.of k))),
      IsIso ((condensedSectionScalarComparison
        (Profinite.padicSubfieldRingObjToPadicAlgCl l (condensedComparisonBaseStage l))
        (condensedComparisonBaseConstants l) (condensedComparisonClosureConstants l Ω)
        (condensedComparisonInclusion l Ω) (condensedComparisonConstants_commute l Ω)
        (Spec (.of k))).app M))
    (P : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj (condensedComparisonBaseStage l))
          (Spec (.of k))))) :
    IsIso ((Functor.mapDerivedCategoryNatTrans
      (condensedSectionScalarComparison
        (Profinite.padicSubfieldRingObjToPadicAlgCl l (condensedComparisonBaseStage l))
        (condensedComparisonBaseConstants l) (condensedComparisonClosureConstants l Ω)
        (condensedComparisonInclusion l Ω) (condensedComparisonConstants_commute l Ω)
        (Spec (.of k)))).app P) :=
  Functor.isIso_mapDerivedCategoryNatTrans_app _ P fun _ ↦ hsec _

/-- Point evaluation identifies the actual internal scalar extension with ordinary
scalar extension for every unbounded object, with no constructibility hypothesis.
Source: HRS Lemma 4.1(1), symmetric monoidality on a weakly contractible affine
(blueprint: lem-weil-condensed-derived-coefficient-comparison).
Proof: Spec k is weakly contractible, so its section functor is exact and symmetric
monoidal. Its canonical tensor comparison is the balanced map used to construct rho.
The coefficient rings evaluate to L and Ω. The comparison is Ω-linear on pure tensors;
its inverse as an underlying L-linear map is consequently Ω-linear. Exactness of the
internal and ordinary scalar extensions identifies their derived and termwise models,
so this computation applies to every unbounded representative. -/
theorem isIso_condensedPointScalarComparison (k : Type u) [Field k] [IsSepClosed k]
    (P : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (condensedRingObj
        (Profinite.continuousMapRingObj (condensedComparisonBaseStage l)) (Spec (.of k))))) :
    IsIso ((condensedPointScalarComparison
      (Profinite.padicSubfieldRingObjToPadicAlgCl l (condensedComparisonBaseStage l))
      (condensedComparisonBaseConstants l) (condensedComparisonClosureConstants l Ω)
      (condensedComparisonInclusion l Ω) (condensedComparisonConstants_commute l Ω) k).app P) := by
  have hsec : ∀ M : Mod
      (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj (condensedComparisonBaseStage l))
        (Spec (.of k))),
      IsIso ((condensedSectionScalarComparison
        (Profinite.padicSubfieldRingObjToPadicAlgCl l (condensedComparisonBaseStage l))
        (condensedComparisonBaseConstants l) (condensedComparisonClosureConstants l Ω)
        (condensedComparisonInclusion l Ω) (condensedComparisonConstants_commute l Ω)
        (Spec (.of k))).app M) :=
    fun M ↦ condensedPointSectionScalarComparison_isIso_aux l Ω k M
  have hmap := condensedPointScalarComparison_map_isIso_aux l Ω k hsec P
  dsimp [condensedPointScalarComparison]
  infer_instance

/-- Frobenius compatibility for the specified condensed coefficient comparison.
The proof is the normalized scalar/geometric exchange rectangle, together with the
point transport and the coefficient-unit Weil naturality. It is separated from the
isomorphism argument because it requires the full mate rectangle and its K-flat
normalization.
Source: the Frobenius compatibility steps of
`lem-weil-condensed-derived-coefficient-comparison`.
(blueprint: new-weil-condensed-derived-coefficient-frobenius-compatibility)
-/
theorem condensed_derived_coefficient_frobenius_compatibility_aux
    (D : FiniteFieldDatum.{u})
    (hl : l ≠ D.p) (X₀ : Over (Spec (.of D.k₀)))
    [IsProper X₀.hom] [GeometricallyConnected X₀.hom]
    (d : ℕ) (hX : D.IsSmoothOfPureDimension X₀ d) :
    (ModuleCat.extendScalars.{v, v, max (u + 1) v}
        (condensedComparisonInclusion l Ω)).mapDerivedCategory.map
        (condensedConstantGlobalGeometricFrobenius
          (Profinite.continuousMapRingObj (condensedComparisonBaseStage l))
          (condensedComparisonBaseField.{v} l) (condensedComparisonBaseConstants l) D X₀) ≫
        condensedDerivedCoefficientComparison l Ω D.k (D.geometricFiber X₀).hom =
      condensedDerivedCoefficientComparison l Ω D.k (D.geometricFiber X₀).hom ≫
        condensedConstantGlobalGeometricFrobenius (Profinite.padicAlgClRingObj l) Ω
          (condensedComparisonClosureConstants l Ω) D X₀ := by
  sorry

/-- The specified coefficient comparison is an isomorphism and intertwines the
canonical global geometric Frobenius endomorphisms as morphisms in D(Ω).
Source: lem-sfb-qlbar-push-iso-proper and the scalar-extension clause of
prop-arithmetic-roots (blueprint: lem-weil-condensed-derived-coefficient-comparison).
Proof: (1) Properness survives geometric base change. The coefficient units and
 their proper direct images are bounded constructible (lem-sfb-dc-tensor-unit and
 lem-sfb-dc-lower-star-preserves), so these are the stipulated ordinary complexes.
(2) Spec k is weakly contractible. HRS Lemma 4.1(1) gives the canonical point tensor
isomorphism rho, including on unbounded inputs, as in isIso_condensedPointScalarComparison.
(3) The bounded-below proper Push clause of prop-zl-condensed-coefficient-compatibility
makes the native derivedPushHom invertible at the coefficient unit. Thus b, its evaluated
composite with rho and the regular-unit identification, is invertible.
(4) In the Cartesian semilinear Frobenius square, the inverse Pull is the balanced
K-flat comparison (lem-weil-condensed-pull-iso-balanced-comparison). The Push map is its
unit--counit mate. The scalar/geometric exchange rectangle therefore applies to these
specified maps, not to an arbitrary isomorphism.
(5) The unit Weil structures commute with scalar extension. On pure tensors both
maps multiply the coefficient with the section. Point transport also commutes with
rho and the balanced Pull: both send a tensor to its transported section with the
same constant coefficient. Exactness lets these identities descend to complexes.
(6) Apply the exchange rectangle, its naturality at the unit Weil map, naturality of
point transport at Push, and naturality of rho. Substituting the defining composite
of global Frobenius yields precisely the displayed morphism equality. -/
theorem condensed_derived_coefficient_comparison (D : FiniteFieldDatum.{u})
    (hl : l ≠ D.p) (X₀ : Over (Spec (.of D.k₀)))
    [IsProper X₀.hom] [GeometricallyConnected X₀.hom]
    (d : ℕ) (hX : D.IsSmoothOfPureDimension X₀ d) :
    IsIso (condensedDerivedCoefficientComparison l Ω D.k (D.geometricFiber X₀).hom) ∧
      (ModuleCat.extendScalars.{v, v, max (u + 1) v}
        (condensedComparisonInclusion l Ω)).mapDerivedCategory.map
        (condensedConstantGlobalGeometricFrobenius
          (Profinite.continuousMapRingObj (condensedComparisonBaseStage l))
          (condensedComparisonBaseField.{v} l) (condensedComparisonBaseConstants l) D X₀) ≫
        condensedDerivedCoefficientComparison l Ω D.k (D.geometricFiber X₀).hom =
      condensedDerivedCoefficientComparison l Ω D.k (D.geometricFiber X₀).hom ≫
        condensedConstantGlobalGeometricFrobenius (Profinite.padicAlgClRingObj l) Ω
          (condensedComparisonClosureConstants l Ω) D X₀ := by
  constructor
  · have : IsProper (D.geometricFiber X₀).hom :=
      MorphismProperty.pullback_snd _ _ inferInstance
    have : (𝟙_ (DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology (D.geometricFiber X₀).left)
          Ab.{u + 1})
          (padicSubfieldRingObj (D.geometricFiber X₀).left l
            (condensedComparisonBaseStage l))))).IsGE 0 :=
      DerivedCategory.TStructure.t.isGE_of_iso (DerivedCategory.singleFunctorObjUnitIso _) 0
    -- Stating the Push component with the theorem's own `𝟙_` and reading `M := _` off it
    -- keeps elaboration fast; matching the theorem directly against the unfolded
    -- definition, or elaborating `𝟙_ _` as a separate argument, cost 27-47 s.
    have hpush : IsIso ((CondensedRing.derivedPushHom
      (Profinite.padicSubfieldRingObjToPadicAlgCl l
        (condensedComparisonBaseStage l)) (D.geometricFiber X₀).hom).app (𝟙_ _)) :=
      isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_app_of_isGE l
        (D.geometricFiber X₀).hom (condensedComparisonBaseStage l) _ 0
    exact IsIso.comp_isIso' (isIso_condensedPointScalarComparison l Ω D.k _)
      (Functor.map_isIso _ _)
  · exact condensed_derived_coefficient_frobenius_compatibility_aux l Ω D hl X₀ d hX


end PadicComparison

end WeilConjectures
