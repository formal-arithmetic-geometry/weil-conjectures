/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q98
-/
module

public import Sheaf.AlgebraicGeometry.OrdinarySupportedKummerScalar
public import Sheaf.AlgebraicGeometry.OrdinarySupportedKummerBoundary
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer
public import WeilConjectures.SixFunctors.BaseChange.RestrictScalars
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Mathlib.AlgebraicGeometry.Scheme

import Sheaf.SixFunctors.GeoCartierCoeffExtension
import WeilConjectures.ConstructibleSheaf.FinitePushforward.ConstantUnit

/-!
# Derived scalar extension of a closed supported constant sheaf

Source: Stacks Project, `etale-cohomology.tex`, Tags 03QP and 03Q1, together with
sites-cohomology derived change of rings (blueprint: lem-asd-supported-kummer-scalar-source).

The theorem records the canonical scalar-extension comparison by the universal property
of `SupportedDerivedScalarUnit`.  The displayed composite is the coefficient unit on the
closed support transported through the canonical restriction-of-scalars/pushforward
comparison.  No flatness assumption on the new coefficient ring occurs.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The canonical coefficient map from the lifted residue ring to `A`.
Source: blueprint lem-amb-cartier-kummer-map, final scalar-extension paragraph;
Stacks, sites-cohomology, Tag 06YY (blueprint: lem-asd-supported-kummer-scalar-source).
It is the scalar map of `def-asd-finite-etale-tate-twist`, composed with the canonical
`ULift` ring equivalence. -/
def supportedScalarMap (N : ℕ) (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0) :
    ULift.{u + 1} (ZMod N) →+* A :=
  (Scheme.finiteEtaleTwistScalar N A hA).comp ULift.ringEquiv.toRingHom

@[irreducible] private def scalarConstantOn
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {R S : Type (u + 1)} [CommRing R] [CommRing S]
    [HasWeakSheafify J (ModuleCat.{u + 1} R)]
    [HasWeakSheafify J (ModuleCat.{u + 1} S)]
    {t : C} (hX : IsTerminal t) (φ : R →+* S) :
    (constantSheaf J (ModuleCat.{u + 1} R)).obj (ModuleCat.of R R) ⟶
      (Sheaf.restrictScalars J φ).obj
        ((constantSheaf J (ModuleCat.{u + 1} S)).obj (ModuleCat.of S S)) :=
  let G := (Sheaf.restrictScalars J φ).obj
    ((constantSheaf J (ModuleCat.{u + 1} S)).obj (ModuleCat.of S S))
  let x : G.obj.obj (op t) :=
    (constantSheafAdj J (ModuleCat.{u + 1} S) hX).unit.app
      (ModuleCat.of S S) (1 : S)
  (constantSheafAdj J (ModuleCat.{u + 1} R) hX).homEquiv _ _ |>.symm
    (ModuleCat.ofHom (Y := G.obj.obj (op t))
      (LinearMap.toSpanSingleton R (G.obj.obj (op t)) x))

private lemma scalarConstantOn_apply
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {R S : Type (u + 1)} [CommRing R] [CommRing S]
    [HasWeakSheafify J (ModuleCat.{u + 1} R)]
    [HasWeakSheafify J (ModuleCat.{u + 1} S)]
    {t : C} (hX : IsTerminal t) (φ : R →+* S) (U : Cᵒᵖ) (r : R) :
    (scalarConstantOn J hX φ).hom.app U
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (ModuleCat.of R R))).app U r) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj (ModuleCat.of S S))).app U (φ r) := by
  let σR := toSheafify J
    ((Functor.const Cᵒᵖ).obj (ModuleCat.of R R))
  let σS := toSheafify J
    ((Functor.const Cᵒᵖ).obj (ModuleCat.of S S))
  let G := (Sheaf.restrictScalars J φ).obj
    ((constantSheaf J (ModuleCat.{u + 1} S)).obj (ModuleCat.of S S))
  let aR := constantSheafAdj J (ModuleCat.{u + 1} R) hX
  let aS := constantSheafAdj J (ModuleCat.{u + 1} S) hX
  let x : G.obj.obj (op t) := aS.unit.app (ModuleCat.of S S) (1 : S)
  let h : ModuleCat.of R R ⟶ G.obj.obj (op t) :=
    ModuleCat.ofHom (Y := G.obj.obj (op t)) (LinearMap.toSpanSingleton R _ x)
  have hk : aR.unit.app (ModuleCat.of R R) ≫
      (scalarConstantOn J hX φ).hom.app (op t) = h := by
    change aR.homEquiv _ _ (scalarConstantOn J hX φ) = h
    unfold scalarConstantOn aR
    rw [Equiv.apply_symm_apply]
  have huR : aR.unit.app (ModuleCat.of R R) = σR.app (op t) := by rfl
  have huS : aS.unit.app (ModuleCat.of S S) = σS.app (op t) := by rfl
  have ht := congrArg (fun f : ModuleCat.of R R ⟶ G.obj.obj (op t) ↦ f r) hk
  rw [huR] at ht
  have hs : h r = σS.app (op t) (φ r) := by
    change (φ r) • (aS.unit.app (ModuleCat.of S S) (1 : S)) = _
    rw [← map_smul, smul_eq_mul, mul_one, huS]
    rfl
  have htop := ht.trans hs
  let f := (hX.from U.unop).op
  have hr := congrArg (fun g ↦ g r) (σR.naturality f)
  have hs' := congrArg (fun g ↦ g (φ r)) (σS.naturality f)
  have hm := congrArg (fun g ↦ g (σR.app (op t) r))
    ((scalarConstantOn J hX φ).hom.naturality f)
  change σR.app U r =
    ((constantSheaf J (ModuleCat.{u + 1} R)).obj (ModuleCat.of R R)).obj.map f
      (σR.app (op t) r) at hr
  change σS.app U (φ r) =
    ((constantSheaf J (ModuleCat.{u + 1} S)).obj (ModuleCat.of S S)).obj.map f
    (σS.app (op t) (φ r)) at hs'
  change (scalarConstantOn J hX φ).hom.app U (σR.app U r) = σS.app U (φ r)
  exact (congrArg ((scalarConstantOn J hX φ).hom.app U) hr).trans
    (hm.trans ((congrArg (G.obj.map f) htop).trans hs'.symm))

@[irreducible] private def scalarConstant {R S : Type (u + 1)}
    [CommRing R] [CommRing S] (φ : R →+* S) (X : Scheme.{u}) :
    ordinaryFiniteConstant R X ⟶
      (Sheaf.restrictScalars X.smallEtaleTopology φ).obj (ordinaryFiniteConstant S X) :=
  scalarConstantOn X.smallEtaleTopology (MorphismProperty.Over.mkIdTerminal _ _) φ

private lemma scalarConstant_apply {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (X : Scheme.{u}) (U : X.Etaleᵒᵖ) (r : R) :
    (scalarConstant φ X).hom.app U
      ((toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj
        (ModuleCat.of R R))).app U r) =
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj
        (ModuleCat.of S S))).app U (φ r) := by
  unfold scalarConstant
  exact scalarConstantOn_apply _ _ _ _ _

private lemma coefficientUnitModule_eq {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) {D X : Scheme.{u}} (i : D ⟶ X) [IsClosedImmersion i] :
    coefficientUnitModule φ i =
      (lowerStar (ModuleCat.{u + 1} R) i).map (scalarConstant φ D) ≫
        (lowerStarCompRestrictScalarsIso φ i).inv.app (ordinaryFiniteConstant S D) := by
  simp only [coefficientUnitModule, scalarConstant, scalarConstantOn,
    lowerStarRestrictScalarsIso, lowerStarCompRestrictScalarsIso,
    Iso.refl_inv, NatTrans.id_app]
  rfl

section Derived

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

-- Preserve the APIs of the chosen sheafification and derived localization.
attribute [local irreducible] constantSheaf HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.mapDerivedCategory
  Functor.mapDerivedCategorySingleFunctor DerivedCategory.singleFunctors

private lemma adjunct_bijective
    {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) {M : C} {N : D} (c : F.obj M ⟶ N) [hcIso : IsIso c]
    (p : M ⟶ G.obj N) (hc : adj.homEquiv M N c = p) (K : D) :
    Function.Bijective (fun f : N ⟶ K ↦ p ≫ G.map f) := by
  let e : (N ⟶ K) ≃ (F.obj M ⟶ K) :=
    { toFun := fun f ↦ c ≫ f
      invFun := fun f ↦ inv c ≫ f
      left_inv := by intro f; simp
      right_inv := by intro f; simp }
  have h : Function.Bijective (fun f : N ⟶ K ↦ adj.homEquiv M K (c ≫ f)) :=
    (adj.homEquiv M K).bijective.comp e.bijective
  convert h using 1
  funext f
  rw [adj.homEquiv_naturality_right, hc]

private lemma supportedScalar_baseChange
    {R S : Type (u + 1)} [CommRing R] [CommRing S] [Finite R] [Finite S]
    (φ : R →+* S) {D X : Scheme.{u}} (i : D ⟶ X) [IsClosedImmersion i] :
    Sheaf.IsDerivedBaseChange (coefficientUnitDerived φ i) := by
  let adj := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)
  have hc : IsIso (supportedCoefficientComparison φ i) :=
    (geoCartierCoeffExtension i φ (RingHom.id S)).1
  intro K
  exact adjunct_bijective
    (C := DerivedCategoryModule R X) (D := DerivedCategoryModule S X)
    adj (M := supportedConstantDerived (A := R) i)
    (N := supportedConstantDerived (A := S) i)
    (supportedCoefficientComparison φ i) (hcIso := hc) (coefficientUnitDerived φ i)
    ((adj.homEquiv _ _).apply_symm_apply (coefficientUnitDerived φ i)) K

private lemma supportedScalar_pushforward
    {R S : Type (u + 1)} [CommRing R] [CommRing S] [Finite R] [Finite S]
    (φ : R →+* S) {D X : Scheme.{u}} (i : D ⟶ X) [IsClosedImmersion i] :
    SupportedDerivedScalarUnit φ X (supportedConstantModule (A := R) i)
      (supportedConstantModule (A := S) i) (coefficientUnitModule φ i) := by
  unfold SupportedDerivedScalarUnit IsScalarExtensionUnit
  exact supportedScalar_baseChange φ i

private lemma unit_transport_eq
    {C D : Type*} [Category C] [Category D] (U : D ⥤ C)
    (P : C ⥤ C) (Q : D ⥤ D) (a : P ≅ 𝟭 C) (b : Q ≅ 𝟭 D)
    (e : Q ⋙ U ≅ U ⋙ P) {F : C} {G : D} (η : F ⟶ U.obj G)
    (η' : P.obj F ⟶ U.obj (Q.obj G))
    (hη : η' = P.map η ≫ e.inv.app G)
    (he : e.inv.app G ≫ U.map (b.hom.app G) = a.hom.app (U.obj G)) :
    a.inv.app F ≫ η' ≫ U.map (b.hom.app G) = η := by
  rw [hη, Category.assoc, he]
  have hn := a.inv.naturality η
  dsimp only [Functor.id_map] at hn
  rw [← Category.assoc, ← hn, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

private lemma scalarUnit_identity
    {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (X : Scheme.{u})
    [PreservesFiniteLimits (Sheaf.restrictScalars X.smallEtaleTopology φ)]
    [PreservesFiniteColimits (Sheaf.restrictScalars X.smallEtaleTopology φ)]
    (η : ordinaryFiniteConstant R X ⟶
      (Sheaf.restrictScalars X.smallEtaleTopology φ).obj (ordinaryFiniteConstant S X))
    (hη : coefficientUnitModule φ (𝟙 X) =
      (lowerStar (ModuleCat.{u + 1} R) (𝟙 X)).map η ≫
        (lowerStarCompRestrictScalarsIso φ (𝟙 X)).inv.app (ordinaryFiniteConstant S X))
    (h : SupportedDerivedScalarUnit φ X (supportedConstantModule (A := R) (𝟙 X))
      (supportedConstantModule (A := S) (𝟙 X)) (coefficientUnitModule φ (𝟙 X))) :
    SupportedDerivedScalarUnit φ X (ordinaryFiniteConstant R X)
      (ordinaryFiniteConstant S X) η := by
  let U := Sheaf.restrictScalars X.smallEtaleTopology φ
  let F := ordinaryFiniteConstant R X
  let G := ordinaryFiniteConstant S X
  let a := (lowerStarId (ModuleCat.{u + 1} R) X).app F
  let b := (lowerStarId (ModuleCat.{u + 1} S) X).app G
  have he : (lowerStarCompRestrictScalarsIso φ (𝟙 X)).inv.app G ≫ U.map b.hom =
      (lowerStarId (ModuleCat.{u + 1} R) X).hom.app (U.obj G) := by
    apply Sheaf.hom_ext
    ext V r
    rfl
  have hn : a.inv ≫ (coefficientUnitModule φ (𝟙 X)) ≫ U.map b.hom = η :=
    unit_transport_eq U (lowerStar (ModuleCat.{u + 1} R) (𝟙 X))
      (lowerStar (ModuleCat.{u + 1} S) (𝟙 X))
      (lowerStarId (ModuleCat.{u + 1} R) X) (lowerStarId (ModuleCat.{u + 1} S) X)
      (lowerStarCompRestrictScalarsIso φ (𝟙 X)) η (coefficientUnitModule φ (𝟙 X)) hη he
  unfold SupportedDerivedScalarUnit at h ⊢
  exact isScalarExtensionUnit_transport
    (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) 0)
    (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} S)) 0)
    (U.mapDerivedCategorySingleFunctor 0) a b (coefficientUnitModule φ (𝟙 X)) η hn h

private lemma scalarConstant_derived
    {R S : Type (u + 1)} [CommRing R] [CommRing S] [Finite R] [Finite S]
    (φ : R →+* S) (X : Scheme.{u}) :
    SupportedDerivedScalarUnit φ X (ordinaryFiniteConstant R X)
      (ordinaryFiniteConstant S X) (scalarConstant φ X) := by
  apply scalarUnit_identity φ X (scalarConstant φ X) (coefficientUnitModule_eq φ (𝟙 X))
  exact supportedScalar_pushforward φ (𝟙 X)

end Derived

private lemma supportedConstantUnit_apply
    (R : Type (u + 1)) [CommRing R] {D T : Scheme.{u}} (i : D ⟶ T)
    (V : T.Etale) (r : R) :
    (supportedConstantUnit R i).hom.app (op V)
      ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
        (ModuleCat.of R R))).app (op V) r) =
    (toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
      (ModuleCat.of R R))).app
      (op ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ i).obj V)) r := by
  have h : supportedConstantUnit R i = constantSheafUnit i (ModuleCat.of R R) := by
    simp only [supportedConstantUnit, Adjunction.homEquiv_unit, constantSheafUnit]
    rfl
  rw [h]
  exact constantSheafUnit_app_toSheafify i (ModuleCat.of R R) V r

private lemma scalarConstant_unit
    {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) {D T : Scheme.{u}} (i : D ⟶ T)
    (ηD : ordinaryFiniteConstant R D ⟶
      (Sheaf.restrictScalars D.smallEtaleTopology φ).obj (ordinaryFiniteConstant S D))
    (ηT : ordinaryFiniteConstant R T ⟶
      (Sheaf.restrictScalars T.smallEtaleTopology φ).obj (ordinaryFiniteConstant S T))
    (hD : ∀ (U : D.Etaleᵒᵖ) (r : R), ηD.hom.app U
      ((toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
        (ModuleCat.of R R))).app U r) =
      (toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
        (ModuleCat.of S S))).app U (φ r))
    (hT : ∀ (U : T.Etaleᵒᵖ) (r : R), ηT.hom.app U
      ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
        (ModuleCat.of R R))).app U r) =
      (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
        (ModuleCat.of S S))).app U (φ r)) :
    ηT ≫ (Sheaf.restrictScalars T.smallEtaleTopology φ).map (supportedConstantUnit S i) =
      supportedConstantUnit R i ≫ (lowerStar (ModuleCat.{u + 1} R) i).map ηD := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _
    ((Sheaf.restrictScalars T.smallEtaleTopology φ).obj
      ((lowerStar (ModuleCat.{u + 1} S) i).obj (ordinaryFiniteConstant S D))).property
  ext U
  change (supportedConstantUnit S i).hom.app U
      (ηT.hom.app U ((toSheafify T.smallEtaleTopology
        ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of R R))).app U (1 : R))) =
    ηD.hom.app (op ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ i).obj U.unop))
      ((supportedConstantUnit R i).hom.app U
        ((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of R R))).app U (1 : R)))
  rw [hT, supportedConstantUnit_apply, supportedConstantUnit_apply, hD]

private lemma scalarSource
    {R S : Type (u + 1)} [CommRing R] [CommRing S] [Finite R] [Finite S]
    (φ : R →+* S) (T : Scheme.{u}) {D : Scheme.{u}}
    (i : D ⟶ T) [IsClosedImmersion i] :
    ∃ (ηD : ordinaryFiniteConstant R D ⟶
        (Sheaf.restrictScalars D.smallEtaleTopology
          φ).obj
          (ordinaryFiniteConstant S D))
      (ηT : ordinaryFiniteConstant R T ⟶
        (Sheaf.restrictScalars T.smallEtaleTopology
          φ).obj
          (ordinaryFiniteConstant S T)),
      (∀ (U : D.Etaleᵒᵖ) (r : R),
        ηD.hom.app U
          ((toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
            (ModuleCat.of R R))).app U r) =
        (toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
          (ModuleCat.of S S))).app U (φ r)) ∧
      (∀ (U : T.Etaleᵒᵖ) (r : R),
        ηT.hom.app U
          ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
            (ModuleCat.of R R))).app U r) =
        (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
          (ModuleCat.of S S))).app U (φ r)) ∧
      SupportedDerivedScalarUnit
          φ D
          (ordinaryFiniteConstant R D)
          (ordinaryFiniteConstant S D) ηD ∧
      SupportedDerivedScalarUnit
          φ T
          ((lowerStar (ModuleCat.{u + 1} R) i).obj
            (ordinaryFiniteConstant R D))
          ((lowerStar (ModuleCat.{u + 1} S) i).obj (ordinaryFiniteConstant S D))
          ((lowerStar (ModuleCat.{u + 1} R) i).map ηD ≫
            (lowerStarCompRestrictScalarsIso
              φ i).inv.app
              (ordinaryFiniteConstant S D)) ∧
      SupportedDerivedScalarUnit
          φ T
          (ordinaryFiniteConstant R T)
          (ordinaryFiniteConstant S T) ηT ∧
      ηT ≫
          (Sheaf.restrictScalars T.smallEtaleTopology
            φ).map
            (supportedConstantUnit S i) =
        supportedConstantUnit R i ≫
          (lowerStar (ModuleCat.{u + 1} R) i).map ηD ≫
          (lowerStarCompRestrictScalarsIso
            φ i).inv.app
            (ordinaryFiniteConstant S D) := by
  refine ⟨scalarConstant φ D, scalarConstant φ T, scalarConstant_apply φ D,
    scalarConstant_apply φ T, scalarConstant_derived φ D, ?_,
    scalarConstant_derived φ T, ?_⟩
  · have h := supportedScalar_pushforward φ i
    rw [coefficientUnitModule_eq] at h
    simpa only [supportedConstantModule] using h
  · change scalarConstant φ T ≫
        (Sheaf.restrictScalars T.smallEtaleTopology φ).map (supportedConstantUnit S i) =
      supportedConstantUnit R i ≫
        (lowerStar (ModuleCat.{u + 1} R) i).map (scalarConstant φ D)
    exact scalarConstant_unit φ i (scalarConstant φ D) (scalarConstant φ T)
      (scalarConstant_apply φ D) (scalarConstant_apply φ T)


/--
For a finite coefficient ring killed by `N`, the supported constant scalar extension is
characterized simultaneously on the closed support and on the ambient scheme.  The
maps `ηD` and `ηT` are the coefficient units; their derived universal properties state
that the displayed objects are the derived scalar extensions.  The final equality is
naturality of the unit under the closed pushforward. The first two conjuncts fix
both maps on constant-presheaf generators, excluding a rescaling of the units.
This is the canonical comparison
of `Ri_* Λ_D ⊗ᴸ_{Λ_T} A_T` with `Ri_* A_D`, expressed in the ordinary unbounded derived
module categories, and does not assume that `A` is flat over `Λ`.

Source: Stacks Project, `etale-cohomology.tex`, Tags 03QP and 03Q1, and
sites-cohomology derived change of rings (blueprint: lem-asd-supported-kummer-scalar-source).

Proof:
1. Construct the coefficient maps by the constant-sheaf adjunction, sending the generator
   one to the constant section one. The adjunction equation and restriction naturality
   prove the specified formulas on constant-presheaf generators.
2. Use `geoCartierCoeffExtension` for the closed immersion and the coefficient map.
   Its comparison is the adjunct of the direct image of the constructed map. Since the
   comparison is an isomorphism, precomposition with it and the adjunction hom equivalence
   give the required derived scalar-unit universal property.
3. Apply the same comparison to the identity immersion on each scheme. Transport along
   the canonical identity-pushforward isomorphisms and the compatibility of exact
   restriction with the degree-zero single functor to obtain the constant scalar units.
4. The proved `constantSheafUnit_app_toSheafify` formula identifies the pushforward unit
   on each constant generator. Both composites in the final square send a generator r
   to the constant section phi(r) on the pullback. Sheafification uniqueness proves their
   equality. Finally specialize to the finite ring `ULift (ZMod N)` and `A`.
This reuses the general canonical comparison instead of repeating its stalk and K-flat
argument, and keeps the coefficient maps and the adjunction unit explicitly normalized.
-/
theorem supported_kummer_scalar_source
    (T : Scheme.{u}) (N : ℕ) (hN : 1 ≤ N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    {D : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i] :
    ∃ (ηD : ordinaryFiniteConstant (ULift.{u + 1} (ZMod N)) D ⟶
        (Sheaf.restrictScalars D.smallEtaleTopology
          (supportedScalarMap N A hA)).obj
          (ordinaryFiniteConstant A D))
      (ηT : ordinaryFiniteConstant (ULift.{u + 1} (ZMod N)) T ⟶
        (Sheaf.restrictScalars T.smallEtaleTopology
          (supportedScalarMap N A hA)).obj
          (ordinaryFiniteConstant A T)),
      (∀ (U : D.Etaleᵒᵖ) (r : ULift.{u + 1} (ZMod N)),
        ηD.hom.app U
          ((toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
            (ModuleCat.of (ULift.{u + 1} (ZMod N)) (ULift.{u + 1} (ZMod N))))).app U r) =
        (toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
          (ModuleCat.of A A))).app U (supportedScalarMap N A hA r)) ∧
      (∀ (U : T.Etaleᵒᵖ) (r : ULift.{u + 1} (ZMod N)),
        ηT.hom.app U
          ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
            (ModuleCat.of (ULift.{u + 1} (ZMod N)) (ULift.{u + 1} (ZMod N))))).app U r) =
        (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
          (ModuleCat.of A A))).app U (supportedScalarMap N A hA r)) ∧
      SupportedDerivedScalarUnit
          (supportedScalarMap N A hA) D
          (ordinaryFiniteConstant (ULift.{u + 1} (ZMod N)) D)
          (ordinaryFiniteConstant A D) ηD ∧
      SupportedDerivedScalarUnit
          (supportedScalarMap N A hA) T
          ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N))) i).obj
            (ordinaryFiniteConstant (ULift.{u + 1} (ZMod N)) D))
          ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
          ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N))) i).map ηD ≫
            (lowerStarCompRestrictScalarsIso
              (supportedScalarMap N A hA) i).inv.app
              (ordinaryFiniteConstant A D)) ∧
      SupportedDerivedScalarUnit
          (supportedScalarMap N A hA) T
          (ordinaryFiniteConstant (ULift.{u + 1} (ZMod N)) T)
          (ordinaryFiniteConstant A T) ηT ∧
      ηT ≫
          (Sheaf.restrictScalars T.smallEtaleTopology
            (supportedScalarMap N A hA)).map
            (supportedConstantUnit A i) =
        supportedConstantUnit (ULift.{u + 1} (ZMod N)) i ≫
          (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N))) i).map ηD ≫
          (lowerStarCompRestrictScalarsIso
            (supportedScalarMap N A hA) i).inv.app
            (ordinaryFiniteConstant A D) := by
  have : NeZero N := ⟨Nat.ne_of_gt hN⟩
  exact scalarSource (supportedScalarMap N A hA) T i

end AlgebraicGeometry.Etale
