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
import Sheaf.AlgebraicGeometry.SupportedKummerScalarSourceData
import Sheaf.AlgebraicGeometry.SupportedKummerScalarSourceNaturality

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
set_option backward.isDefEq.respectTransparency false

universe u u₁ u₂ v₁ v₂ w₁ w₂

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

private theorem supportedHasSheafify (R : Type (u + 1)) [CommRing R]
    (T : Scheme.{u}) : HasSheafify T.smallEtaleTopology (ModuleCat.{u + 1} R) :=
  GrothendieckTopology.hasSheafify_smallEtaleTopology (ModuleCat.{u + 1} R) T

attribute [local instance 2000] supportedHasSheafify

private theorem supportedHasWeakSheafify (R : Type (u + 1)) [CommRing R]
    (T : Scheme.{u}) : HasWeakSheafify T.smallEtaleTopology (ModuleCat.{u + 1} R) :=
  (supportedHasSheafify R T).isRightAdjoint

attribute [local instance 2100] supportedHasWeakSheafify


set_option backward.isDefEq.respectTransparency false in
private lemma coefficientUnitModule_eq {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (η : ordinaryFiniteConstant R D ⟶
      (Sheaf.restrictScalars D.smallEtaleTopology φ).obj (ordinaryFiniteConstant S D))
    (hη : ∀ (U : D.Etaleᵒᵖ) (r : R), η.hom.app U
      ((toSheafify D.smallEtaleTopology
        ((Functor.const D.Etaleᵒᵖ).obj (ModuleCat.of R R))).app U r) =
      (toSheafify D.smallEtaleTopology
        ((Functor.const D.Etaleᵒᵖ).obj (ModuleCat.of S S))).app U (φ r)) :
    (lowerStar (ModuleCat.{u + 1} R) i).map η ≫
      (lowerStarCompRestrictScalarsIso φ i).inv.app (ordinaryFiniteConstant S D) =
      coefficientUnitModule φ i := by
  unfold coefficientUnitModule
  congr 1
  apply congrArg (lowerStar (ModuleCat.{u + 1} R) i).map
  apply ((constantSheafAdj D.smallEtaleTopology (ModuleCat.{u + 1} R)
    (MorphismProperty.Over.mkIdTerminal _ _)).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  rw [Adjunction.homEquiv_unit]
  change η.hom.app (op (Scheme.Etale.mk (𝟙 D)))
      (((constantSheafAdj D.smallEtaleTopology (ModuleCat.{u + 1} R)
        (MorphismProperty.Over.mkIdTerminal _ _)).unit.app (ModuleCat.of R R)) r) = _
  change η.hom.app (op (Scheme.Etale.mk (𝟙 D)))
      (((constantSheafAdj D.smallEtaleTopology (ModuleCat.{u + 1} R)
        (MorphismProperty.Over.mkIdTerminal _ _)).unit.app (ModuleCat.of R R)) r) =
    φ r • (((constantSheafAdj D.smallEtaleTopology (ModuleCat.{u + 1} S)
      (MorphismProperty.Over.mkIdTerminal _ _)).unit.app (ModuleCat.of S S)) (1 : S))
  have hunit (B : Type (u + 1)) [CommRing B] :
      (constantSheafAdj D.smallEtaleTopology (ModuleCat.{u + 1} B)
        (MorphismProperty.Over.mkIdTerminal _ _)).unit.app (ModuleCat.of B B) =
      (toSheafify D.smallEtaleTopology
        ((Functor.const D.Etaleᵒᵖ).obj (ModuleCat.of B B))).app
          (op (Scheme.Etale.mk (𝟙 D))) := by
    simp only [constantSheafAdj, Adjunction.comp_unit_app,
      constantPresheafAdj_unit_app, sheafificationAdjunction_unit_app]
    rfl
  rw [hunit R, hunit S]
  exact (hη (op (Scheme.Etale.mk (𝟙 D))) r).trans (by
    rw [← map_smul]
    congr 1
    exact (mul_one (φ r)).symm)

/-- An invertible adjunct gives a universal arrow to the right adjoint. -/
private lemma bijective_of_iso_adjunct
    {C : Type*} [Category C] {B : Type*} [Category B]
    {L : C ⥤ B} {U : B ⥤ C} (a : L ⊣ U)
    {X : C} {Y : B} (η : X ⟶ U.obj Y)
    (c : L.obj X ⟶ Y) [hcIso : IsIso c] (hc : a.homEquiv X Y c = η) (K : B) :
    Function.Bijective (fun f : Y ⟶ K ↦ η ≫ U.map f) := by
  have h := (a.homEquiv X K).bijective.comp
    ((asIso c).symm.homFromEquiv (Z := K)).bijective
  convert h using 1
  funext f
  exact (a.homEquiv_naturality_right c f).trans (by rw [hc]) |>.symm

/-- Build the degree-zero universal property from the invertible specified adjunct. -/
private lemma exactScalarUnit_of_iso_adjunct
    {C : Type u₁} [Category.{v₁} C] [CategoryTheory.Abelian C]
    [HasDerivedCategory.{w₁} C]
    {B : Type u₂} [Category.{v₂} B] [CategoryTheory.Abelian B]
    [HasDerivedCategory.{w₂} B]
    (V : B ⥤ C) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    {L : DerivedCategory C ⥤ DerivedCategory B} (a : L ⊣ V.mapDerivedCategory)
    {F : C} {G : B} (η : F ⟶ V.obj G)
    (c : L.obj ((DerivedCategory.singleFunctor C 0).obj F) ⟶
      (DerivedCategory.singleFunctor B 0).obj G) [hcIso : IsIso c]
    (hc : a.homEquiv _ _ c = exactDerivedScalarUnitMap V η) : ExactDerivedScalarUnit V F G η := by
  constructor
  intro K
  exact bijective_of_iso_adjunct a _ c hc K

private lemma exactScalarUnit_congr
    {C : Type u₁} [Category.{v₁} C] [CategoryTheory.Abelian C]
    [HasDerivedCategory.{w₁} C]
    {B : Type u₂} [Category.{v₂} B] [CategoryTheory.Abelian B]
    [HasDerivedCategory.{w₂} B]
    (V : B ⥤ C) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    {F : C} {G : B} {η η' : F ⟶ V.obj G} (h : η = η')
    (h' : ExactDerivedScalarUnit V F G η') : ExactDerivedScalarUnit V F G η := by
  subst η'
  exact h'

private lemma coefficientUnitDerived_eq_scalarMap
    {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i] :
    coefficientUnitDerived φ i =
      exactDerivedScalarUnitMap (Sheaf.restrictScalars T.smallEtaleTopology φ)
        (coefficientUnitModule φ i) := rfl

private lemma coefficientComparison_adjunct
    {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i] :
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)).homEquiv
      (supportedConstantDerived (A := R) i) (supportedConstantDerived (A := S) i)
      (supportedCoefficientComparison φ i) = coefficientUnitDerived φ i :=
  (Equiv.apply_symm_apply _ _)

private lemma coefficientUnitModule_scalarUnit
    {R S : Type (u + 1)} [CommRing R] [CommRing S] [Finite R] [Finite S]
    (φ : R →+* S) {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i] :
    SupportedDerivedScalarUnit φ T
      (supportedConstantModule (A := R) i) (supportedConstantModule (A := S) i)
      (coefficientUnitModule φ i) := by
  let a := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)
  exact exactScalarUnit_of_iso_adjunct
    (Sheaf.restrictScalars T.smallEtaleTopology φ) a (coefficientUnitModule φ i)
    (supportedCoefficientComparison φ i)
    (hcIso := (geoCartierCoeffExtension i φ (RingHom.id S)).1)
    ((coefficientComparison_adjunct φ i).trans (coefficientUnitDerived_eq_scalarMap φ i))

private lemma supported_scalar_finite
    {R S : Type (u + 1)} [CommRing R] [CommRing S] [Finite R] [Finite S]
    (φ : R →+* S) {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (η : ordinaryFiniteConstant R D ⟶
      (Sheaf.restrictScalars D.smallEtaleTopology φ).obj (ordinaryFiniteConstant S D))
    (hη : ∀ (U : D.Etaleᵒᵖ) (r : R), η.hom.app U
      ((toSheafify D.smallEtaleTopology
        ((Functor.const D.Etaleᵒᵖ).obj (ModuleCat.of R R))).app U r) =
      (toSheafify D.smallEtaleTopology
        ((Functor.const D.Etaleᵒᵖ).obj (ModuleCat.of S S))).app U (φ r)) :
    SupportedDerivedScalarUnit φ T
      ((lowerStar (ModuleCat.{u + 1} R) i).obj (ordinaryFiniteConstant R D))
      ((lowerStar (ModuleCat.{u + 1} S) i).obj (ordinaryFiniteConstant S D))
      ((lowerStar (ModuleCat.{u + 1} R) i).map η ≫
        (lowerStarCompRestrictScalarsIso φ i).inv.app (ordinaryFiniteConstant S D)) := by
  exact exactScalarUnit_congr (Sheaf.restrictScalars T.smallEtaleTopology φ)
    (coefficientUnitModule_eq φ i η hη) (coefficientUnitModule_scalarUnit φ i)

/-- Transport a universal coefficient map through a commutative square of isomorphisms. -/
private lemma bijective_of_unit_square
    {C : Type*} [Category C] {B : Type*} [Category B] (U : B ⥤ C)
    {X X' : C} {Y Y' : B} (e : X ≅ X') (d : Y ≅ Y')
    (η : X ⟶ U.obj Y) (η' : X' ⟶ U.obj Y')
    (h : η ≫ U.map d.hom = e.hom ≫ η') {K : B}
    (hb : Function.Bijective (fun f : Y' ⟶ K ↦ η' ≫ U.map f)) :
    Function.Bijective (fun f : Y ⟶ K ↦ η ≫ U.map f) := by
  have hc := (e.symm.homFromEquiv (Z := U.obj K)).bijective.comp
    (hb.comp (d.homFromEquiv (Z := K)).bijective)
  convert hc using 1
  funext f
  change η ≫ U.map f = e.hom ≫ (η' ≫ U.map (d.inv ≫ f))
  rw [U.map_comp, ← Category.assoc, ← h]
  simp only [Category.assoc, ← U.map_comp]
  rw [← Category.assoc d.hom d.inv f, d.hom_inv_id, Category.id_comp]

/-- A natural comparison transports a commuting unit square to the target categories. -/
private lemma bijective_of_natural_unit_square
    {C : Type*} [Category C] {B : Type*} [Category B]
    {CD : Type*} [Category CD] {BD : Type*} [Category BD]
    (P : C ⥤ CD) (Q : B ⥤ BD) (V : B ⥤ C) (W : BD ⥤ CD)
    (a : Q ⋙ W ≅ V ⋙ P)
    {F F' : C} {G G' : B} (e : F ≅ F') (d : G ≅ G')
    (η : F ⟶ V.obj G) (η' : F' ⟶ V.obj G')
    (h : η ≫ V.map d.hom = e.hom ≫ η') (K : BD)
    (hb : Function.Bijective (fun f : Q.obj G' ⟶ K ↦
      P.map η' ≫ a.inv.app G' ≫ W.map f)) :
    Function.Bijective (fun f : Q.obj G ⟶ K ↦
      P.map η ≫ a.inv.app G ≫ W.map f) := by
  have hh : (P.map η ≫ a.inv.app G) ≫ W.map (Q.map d.hom) =
      P.map e.hom ≫ (P.map η' ≫ a.inv.app G') := by
    have hn := a.inv.naturality d.hom
    dsimp only [Functor.comp_map] at hn
    rw [Category.assoc, ← hn, ← Category.assoc, ← P.map_comp, h,
      P.map_comp, Category.assoc]
  have hb' : Function.Bijective (fun f : Q.obj G' ⟶ K ↦
      (P.map η' ≫ a.inv.app G') ≫ W.map f) := by
    simpa only [Category.assoc] using hb
  have hc := bijective_of_unit_square (C := CD) (B := BD) W (P.mapIso e) (Q.mapIso d)
    (P.map η ≫ a.inv.app G) (P.map η' ≫ a.inv.app G') hh (K := K) hb'
  simpa only [Category.assoc] using hc

private lemma exactScalarUnit_transport
    {C : Type u₁} [Category.{v₁} C] [CategoryTheory.Abelian C]
    [HasDerivedCategory.{w₁} C]
    {B : Type u₂} [Category.{v₂} B] [CategoryTheory.Abelian B]
    [HasDerivedCategory.{w₂} B]
    (V : B ⥤ C) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    {F F' : C} {G G' : B} (e : F ≅ F') (d : G ≅ G')
    (η : F ⟶ V.obj G) (η' : F' ⟶ V.obj G')
    (h : η ≫ V.map d.hom = e.hom ≫ η')
    (h' : ExactDerivedScalarUnit V F' G' η') : ExactDerivedScalarUnit V F G η := by
  constructor
  intro K
  have hb := h'.bijective K
  simp only [exactDerivedScalarUnitMap, Category.assoc] at hb ⊢
  exact bijective_of_natural_unit_square
    (DerivedCategory.singleFunctor C 0) (DerivedCategory.singleFunctor B 0)
    V V.mapDerivedCategory (V.mapDerivedCategorySingleFunctor 0) e d η η' h K
    hb

private lemma scalarUnit_transport {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (T : Scheme.{u})
    {F F' : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)}
    {G G' : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} S)}
    (e : F ≅ F') (d : G ≅ G')
    (η : F ⟶ (Sheaf.restrictScalars T.smallEtaleTopology φ).obj G)
    (η' : F' ⟶ (Sheaf.restrictScalars T.smallEtaleTopology φ).obj G')
    (h : η ≫ (Sheaf.restrictScalars T.smallEtaleTopology φ).map d.hom = e.hom ≫ η')
    (h' : SupportedDerivedScalarUnit φ T F' G' η') :
    SupportedDerivedScalarUnit φ T F G η := by
  exact exactScalarUnit_transport (Sheaf.restrictScalars T.smallEtaleTopology φ)
    e d η η' h h'

private lemma constant_scalar_finite
    {R S : Type (u + 1)} [CommRing R] [CommRing S] [Finite R] [Finite S]
    (φ : R →+* S) (T : Scheme.{u})
    (η : ordinaryFiniteConstant R T ⟶
      (Sheaf.restrictScalars T.smallEtaleTopology φ).obj (ordinaryFiniteConstant S T))
    (hη : ∀ (U : T.Etaleᵒᵖ) (r : R), η.hom.app U
      ((toSheafify T.smallEtaleTopology
        ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of R R))).app U r) =
      (toSheafify T.smallEtaleTopology
        ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of S S))).app U (φ r)) :
    SupportedDerivedScalarUnit φ T
      (ordinaryFiniteConstant R T) (ordinaryFiniteConstant S T) η := by
  have h := supported_scalar_finite φ (𝟙 T) η hη
  have hcomm := supported_kummer_scalar_source_naturality φ (𝟙 T) η η hη hη
  have hR : IsIso (supportedConstantUnit R (𝟙 T)) := by
    unfold supportedConstantUnit
    rw [Adjunction.homEquiv_unit]
    infer_instance
  have hS : IsIso (supportedConstantUnit S (𝟙 T)) := by
    unfold supportedConstantUnit
    rw [Adjunction.homEquiv_unit]
    infer_instance
  exact scalarUnit_transport φ T (asIso (supportedConstantUnit R (𝟙 T)))
    (asIso (supportedConstantUnit S (𝟙 T))) η _ hcomm h


/-- The canonical coefficient map from the lifted residue ring to `A`.
Source: blueprint lem-amb-cartier-kummer-map, final scalar-extension paragraph;
Stacks, sites-cohomology, Tag 06YY (blueprint: lem-asd-supported-kummer-scalar-source).
It is the scalar map of `def-asd-finite-etale-tate-twist`, composed with the canonical
`ULift` ring equivalence. -/
def supportedScalarMap (N : ℕ) (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0) :
    ULift.{u + 1} (ZMod N) →+* A :=
  (Scheme.finiteEtaleTwistScalar N A hA).comp ULift.ringEquiv.toRingHom

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

Proof plan (the six steps of the node):
1. A closed immersion is finite: locally it is Spec(R/I) over Spec(R), and R/I is
   generated by one (`def-weil-closed-immersion`, `def-weil-finite-integral-morphism`).
   Its geometric fibre is empty or a singleton. The normalized finite-stalk formula
   (`lem-weil-pbc-finite-stalk-formula-restriction`) and constant-stalk identification
   (`lem-weil-pbc-constant-sheaf-geometric-stalk`) give stalks of E = i_*Λ_D equal
   to Λ on D and zero off D, with the indicated coefficient action; similarly for A.
2. Finite direct image is exact (`sk-lem-pbc-finite`). Forgetting the module action
   computes kernels and cokernels, so this remains true for module sheaves. Apply
   `lem-weil-pbc-exact-functor-derived-functor`: E[0] and (i_*A_D)[0] compute Ri_*;
   the canonical comparisons are natural in coefficient maps and units.
3. E[0] is K-flat (`def-pc-kflat-complex`, `def-kun-derived-tensor`): for an acyclic
   complex C, the degree n term of C tensor E is C^n tensor E. Tensor-stalk
   compatibility (`lem-pod-etale-stalk-tensor-scalar`) identifies the stalk complex
   with C_stalk tensor E_stalk, including differentials. The tensor over the constant
   ring sheaf and tensor over Λ have the same stalks, since the constant ring's stalk
   is Λ and filtered colimits commute with tensor. Step 1 makes this complex C_stalk
   or zero. Exactness of stalks (`prop-weil-pbc-geometric-stalks-exact`) and their
   conservativity (`lemma-weil-pbc-geometric-stalk-conservative`) detect acyclicity.
   The same argument makes Λ_T[0] K-flat, and applies to constants on D.
4. Construct m : E tensor A_T → i_*A_D on an etale W by s tensor a ↦ c(s) a|_D,
   where c = i_*(Λ_D → A_D). It is balanced and commutes with restrictions, hence
   descends by `def-pur-sheaf-tensor-product` and `def-weil-pbc-direct-image`.
   Pure tensors generate locally, so m is the unique A-linear extension of c.
   The tensor-stalk and normalized finite-stalk formulas identify m on D with
   Λ tensor A → A, λ tensor a ↦ λa, inverse a ↦ 1 tensor a; off D both sides
   vanish. Stalk conservativity makes m an isomorphism.
5. Compute `lem-pur-derived-change-of-rings` with the identity K-flat resolution
   from step 3, then combine m with step 2. This gives the derived scalar-unit
   universal properties for the normalized maps on D, T, and the pushforward.
   Their ordinary representatives are the specified coefficient maps, rather than
   an unspecified isomorphism; no flatness of A is used.
6. Both ends of Λ_T → E are K-flat. Its scalar extension followed by m sends a
   to m(η_Λ(1) tensor a) = a|_D, exactly the unit A_T → i_*A_D. Naturality of
   step 2 makes this the derived unit too. `supportedConstantUnit` records the
   adjunction unit, and `lowerStarCompRestrictScalarsIso` supplies the objectwise
   coefficient comparison, giving the final equality.
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
  have : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hN)⟩
  obtain ⟨ηD, hDgen⟩ := exists_supported_constant_scalar_map (supportedScalarMap N A hA) D
  obtain ⟨ηT, hTgen⟩ := exists_supported_constant_scalar_map (supportedScalarMap N A hA) T
  refine ⟨ηD, ηT, hDgen, hTgen, ?_, ?_, ?_, ?_⟩
  · exact constant_scalar_finite (supportedScalarMap N A hA) D ηD hDgen
  · exact supported_scalar_finite (supportedScalarMap N A hA) i ηD hDgen
  · exact constant_scalar_finite (supportedScalarMap N A hA) T ηT hTgen
  · exact supported_kummer_scalar_source_naturality
      (supportedScalarMap N A hA) i ηD ηT hDgen hTgen

end AlgebraicGeometry.Etale
