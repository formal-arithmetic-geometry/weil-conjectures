/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.CurrentPurityConventions.Setting.CurrentPurityConventions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FormalClosedSupportGeneralField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.KrullDimension.Basic

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.ClosedImmersion
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.CategoryTheory.Adjunction.SmoothDivisorNativeUnitNormalization

import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothDivisorNativeFiniteUnit
import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothDivisorNativeCoefficientUnits
import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedSupportTriangle
import WeilConjectures.AlgebraicGeometry.SmoothDivisorLowSupport
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.Algebra.CharP.Basic

/-!
# Native bottom-degree descent for a smooth Cartier divisor

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-an/lem-pur-divisor-class.proof.md, proof (b),
descent to Cartier charts before Thom purity
(blueprint: lem-pur-smooth-divisor-native-bottom).

The general section helpers are moved unchanged from ZeroSectionBottomCoefficients,
which publicly re-exports this module. No zero-section purity assertion is imported.
A free module on an open representable is extension by zero of the coefficient unit.
Thus closed direct image of that module represents the supported Hom group on the open.
The bottom comparison is the closed-support adjunct, followed by H^0 and evaluation
at the identity generator. It specifies a map before asserting its bijectivity.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilConjectures.PurityFiniteSetting

private theorem nativeBottom_prime_unit (P : PurityFiniteSetting.{u}) :
    IsUnit (P.coefficients.l : P.field.k) := by
  classical
  let : Fintype P.field.k₀ := Fintype.ofFinite _
  let : Fact P.field.p.Prime := ⟨P.field.prime⟩
  let : CharP P.field.k₀ P.field.p := charP_of_card_eq_prime_pow (f := P.field.a)
    (by simpa only [Nat.card_eq_fintype_card] using
      P.field.card_base.trans P.field.cardinality_eq)
  let : CharP P.field.k P.field.p := charP_of_injective_algebraMap' P.field.k₀ P.field.p
  exact isUnit_iff_ne_zero.mpr (CharP.cast_ne_zero_of_ne_of_prime P.field.k
    (Fact.out : P.coefficients.l.Prime) P.coefficients.different.symm)

set_option maxHeartbeats 1000000 in
-- The derived support triangle involves several large sheaf-category adjunctions.
private theorem etale_bottom_unit_of_low_support
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {D T V : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (j : V ⟶ T) [IsOpenImmersion j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hv : ∀ q : ℤ, q < 2 → IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((Etale.sectionsWithSupport (ModuleCat.{u + 1} A) j).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj M)))) :
    IsIso ((DerivedCategory.homologyFunctor _ 0).map
      ((Etale.mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit.app
        ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  let C := ModuleCat.{u + 1} A
  let S := Etale.sectionsWithSupport C j
  let E := Etale.closedUpperShriek C i j
  let R := Etale.lowerStar C i
  let : R.PreservesHomology := {}
  let : E.PreservesKInjectiveComplexes :=
    (Etale.lowerStarClosedUpperShriekAdjunction C i j hij).preservesKInjectiveComplexes
  let u := Functor.whiskerLeft S (Etale.upperStarLowerStarAdjunction C i).unit
  have (N : Sheaf T.smallEtaleTopology C) : IsIso (u.app N) :=
    Etale.isIso_upperStarLowerStarAdjunction_unit_app_of_isZero C i j hij
      (Etale.isZero_upperStar_sectionsWithSupport C j N)
  let : IsIso u := NatIso.isIso_of_isIso_app u
  let eS : S ≅ E ⋙ R := asIso u
  let adji := Etale.derivedLowerStarClosedUpperShriekAdjunction (R := A) i j hij
  let eR := (Adjunction.ofIsLeftAdjoint R.rightDerivedFunctor).rightAdjointUniq adji
  let K := (DerivedCategory.singleFunctor _ 0).obj M
  obtain ⟨δ, hδ⟩ := Etale.exists_etale_closedSupportTriangle A i j hij
  let Δ := Pretriangulated.Triangle.mk
    ((Adjunction.ofIsLeftAdjoint R.rightDerivedFunctor).counit.app K)
    ((Etale.mapDerivedUpperStarLowerStarAdjunction C j).unit.app K) (δ.app K)
  have hΔ : Δ ∈ Pretriangulated.distinguishedTriangles := hδ K
  let e : Δ.obj₁ ≅ S.rightDerivedFunctor.obj K :=
    R.rightDerivedFunctor.mapIso (eR.app K) ≪≫
      (Functor.rightDerivedFunctorCompIso' E R eS.symm).app K
  have h₀ : IsZero ((DerivedCategory.homologyFunctor _ 0).obj Δ.obj₁) :=
    (hv 0 (by omega)).of_iso ((DerivedCategory.homologyFunctor _ 0).mapIso e)
  have h₁ : IsZero ((DerivedCategory.homologyFunctor _ 1).obj Δ.obj₁) :=
    (hv 1 (by omega)).of_iso ((DerivedCategory.homologyFunctor _ 1).mapIso e)
  let : Mono ((DerivedCategory.homologyFunctor _ 0).map Δ.mor₂) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff Δ hΔ 0).mpr
      (h₀.eq_of_src _ _)
  let : Epi ((DerivedCategory.homologyFunctor _ 0).map Δ.mor₂) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff Δ hΔ 0 1).mpr
      (h₁.eq_of_tgt _ _)
  change IsIso ((DerivedCategory.homologyFunctor _ 0).map Δ.mor₂)
  exact isIso_of_mono_of_epi _


private theorem zeroBottomOpens_hom_ext {B : Scheme.{u}} {A : B.ProEt} {U : B.Opens}
    (f g : A ⟶ (zeroBottomOpens B).obj U) : f = g := by
  apply MorphismProperty.Over.Hom.ext
  rw [← cancel_mono U.ι]
  exact (MorphismProperty.Over.w f).trans (MorphismProperty.Over.w g).symm

private def zeroBottomOpensLift {B : Scheme.{u}} {A : B.ProEt} {U : B.Opens}
    (h : ∀ a, A.hom a ∈ U) : A ⟶ (zeroBottomOpens B).obj U :=
  MorphismProperty.Over.homMk (IsOpenImmersion.lift U.ι A.hom (by
    rintro _ ⟨a, rfl⟩
    exact (congrArg (A.hom a ∈ ·) (Scheme.Opens.range_ι U)).mpr (h a)))
    (IsOpenImmersion.lift_fac _ _ _) trivial

private theorem zeroBottomOpens_mem {B : Scheme.{u}} {A : B.ProEt} {U : B.Opens}
    (f : A ⟶ (zeroBottomOpens B).obj U) (a : A.left) : A.hom a ∈ U := by
  rw [← MorphismProperty.Over.w f]
  change U.ι (f.left a) ∈ U
  simp

private instance zeroBottomOpens_flat (B : Scheme.{u}) :
    RepresentablyFlat (zeroBottomOpens B) := by
  constructor
  intro A
  refine @IsCofiltered.mk _ _ ?_ ?_
  · constructor
    · intro V W
      let h : ∀ a, A.hom a ∈ V.right ⊓ W.right := fun a ↦
        ⟨zeroBottomOpens_mem V.hom a, zeroBottomOpens_mem W.hom a⟩
      exact ⟨StructuredArrow.mk (Y := V.right ⊓ W.right) (zeroBottomOpensLift h),
        StructuredArrow.homMk (homOfLE inf_le_left) (zeroBottomOpens_hom_ext _ _),
        StructuredArrow.homMk (homOfLE inf_le_right) (zeroBottomOpens_hom_ext _ _), trivial⟩
    · exact fun _ _ _ _ ↦ ⟨_, 𝟙 _, by ext; exact Subsingleton.elim _ _⟩
  · exact ⟨StructuredArrow.mk (Y := ⊤) (zeroBottomOpensLift (fun _ ↦ trivial))⟩

private theorem zeroBottomOpens_coverPreserving (B : Scheme.{u}) :
    CoverPreserving (Opens.grothendieckTopology B) (Scheme.ProEt.topology B)
      (zeroBottomOpens B) where
  cover_preserve {U S} hS := by
    let V (x : U) : B.Opens := (hS x.val x.property).choose
    let f (x : U) : V x ⟶ U := (hS x.val x.property).choose_spec.choose
    have hf (x : U) : S (f x) := (hS x.val x.property).choose_spec.choose_spec.1
    have hx (x : U) : x.val ∈ V x := (hS x.val x.property).choose_spec.choose_spec.2
    have hopen (x : U) : IsOpenImmersion (B.homOfLE (f x).le) := inferInstance
    apply Scheme.ProEt.mem_topology_of_openImmersion _ (fun x : U ↦ B.homOfLE (f x).le)
    · intro x
      exact ⟨x, ⟨x.val, hx x⟩, Subtype.ext (B.homOfLE_apply _ _)⟩
    · intro x
      let a : Scheme.ProEt.ofOpenImmersion ((zeroBottomOpens B).obj U)
          (B.homOfLE (f x).le) ⟶ (zeroBottomOpens B).obj (V x) :=
        MorphismProperty.Over.homMk (𝟙 _) (by
          change 𝟙 _ ≫ (Scheme.Opens.ι (V x)) = B.homOfLE (f x).le ≫ Scheme.Opens.ι U
          simp) trivial
      have he : a ≫ (zeroBottomOpens B).map (f x) =
          Scheme.ProEt.ofOpenImmersionHom ((zeroBottomOpens B).obj U)
            (B.homOfLE (f x).le) := zeroBottomOpens_hom_ext _ _
      rw [← he]
      exact (S.functorPushforward (zeroBottomOpens B)).downward_closed
        (Sieve.image_mem_functorPushforward _ _ (hf x)) a

private instance zeroBottomOpens_continuous (B : Scheme.{u}) :
    (zeroBottomOpens B).IsContinuous (Opens.grothendieckTopology B)
      (Scheme.ProEt.topology B) :=
  Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
    (zeroBottomOpens_coverPreserving B)

set_option maxHeartbeats 1000000 in
-- The free/sheafification composite elaborates large internal-module equivalences.
set_option maxHeartbeats 1000000 in
-- The two adjunctions elaborate large section-module equivalence expressions.
set_option maxHeartbeats 1000000 in
-- Section-module and derived comparisons have large type-class parameters.
private def zeroBottomEvaluateEquiv
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (B : Scheme.{u}) (M : supportModules Λ B)
    (U : B.Opens) :
    ((zeroBottomFree Λ B).obj ((zeroBottomOpens B).obj U) ⟶ M) ≃
      (zeroBottomSections Λ B M).obj (op U) :=
  let e := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology B) (condensedRingObj Λ B)
  let R := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    (Scheme.ProEt.topology B) (condensedRingObj Λ B)
  let S := (sheafCompose (Scheme.ProEt.topology B)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  ((e.symm.toAdjunction.homEquiv _ _).trans
    ((PresheafOfModules.sheafificationAdjunction (R := S) (𝟙 _)).homEquiv _ _)).trans
      (PresheafOfModules.freeHomEquiv.trans uliftYonedaEquiv)

set_option maxHeartbeats 1000000 in
-- Section-module and derived comparisons have large type-class parameters.
private theorem zeroBottomEvaluate_bijective
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (B : Scheme.{u}) (M : supportModules Λ B)
    (U : B.Opens) : Function.Bijective (zeroBottomEvaluate Λ B M U) := by
  exact (zeroBottomEvaluateEquiv Λ B M U).bijective

set_option maxHeartbeats 1000000 in
-- Section-module and derived comparisons have large type-class parameters.
private theorem zeroBottomEvaluate_naturality
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (B : Scheme.{u}) (M : supportModules Λ B)
    {U W : B.Opens} (f : U ⟶ W)
    (a : (zeroBottomFree Λ B).obj ((zeroBottomOpens B).obj W) ⟶ M) :
    zeroBottomEvaluate Λ B M U
        ((zeroBottomFree Λ B).map ((zeroBottomOpens B).map f) ≫ a) =
      (zeroBottomSections Λ B M).map f.op (zeroBottomEvaluate Λ B M W a) := by
  let e := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology B) (condensedRingObj Λ B)
  let R := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    (Scheme.ProEt.topology B) (condensedRingObj Λ B)
  let S := (sheafCompose (Scheme.ProEt.topology B)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let adj := ((PresheafOfModules.freeAdjunction S.obj).comp
    (PresheafOfModules.sheafificationAdjunction (R := S) (𝟙 _))).comp
      e.symm.toAdjunction
  let F := (PresheafOfModules.free S.obj ⋙
    PresheafOfModules.sheafification (R := S) (𝟙 _)) ⋙ e.inverse
  let g := (zeroBottomOpens B).map f
  change (F.obj (uliftYoneda.{u + 1}.obj ((zeroBottomOpens B).obj W)) ⟶ M) at a
  change uliftYonedaEquiv.{u + 1} (adj.homEquiv _ _
    (F.map (uliftYoneda.{u + 1}.map g) ≫ a)) =
    (e.functor.obj M).val.presheaf.map g.op
      (uliftYonedaEquiv.{u + 1} (adj.homEquiv _ _ a))
  exact (congrArg uliftYonedaEquiv.{u + 1}
    (adj.homEquiv_naturality_left (uliftYoneda.{u + 1}.map g) a)).trans
      (uliftYonedaEquiv_naturality _ g.op).symm

/-- The published conventions with the given finite coefficient extension and level.
Only the coefficient presentation varies; the global field and coefficient datum stay fixed.
Source: def-pur-conventions (blueprint: lem-pur-smooth-divisor-native-bottom). -/
def nativeDivisorSetting (P : PurityFiniteSetting.{u})
    (c : PurityTransport.Coefficient P.coefficients.l) : CurrentPurityConventions.Setting.{u} :=
  ⟨P.field, P.coefficients, c⟩

/-- The actual root-normalized Tate line placed in degree zero, then shifted by two.
Source: sk-def-sp-tate-twist (blueprint: lem-pur-smooth-divisor-native-bottom). -/
def nativeDivisorInput (P : PurityFiniteSetting.{u})
    (c : PurityTransport.Coefficient P.coefficients.l) (T : Scheme.{u}) :
    c.derived P.coefficients.l T :=
  ((DerivedCategory.singleFunctor _ 0).obj
    ((nativeDivisorSetting P c).twistLine T 1)) ⟦(2 : ℤ)⟧

/-- Exact closed direct image from the published support adjunction. No extra geometric
hypothesis is imposed: a complement in a Noetherian scheme is quasi-compact.
Source: sk-lem-formal-closed-support (blueprint: lem-pur-smooth-divisor-native-bottom). -/
instance nativeDivisorClosedExact (P : PurityFiniteSetting.{u})
    (c : PurityTransport.Coefficient P.coefficients.l) {D T : Scheme.{u}}
    (i : D ⟶ T) [IsClosedImmersion i] [IsNoetherian T] :
    PreservesFiniteColimits (lowerStar (c.obj P.coefficients.l) i) :=
  letI : QuasiCompact i.openComplement.ι := inferInstance
  closedSupport_lowerStarExact _ i i.openComplement.ι
    i.range_eq_compl_range_openComplement_ι

/-- The actual right-derived support kernel on Lambda_T(1)[2]. Right-derived support
commutes canonically with shifts, so this is Ri^!(Lambda_T(1))[2]. The fibre comparison
in formalClosedSupportFiberAssertionsOfField identifies it with the closed pullback
of the fibre of the specified open restriction unit, not an arbitrary fibre.
Source: sk-lem-formal-closed-support (blueprint: lem-pur-smooth-divisor-native-bottom). -/
def nativeDivisorSupport (P : PurityFiniteSetting.{u})
    (c : PurityTransport.Coefficient P.coefficients.l) {D T : Scheme.{u}}
    (i : D ⟶ T) [IsClosedImmersion i] : c.derived P.coefficients.l D :=
  (closedSupport (c.obj P.coefficients.l) i i.openComplement.ι).rightDerivedFunctor.obj
    (nativeDivisorInput P c T)

set_option maxHeartbeats 1000000 in
-- The native module and derived triangle instances require extended elaboration.
private theorem support_isGE_two_of_bottom_unit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {D T V : Scheme.{u}}
    (i : D ⟶ T) (j : V ⟶ T) [IsClosedImmersion i] [IsOpenImmersion j]
    [QuasiCompact j] (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (M : supportModules Λ T)
    (hη : IsIso ((DerivedCategory.homologyFunctor _ 0).map
      ((closedSupportOpenDerivedAdjunction Λ j).unit.app
        ((DerivedCategory.singleFunctor _ 0).obj M)))) :
    ((closedSupport Λ i j).rightDerivedFunctor.obj
      ((DerivedCategory.singleFunctor _ 0).obj M)).IsGE 2 := by
  let := closedSupport_lowerStarExact Λ i j hij
  let := hη
  let S := (DerivedCategory.singleFunctor (supportModules Λ T) 0).obj M
  let R := (closedSupport Λ i j).rightDerivedFunctor.obj S
  let : R.IsGE 0 := (closedSupport Λ i j).isGE_rightDerivedFunctor_obj_singleFunctor M
  obtain ⟨δ, hδ⟩ := closedSupport_triangle Λ i j hij
  let Δ := Pretriangulated.Triangle.mk ((closedSupportDerivedAdjunction Λ i j hij).counit.app S)
    ((closedSupportOpenDerivedAdjunction Λ j).unit.app S) (δ.app S)
  have hΔ : Δ ∈ Pretriangulated.distinguishedTriangles := hδ S
  let F := lowerStar Λ i
  let G := lowerStar Λ j
  let L := supportPullback Λ j
  let e := G.rightDerivedFunctor.mapIso ((L.mapDerivedCategorySingleFunctor 0).app M)
  let hO : Δ.obj₃.IsGE 0 := by
    have hG := G.isGE_rightDerivedFunctor_obj_singleFunctor (L.obj M)
    exact ⟨(DerivedCategory.TStructure.t.ge 0).prop_of_iso e.symm hG.ge⟩
  let : IsIso ((DerivedCategory.homologyFunctor _ 0).map Δ.mor₂) := hη
  have hA₀ : IsZero ((DerivedCategory.homologyFunctor _ 0).obj Δ.obj₁) := by
    have hleft := Δ.obj₃.isZero_of_isGE 0 (-1) (by omega)
    have hright := (DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff
      Δ hΔ 0).mp (by exact inferInstanceAs (Mono
        ((DerivedCategory.homologyFunctor _ 0).map Δ.mor₂)))
    exact (DerivedCategory.HomologySequence.exact₁ Δ hΔ (-1) 0).isZero_X₂
      (hleft.eq_of_src _ _) hright
  have hA₁ : IsZero ((DerivedCategory.homologyFunctor _ 1).obj Δ.obj₁) := by
    have hleft := (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff
      Δ hΔ 0 1).mp (by exact inferInstanceAs (Epi
        ((DerivedCategory.homologyFunctor _ 0).map Δ.mor₂)))
    have hright := S.isZero_of_isLE 0 1 (by omega)
    exact (DerivedCategory.HomologySequence.exact₁ Δ hΔ 0 1).isZero_X₂
      hleft (hright.eq_of_tgt _ _)
  refine (DerivedCategory.isGE_iff R 2).2 ?_
  intro q hq
  by_cases hneg : q < 0
  · exact R.isZero_of_isGE 0 q hneg
  · have hq' : q = 0 ∨ q = 1 := by omega
    rcases hq' with rfl | rfl
    · exact F.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj hA₀
    · exact F.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj hA₁

/-- Degree one of the signed construction is the original line via the section equivalence. -/
private def zeroBottomSignedFirstIso (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) :
    spInternalSignedTwist X R M 1 ≅ M :=
  (InternalAbelianSheafModule.sectionModuleEquivalence
    (Scheme.ProEt.topology X) R).unitIso.symm.app M

private theorem support_bottom_unit_of_ordinary_unit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {V T : Scheme.{u}}
    (j : V ⟶ T) (M : supportModules Λ T)
    (hη : IsIso ((supportPullbackAdjunction Λ j).unit.app M)) :
    IsIso ((DerivedCategory.homologyFunctor _ 0).map
      ((closedSupportOpenDerivedAdjunction Λ j).unit.app
        ((DerivedCategory.singleFunctor _ 0).obj M))) :=
  (Adjunction.derived_unit_single_zero_isIso_iff (supportPullbackAdjunction Λ j) M).mpr hη

set_option maxHeartbeats 1000000 in
-- Abstract ring and module parameters keep the unit and shift calculations small.
private theorem support_shift_isGE_of_restriction_unit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {D V T : Scheme.{u}}
    (i : D ⟶ T) (j : V ⟶ T) [IsClosedImmersion i] [IsOpenImmersion j]
    [QuasiCompact j] (hij : Set.range i.base = (Set.range j.base)ᶜ)
    {M N : supportModules Λ T} (e : M ≅ N)
    (hη : IsIso ((supportPullbackAdjunction Λ j).unit.app N)) :
    ((closedSupport Λ i j).rightDerivedFunctor.obj
      (((DerivedCategory.singleFunctor _ 0).obj M) ⟦(2 : ℤ)⟧)).IsGE 0 := by
  let adj := supportPullbackAdjunction Λ j
  have hfirst : IsIso (adj.unit.app M) :=
    (NatTrans.isIso_app_iff_of_iso adj.unit e).mpr hη
  have hd := support_bottom_unit_of_ordinary_unit Λ j M hfirst
  let F := (closedSupport Λ i j).rightDerivedFunctor
  let K := (DerivedCategory.singleFunctor _ 0).obj M
  let : (F.obj K).IsGE 2 := support_isGE_two_of_bottom_unit Λ i j hij M hd
  let hshift : (F.obj K⟦(2 : ℤ)⟧).IsGE 0 :=
    DerivedCategory.TStructure.t.isGE_shift (F.obj K) 2 2 0
  exact ⟨(DerivedCategory.TStructure.t.ge 0).prop_of_iso
    ((F.commShiftIso (2 : ℤ)).app K).symm hshift.ge⟩

section
-- Preserve the actual line as an object while elaborating its formal comparison.
attribute [local irreducible] PurityTransport.Coefficient.firstLine

private theorem nativeDivisorSupport_isGE_of_restriction_unit
    (P : PurityFiniteSetting.{u})
    (c : PurityTransport.Coefficient P.coefficients.l) {D T : Scheme.{u}}
    (i : D ⟶ T) [IsClosedImmersion i] [IsNoetherian T]
    (hη : IsIso ((supportPullbackAdjunction (c.obj P.coefficients.l)
      i.openComplement.ι).unit.app (c.firstLine P.coefficients.l T))) :
    (nativeDivisorSupport P c i).IsGE 0 :=
  support_shift_isGE_of_restriction_unit (c.obj P.coefficients.l) i i.openComplement.ι
    i.range_eq_compl_range_openComplement_ι
    (zeroBottomSignedFirstIso T (condensedRingObj (c.obj P.coefficients.l) T)
      (c.firstLine P.coefficients.l T)) hη

end

/-- On U this is i_* extension-by-zero of Lambda_(D intersect U), in degree zero.
Closed base change and open adjunction identify maps from it to the fixed input
with Hom(i_(U)* Lambda_(D_U), Lambda_U(1)[2]). Its arrows give the usual restriction
maps by precomposition; no independent restriction maps are chosen.
Source: proof (b), open restriction (blueprint: lem-pur-smooth-divisor-native-bottom). -/
def nativeDivisorSource (P : PurityFiniteSetting.{u})
    (c : PurityTransport.Coefficient P.coefficients.l) {D T : Scheme.{u}}
    (i : D ⟶ T) [IsClosedImmersion i] [IsNoetherian T] :=
  TopologicalSpace.Opens.map i.base ⋙ zeroBottomOpens D ⋙
    zeroBottomFree (c.obj P.coefficients.l) D ⋙ DerivedCategory.singleFunctor _ 0 ⋙
      (lowerStar (c.obj P.coefficients.l) i).mapDerivedCategory

/-- The supported Hom presheaf on T, with restriction by the actual open inclusions.
Source: proof (b), supported arrows (blueprint: lem-pur-smooth-divisor-native-bottom). -/
def nativeDivisorHom (P : PurityFiniteSetting.{u})
    (c : PurityTransport.Coefficient P.coefficients.l) {D T : Scheme.{u}}
    (i : D ⟶ T) [IsClosedImmersion i] [IsNoetherian T] :=
  (nativeDivisorSource P c i).op ⋙ yoneda.obj (nativeDivisorInput P c T)

/-- Actual sections over D intersect U of the single cohomology sheaf H^0 K on D.
The section-module equivalence retains the sheaf and its scalar action.
Source: proof (b), bottom truncation (blueprint: lem-pur-smooth-divisor-native-bottom). -/
def nativeDivisorSections (P : PurityFiniteSetting.{u})
    (c : PurityTransport.Coefficient P.coefficients.l) {D T : Scheme.{u}}
    (i : D ⟶ T) [IsClosedImmersion i] :=
  (TopologicalSpace.Opens.map i.base).op ⋙
    zeroBottomSections (c.obj P.coefficients.l) D
      ((DerivedCategory.homologyFunctor _ 0).obj (nativeDivisorSupport P c i))

private theorem nativeDivisorSections_isSheaf
    (P : PurityFiniteSetting.{u})
    (c : PurityTransport.Coefficient P.coefficients.l) {D T : Scheme.{u}}
    (i : D ⟶ T) [IsClosedImmersion i] :
    Presheaf.IsSheaf (Opens.grothendieckTopology T) (nativeDivisorSections P c i) := by
  let M := ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology D) (condensedRingObj (c.obj P.coefficients.l) D)).functor.obj
      ((DerivedCategory.homologyFunctor _ 0).obj (nativeDivisorSupport P c i)))
  have hM := (Presheaf.isSheaf_iff_isSheaf_forget _ M.val.presheaf (forget Ab)).mp M.isSheaf
  have hD := (zeroBottomOpens D).op_comp_isSheaf_of_isSheaf
    (Opens.grothendieckTopology D) (Scheme.ProEt.topology D) _ hM
  exact (TopologicalSpace.Opens.map i.base).op_comp_isSheaf_of_isSheaf
    (Opens.grothendieckTopology T) (Opens.grothendieckTopology D) _ hD

/-- The specified canonical comparison: take the closed-support adjunct, apply H^0,
normalize H^0 of the free module in degree zero, then evaluate at its identity generator.
Thus this is the adjunction/bottom-truncation map, before any bijectivity is asserted.
Source: proof (b), descent to charts (blueprint: lem-pur-smooth-divisor-native-bottom). -/
def nativeDivisorComparison (P : PurityFiniteSetting.{u})
    (c : PurityTransport.Coefficient P.coefficients.l) {D T : Scheme.{u}}
    (i : D ⟶ T) [IsClosedImmersion i] [IsNoetherian T] (U : T.Opens) :
    (nativeDivisorHom P c i).obj (op U) → (nativeDivisorSections P c i).obj (op U) :=
  letI : QuasiCompact i.openComplement.ι := inferInstance
  fun f ↦ zeroBottomEvaluate (c.obj P.coefficients.l) D
    ((DerivedCategory.homologyFunctor _ 0).obj (nativeDivisorSupport P c i))
    ((TopologicalSpace.Opens.map i.base).obj U)
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).inv.app _ ≫
      (DerivedCategory.homologyFunctor _ 0).map
        ((closedSupportDerivedAdjunction _ i i.openComplement.ι
          i.range_eq_compl_range_openComplement_ι).homEquiv _ _ f))

set_option maxHeartbeats 1000000 in
-- Section-module and derived comparisons have large type-class parameters.
private theorem nativeDivisorComparison_bijective_of_isGE
    (P : PurityFiniteSetting.{u})
    (c : PurityTransport.Coefficient P.coefficients.l) {D T : Scheme.{u}}
    (i : D ⟶ T) [IsClosedImmersion i] [IsNoetherian T]
    [(nativeDivisorSupport P c i).IsGE 0] (U : T.Opens) :
    Function.Bijective (nativeDivisorComparison P c i U) := by
  let : QuasiCompact i.openComplement.ι := inferInstance
  let M := (zeroBottomFree (c.obj P.coefficients.l) D).obj
    ((zeroBottomOpens D).obj ((TopologicalSpace.Opens.map i.base).obj U))
  let K := nativeDivisorSupport P c i
  let e := (DerivedCategory.singleFunctorCompHomologyFunctorIso
    (supportModules (c.obj P.coefficients.l) D) 0).app M
  let adj := closedSupportDerivedAdjunction (c.obj P.coefficients.l) i
    i.openComplement.ι i.range_eq_compl_range_openComplement_ι
  have h := (zeroBottomEvaluate_bijective (c.obj P.coefficients.l) D
    ((DerivedCategory.homologyFunctor _ 0).obj K)
    ((TopologicalSpace.Opens.map i.base).obj U)).comp
      ((Iso.homCongr e (Iso.refl _)).bijective.comp
        ((DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE
          (X := (DerivedCategory.singleFunctor _ 0).obj M) (Y := K) 0).comp
            (adj.homEquiv _ _).bijective))
  change Function.Bijective (fun a ↦ zeroBottomEvaluate (c.obj P.coefficients.l) D
    ((DerivedCategory.homologyFunctor _ 0).obj K)
    ((TopologicalSpace.Opens.map i.base).obj U)
      (e.inv ≫ (DerivedCategory.homologyFunctor _ 0).map (adj.homEquiv _ _ a)))
  convert h using 1
  funext a
  dsimp only [Function.comp_apply, EquivLike.coe_coe, Iso.homCongr_apply]
  exact congrArg (zeroBottomEvaluate _ D _ _)
    (Category.comp_id _).symm

private theorem bottomAdjunct_naturality
    {A C E : Type*} [Category A] [Category C] [Category E]
    {L : C ⥤ E} {R : E ⥤ C} (adj : L ⊣ R)
    (S : A ⥤ C) (H : C ⥤ A) (e : S ⋙ H ≅ 𝟭 A)
    {M N : A} {K : E} (g : M ⟶ N) (a : L.obj (S.obj N) ⟶ K) :
    e.inv.app M ≫ H.map (adj.homEquiv _ _ (L.map (S.map g) ≫ a)) =
      g ≫ e.inv.app N ≫ H.map (adj.homEquiv _ _ a) := by
  rw [adj.homEquiv_naturality_left, H.map_comp, ← Category.assoc]
  have hn := e.inv.naturality g
  change g ≫ e.inv.app N = e.inv.app M ≫ H.map (S.map g) at hn
  rw [← hn, Category.assoc]

set_option maxHeartbeats 1000000 in
-- Section-module and derived comparisons have large type-class parameters.
private theorem nativeDivisorComparison_naturality
    (P : PurityFiniteSetting.{u})
    (c : PurityTransport.Coefficient P.coefficients.l) {D T : Scheme.{u}}
    (i : D ⟶ T) [IsClosedImmersion i] [IsNoetherian T]
    (U W : T.Opens) (f : U ⟶ W) (a : (nativeDivisorHom P c i).obj (op W)) :
    nativeDivisorComparison P c i U ((nativeDivisorHom P c i).map f.op a) =
      (nativeDivisorSections P c i).map f.op (nativeDivisorComparison P c i W a) := by
  let : QuasiCompact i.openComplement.ι := inferInstance
  let Λ := c.obj P.coefficients.l
  let M := (zeroBottomFree Λ D).obj
    ((zeroBottomOpens D).obj ((TopologicalSpace.Opens.map i.base).obj U))
  let N := (zeroBottomFree Λ D).obj
    ((zeroBottomOpens D).obj ((TopologicalSpace.Opens.map i.base).obj W))
  let g : M ⟶ N := (zeroBottomFree Λ D).map
    ((zeroBottomOpens D).map ((TopologicalSpace.Opens.map i.base).map f))
  let adj := closedSupportDerivedAdjunction Λ i i.openComplement.ι
    i.range_eq_compl_range_openComplement_ι
  let H := DerivedCategory.homologyFunctor (supportModules Λ D) 0
  let S := DerivedCategory.singleFunctor (supportModules Λ D) 0
  let e := DerivedCategory.singleFunctorCompHomologyFunctorIso (supportModules Λ D) 0
  have h := bottomAdjunct_naturality adj S H e g a
  change zeroBottomEvaluate Λ D _ _
    (e.inv.app M ≫ H.map (adj.homEquiv _ _
      ((lowerStar Λ i).mapDerivedCategory.map (S.map g) ≫ a))) = _
  rw [h]
  exact zeroBottomEvaluate_naturality Λ D _ ((TopologicalSpace.Opens.map i.base).map f)
    (e.inv.app N ≫ H.map (adj.homEquiv _ _ a))

set_option maxHeartbeats 1000000 in
-- Section-module and derived comparisons have large type-class parameters.
private theorem nativeDivisorHom_isSheaf_of_isGE
    (P : PurityFiniteSetting.{u})
    (c : PurityTransport.Coefficient P.coefficients.l) {D T : Scheme.{u}}
    (i : D ⟶ T) [IsClosedImmersion i] [IsNoetherian T]
    [(nativeDivisorSupport P c i).IsGE 0] :
    Presheaf.IsSheaf (Opens.grothendieckTopology T) (nativeDivisorHom P c i) := by
  let e : nativeDivisorHom P c i ≅ nativeDivisorSections P c i :=
    NatIso.ofComponents (fun U ↦
      (Equiv.ofBijective _ (nativeDivisorComparison_bijective_of_isGE P c i U.unop)).toIso)
      (fun f ↦ by
        ext a
        exact nativeDivisorComparison_naturality P c i _ _ f.unop a)
  exact (Presheaf.isSheaf_of_iso_iff e).mpr (nativeDivisorSections_isSheaf P c i)

/-- Native bottom-degree descent for a relative smooth effective Cartier divisor,
before any Thom or purity isomorphism. The empty divisor and nonreduced bases are included.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-an/lem-pur-divisor-class.proof.md, proof (b),
the paragraph beginning Both classes are global classes supported on D
(blueprint: lem-pur-smooth-divisor-native-bottom).

Proof plan, following the six steps of the DAG node:
1. T is Noetherian because it is finite type over a field, so its open complement j
is quasi-compact. The support triangle and left t-exactness identify vanishing of
support cohomology below two with invertibility of L -> j_*j^*L for L in degree zero.
Exact fully faithful closed direct image reflects these vanishing assertions.
2. For finite coefficients, use the smooth-divisor low-support lemma on the etale
site. The bounded-below direct-image comparison, including its unit compatibility,
and the exact finite section-action equivalence identify the actual pro-etale unit.
The root-normalized Tate lines coincide, so this unit is invertible.
3. The native integral root-normalized line is the inverse limit of the twists at
O_E/ell^m. Open restriction and j_* preserve these limits. Naturality identifies
the integral unit with the limit of the finite units, so the compatible inverses
provide its inverse. Exact faithful scalar forgetting retains the native unit.
4. For E invert ell in the integral line; for Qbar take the sheafified filtered
colimit over finite coefficient subextensions. Restriction commutes with these
colimits, and qcqs j_* commutes with them by the q=0 higher-direct-image theorem.
Their compatible units are invertible. This includes every finite extension of F.
5. Hence Ri^!L is in D>=2 and its shift by two is in D>=0. Restriction commutes
with the support kernel; exact extension by zero makes restriction preserve
K-injectives. This identifies the support complexes on all opens, compatibly with
nested restrictions, and exact restriction commutes with cohomology sheaves.
6. Closed adjunction with the regular coefficient module and open restriction give
Hom(i_(U)*Lambda_(D_U),Lambda_U(1)[2]) = H^0 RGamma(D_U,K|_(D_U)). Bottom truncation
identifies this with Gamma(D_U,H^0 K|_(D_U)). On a free open representable the map is
exactly nativeDivisorComparison. Every construction is natural in open inclusions;
sections glue uniquely, so this Hom presheaf is a sheaf. Empty support gives zero.
No generator or invertibility of a divisor, Thom or purity arrow is used or asserted.
-/
theorem smoothDivisorNativeBottom (P : PurityFiniteSetting.{u})
    {B T D : Scheme.{u}}
    (b : B ⟶ Spec (.of P.field.k))
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (v : T ⟶ B) (d : ℕ) (_hd : 1 ≤ d) [SmoothOfRelativeDimension d v]
    [IsSeparated (v ≫ b)] [LocallyOfFiniteType (v ≫ b)] [QuasiCompact (v ≫ b)]
    (i : D ⟶ T) [IsClosedImmersion i] (_hcartier : IsEffectiveCartierCenter i)
    [Smooth (i ≫ v)]
    (_hcodim : ∀ x : D, ringKrullDim (T.presheaf.stalk (i x)) =
      ringKrullDim (D.presheaf.stalk x) + (1 : WithBot ℕ∞))
    (c : PurityTransport.Coefficient P.coefficients.l) (_hc : zeroBottomAllowed P c) :
    letI : IsNoetherian T := isNoetherian_of_locallyOfFiniteType (v ≫ b)
    (nativeDivisorSupport P c i).IsGE 0 ∧
    (∀ U : T.Opens, Function.Bijective (nativeDivisorComparison P c i U)) ∧
    (∀ (U W : T.Opens) (f : U ⟶ W) (a : (nativeDivisorHom P c i).obj (op W)),
      nativeDivisorComparison P c i U ((nativeDivisorHom P c i).map f.op a) =
        (nativeDivisorSections P c i).map f.op (nativeDivisorComparison P c i W a)) ∧
    Presheaf.IsSheaf (Opens.grothendieckTopology T)
      (nativeDivisorHom P c i) := by
  let : IsNoetherian T := isNoetherian_of_locallyOfFiniteType (v ≫ b)
  have hfield := nativeBottom_prime_unit P
  have hT : IsUnit (P.coefficients.l : Γ(T, ⊤)) := by
    simpa using hfield.map ((Scheme.ΓSpecIso (.of P.field.k)).inv ≫ (v ≫ b).appTop).hom
  have hfinite (A : CommRingCat.{0}) (fin : Finite A) (n : ℕ)
      (hA : (P.coefficients.l ^ (n + 1) : A) = 0) :
      IsIso ((supportPullbackAdjunction
        ((PurityTransport.Coefficient.finite A fin n hA).obj P.coefficients.l)
        i.openComplement.ι).unit.app
          ((PurityTransport.Coefficient.finite A fin n hA).firstLine P.coefficients.l T)) := by
    let := fin
    let hΛ := PurityTransport.finiteLiftAnnihilator P.coefficients.l A n hA
    let M := Scheme.finiteEtaleTateSheaf (ULift.{u + 1} A)
      (P.coefficients.l ^ (n + 1)) T hΛ 1
    have hv := Etale.isZero_homology_rightDerivedSectionsWithSupport_of_smooth_divisor
      P.coefficients.l (n + 1) (Fact.out : P.coefficients.l.Prime)
      hfield (by omega) b v d i _hcodim (ULift.{u + 1} A) hΛ
    have hd := etale_bottom_unit_of_low_support (ULift.{u + 1} A) i
      i.openComplement.ι i.range_eq_compl_range_openComplement_ι M hv
    have hη := (Adjunction.derived_unit_single_zero_isIso_iff
      (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} A))
        i.openComplement.ι) M).mp hd
    exact nativeFiniteRestrictionUnit_of_etaleUnit P.coefficients.l i.openComplement.ι
      A fin n hA hT hη
  have hη := nativeTateRestrictionUnit_of_finite P.coefficients.l i.openComplement.ι
    hT hfinite c
  let hge := nativeDivisorSupport_isGE_of_restriction_unit P c i hη
  let := hge
  exact ⟨hge, nativeDivisorComparison_bijective_of_isGE P c i,
    nativeDivisorComparison_naturality P c i, nativeDivisorHom_isSheaf_of_isGE P c i⟩

end WeilConjectures.PurityFiniteSetting
