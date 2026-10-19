/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.Ring.Limits
import Sheaf.CategoryTheory.ModuleInverseImageAdjunction
import Sheaf.CategoryTheory.SheafPullbackForgetComparison
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.ShortExact
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.CategoryTheory.RingedSiteModules

/-!
# Exact pullback of finite constant pro-etale left modules

Source: Weil conjectures blueprint, order 1236; Stacks Project, Tags 00WJ, 03D2, and 04JC
(blueprint: prop-weil-pbc-proetale-constant-exact).

The coefficient categories are the recorded continuous-function ringed module categories.
The small-model module Kan extension gives inverse image over the inverse-image ring;
restriction along the inverse of the canonical coefficient map transports the action.
The commutative comparison uses the recorded tensor pullback, with the canonical
constant-preserving coefficient identifications written explicitly.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

section
open Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace AlgebraicGeometry.Scheme
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private noncomputable def finiteExactRingUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) RingCat.{u + 1}) :
    ((AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).sheafPushforwardContinuous
      RingCat.{u + 1} (proEtaleModelTopology Y) (ProEt.topology Y)).obj R ⟶
    ((proEtaleModelBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
      (proEtaleModelTopology Y) (proEtaleModelTopology X)).obj
        (((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
          RingCat.{u + 1} (proEtaleModelTopology X) (ProEt.topology X)).obj
            ((proEtaleSheafInverseImage f RingCat.{u + 1}).obj R)) :=
  ⟨Functor.whiskerLeft AsSmall.down.op
    ((proEtaleSheafAdjunction f RingCat.{u + 1}).unit.app R).hom⟩
private noncomputable def finiteExactRingEquivalence (X : Scheme.{u}) :
    Sheaf (proEtaleModelTopology X) RingCat.{u + 1} ≌
      Sheaf (ProEt.topology X) RingCat.{u + 1} :=
  CategoryTheory.Equivalence.mk
    ((AsSmall.up : X.ProEt ⥤ proEtaleSiteModel X).sheafPushforwardContinuous
      RingCat.{u + 1} (ProEt.topology X) (proEtaleModelTopology X))
    ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
      RingCat.{u + 1} (proEtaleModelTopology X) (ProEt.topology X))
    (Iso.refl _) (Iso.refl _)
@[irreducible] private noncomputable def finiteExactRingAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (finiteExactRingEquivalence Y).functor ⋙ proEtaleSheafInverseImage f RingCat.{u + 1} ⋙
      (finiteExactRingEquivalence X).inverse ⊣
        (proEtaleModelBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
          (proEtaleModelTopology Y) (proEtaleModelTopology X) :=
  (proEtaleSheafAdjunction f RingCat.{u + 1}).restrictFullyFaithful
    (finiteExactRingEquivalence Y).fullyFaithfulFunctor
    (finiteExactRingEquivalence X).fullyFaithfulFunctor
    (Iso.refl _) (Iso.refl _)
private theorem finiteExactRingAdjunction_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) RingCat.{u + 1}) :
    (finiteExactRingAdjunction f).unit.app ((finiteExactRingEquivalence Y).inverse.obj R) =
      ⟨CategoryTheory.Functor.whiskerLeft AsSmall.down.op
        ((proEtaleSheafAdjunction f RingCat.{u + 1}).unit.app R).hom⟩ := by
  apply (finiteExactRingEquivalence Y).functor.map_injective
  rw [finiteExactRingAdjunction, Adjunction.map_restrictFullyFaithful_unit_app]
  simp only [Iso.refl_hom, NatTrans.id_app]
  rfl
private theorem finiteExactRingPresentation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) RingCat.{u + 1}) :
    let A := ((AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).sheafPushforwardContinuous
      RingCat.{u + 1} (proEtaleModelTopology Y) (ProEt.topology Y)).obj R
    let B := ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
      RingCat.{u + 1} (proEtaleModelTopology X) (ProEt.topology X)).obj
        ((proEtaleSheafInverseImage f RingCat.{u + 1}).obj R)
    ∃ p : SheafPullbackUnitPresentation (F := proEtaleModelBaseChange f)
      ((sheafCompose (proEtaleModelTopology Y) (CategoryTheory.forget RingCat.{u + 1})).obj A)
      ((sheafCompose (proEtaleModelTopology X) (CategoryTheory.forget RingCat.{u + 1})).obj B),
      ∀ U r, p.unit.hom.app U r = (finiteExactRingUnit f R).hom.app U r := by
  let F := proEtaleModelBaseChange f
  let J := proEtaleModelTopology Y
  let K := proEtaleModelTopology X
  let A := (finiteExactRingEquivalence Y).inverse.obj R
  let B := (finiteExactRingEquivalence X).inverse.obj
    ((proEtaleSheafInverseImage f RingCat.{u + 1}).obj R)
  let : (AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)).inverse.IsEquivalence
  let : (AsSmall.up : X.ProEt ⥤ proEtaleSiteModel X).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).functor.IsEquivalence
  let : PreservesFiniteLimits F := by
    dsimp [F, proEtaleModelBaseChange]
    infer_instance
  let : RepresentablyFlat F := flat_of_preservesFiniteLimits F
  let e := (finiteExactRingAdjunction f).leftAdjointUniq
    (sheafAdjunctionContinuous F RingCat.{u + 1} J K)
  let c := sheafPullbackForgetIso J K F (CategoryTheory.forget RingCat.{u + 1})
  let iso : (sheafCompose K (CategoryTheory.forget RingCat.{u + 1})).obj B ≅
      (sheafPullback F (Type (u + 1)) J K).obj
        ((sheafCompose J (CategoryTheory.forget RingCat.{u + 1})).obj A) :=
    (sheafCompose K (CategoryTheory.forget RingCat.{u + 1})).mapIso (e.app A) ≪≫
      c.app A
  let unit :=
    (sheafCompose J (CategoryTheory.forget RingCat.{u + 1})).map (finiteExactRingUnit f R)
  refine ⟨⟨unit, iso, ?_⟩, fun U r ↦ rfl⟩
  intro U r
  have he := Adjunction.unit_leftAdjointUniq_hom_app (finiteExactRingAdjunction f)
    (sheafAdjunctionContinuous F RingCat.{u + 1} J K) A
  have hc := sheafPullbackForgetIso_unit J K F (CategoryTheory.forget RingCat.{u + 1}) A
  have ht := finiteExactRingAdjunction_unit f R
  have ht' := congrArg (fun z ↦ z.hom.app U) ht
  have htr : ((finiteExactRingAdjunction f).unit.app A).hom.app U r = unit.hom.app U r :=
    ConcreteCategory.congr_hom ht' r
  have he' := congrArg (fun z ↦ z.hom.app U) he
  have he0 := ConcreteCategory.congr_hom he' r
  have hc' := congrArg (fun z ↦ z.hom.app U) hc
  have hc0 := ConcreteCategory.congr_hom hc' r
  change (c.hom.app A).hom.app (F.op.obj U)
      ((e.hom.app A).hom.app (F.op.obj U) (unit.hom.app U r)) = _
  exact (congrArg (fun t ↦ (c.hom.app A).hom.app (F.op.obj U)
      ((e.hom.app A).hom.app (F.op.obj U) t)) htr.symm).trans
    ((congrArg (fun t ↦ (c.hom.app A).hom.app (F.op.obj U) t) he0).trans hc0)
end AlgebraicGeometry.Scheme
end

namespace AlgebraicGeometry.ProEtale

variable {U V : Scheme.{u}} (f : U ⟶ V) (Λ : Type (u + 1))
  [Ring Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ]

/-- Register the recorded coefficient isomorphism, without choosing any new map.
Source: blueprint order 1235 (blueprint: prop-weil-pbc-proetale-constant-exact). -/
noncomputable instance finiteCoefficientInverseImageMap_invertible :
    IsIso (finiteCoefficientInverseImageMap f Λ) :=
  finiteCoefficientInverseImageMap_isIso f Λ

/-- The inverse-image coefficient ring on the original small site.
Source: Stacks Tag 03D2 (blueprint: prop-weil-pbc-proetale-constant-exact). -/
noncomputable abbrev finiteCoefficientInverseRing :=
  (Scheme.proEtaleSheafInverseImage f RingCat.{u + 1}).obj (finiteCoefficientRingSheaf V Λ)

/-- The ring adjunction unit on the small site models. Only the Hom universe is enlarged.
Source: Stacks Tags 00YV and 03D2 (blueprint: prop-weil-pbc-proetale-constant-exact). -/
noncomputable def finiteCoefficientModelRingUnit :
    ((AsSmall.down : Scheme.proEtaleSiteModel V ⥤ V.ProEt).sheafPushforwardContinuous
      RingCat.{u + 1} (Scheme.proEtaleModelTopology V) (Scheme.ProEt.topology V)).obj
        (finiteCoefficientRingSheaf V Λ) ⟶
    ((Scheme.proEtaleModelBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
      (Scheme.proEtaleModelTopology V) (Scheme.proEtaleModelTopology U)).obj
        (((AsSmall.down : Scheme.proEtaleSiteModel U ⥤ U.ProEt).sheafPushforwardContinuous
          RingCat.{u + 1} (Scheme.proEtaleModelTopology U) (Scheme.ProEt.topology U)).obj
            (finiteCoefficientInverseRing f Λ)) :=
  ⟨Functor.whiskerLeft AsSmall.down.op
    (((Scheme.proEtaleSheafAdjunction f RingCat.{u + 1}).unit.app
      (finiteCoefficientRingSheaf V Λ)).hom)⟩

/-- Inverse image of left modules over the inverse-image ring. Mathlib's module pullback
is the module Kan extension followed by sheafification, along the actual ring unit.
Its action is the inverse image of the original action under the product comparison.
Transport to and from the equivalent small model retains every original site object.
Source: Stacks Tag 03D2 (blueprint: prop-weil-pbc-proetale-constant-exact). -/
noncomputable def finiteCoefficientModuleInverseImage :
    FiniteCoefficientModules V Λ ⥤ SheafOfModules.{u + 1} (finiteCoefficientInverseRing f Λ) :=
  Scheme.proEtaleModuleToModel (finiteCoefficientRingSheaf V Λ) ⋙
    SheafOfModules.pullback (finiteCoefficientModelRingUnit f Λ) ⋙
    Scheme.proEtaleModuleFromModel (finiteCoefficientInverseRing f Λ)

/-- The specified pullback: transport the inverse-image action by c_f inverse.
Thus r acts as c_f inverse(r), and on underlying abelian maps the functor is inverse image.
No tensor product or multiplicative commutativity is required here.
Source: blueprint order 1236; Stacks Tag 03D2
(blueprint: prop-weil-pbc-proetale-constant-exact). -/
noncomputable def finiteCoefficientModulePullback :
    FiniteCoefficientModules V Λ ⥤ FiniteCoefficientModules U Λ :=
  finiteCoefficientModuleInverseImage f Λ ⋙
    SheafOfModules.restrictScalars (inv (finiteCoefficientInverseImageMap f Λ))

/-- Additivity needed to map short complexes by the specified pullback.
Source: blueprint order 1236; Stacks Tags 03D2 and 04JC
(blueprint: prop-weil-pbc-proetale-constant-exact).
Proof: inverse image carries addition of abelian maps to addition, by preservation of
products and the addition operation. The module Kan extension is the same lifted inverse
image by its universal property. Restriction along c_f inverse changes only scalar actions,
so preserves this equality on maps. No commutativity of the ring is used. -/
theorem finiteCoefficientModulePullback_additive :
    (finiteCoefficientModulePullback f Λ).Additive := by
  let : (SheafOfModules.pushforward (finiteCoefficientModelRingUnit f Λ)).Additive :=
    ⟨by intros; rfl⟩
  let : (SheafOfModules.pullback (finiteCoefficientModelRingUnit f Λ)).Additive :=
    (SheafOfModules.pullbackPushforwardAdjunction
      (finiteCoefficientModelRingUnit f Λ)).left_adjoint_additive
  let : (Scheme.proEtaleModuleToModel (finiteCoefficientRingSheaf V Λ)).Additive :=
    ⟨by intros; rfl⟩
  let : (Scheme.proEtaleModuleFromModel (finiteCoefficientInverseRing f Λ)).Additive :=
    ⟨by intros; rfl⟩
  exact inferInstanceAs (Scheme.proEtaleModuleToModel (finiteCoefficientRingSheaf V Λ) ⋙
    SheafOfModules.pullback (finiteCoefficientModelRingUnit f Λ) ⋙
    Scheme.proEtaleModuleFromModel (finiteCoefficientInverseRing f Λ) ⋙
    SheafOfModules.restrictScalars (inv (finiteCoefficientInverseImageMap f Λ))).Additive

attribute [instance] finiteCoefficientModulePullback_additive

section
open Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
open Scheme
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
private noncomputable def finiteExactAbelianEquivalence (X : Scheme.{u}) :
    Sheaf (proEtaleModelTopology X) AddCommGrpCat.{u + 1} ≌
      Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  CategoryTheory.Equivalence.mk
    ((AsSmall.up : X.ProEt ⥤ proEtaleSiteModel X).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} (ProEt.topology X) (proEtaleModelTopology X))
    ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} (proEtaleModelTopology X) (ProEt.topology X))
    (Iso.refl _) (Iso.refl _)
@[irreducible] private noncomputable def finiteExactAbelianAdjunction
    {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (finiteExactAbelianEquivalence X).functor ⋙
      proEtaleSheafInverseImage f AddCommGrpCat.{u + 1} ⋙
      (finiteExactAbelianEquivalence Y).inverse ⊣
    (proEtaleModelBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (proEtaleModelTopology X) (proEtaleModelTopology Y) :=
  (proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).restrictFullyFaithful
    (finiteExactAbelianEquivalence X).fullyFaithfulFunctor
    (finiteExactAbelianEquivalence Y).fullyFaithfulFunctor
    (Iso.refl _) (Iso.refl _)
@[irreducible] private noncomputable def finiteExactAbelianPullbackIso {X Y : Scheme.{u}}
    (f : Y ⟶ X) :
    (finiteExactAbelianEquivalence X).inverse ⋙
      Functor.sheafPullbackConstruction.sheafPullback (proEtaleModelBaseChange f)
        AddCommGrpCat.{u + 1} (proEtaleModelTopology X) (proEtaleModelTopology Y) ⋙
      (finiteExactAbelianEquivalence Y).functor ≅
        proEtaleSheafInverseImage f AddCommGrpCat.{u + 1} := by
  let a := finiteExactAbelianAdjunction f
  let b := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (proEtaleModelBaseChange f) AddCommGrpCat.{u + 1}
      (proEtaleModelTopology X) (proEtaleModelTopology Y)
  exact Functor.isoWhiskerLeft (finiteExactAbelianEquivalence X).inverse
    (Functor.isoWhiskerRight (b.leftAdjointUniq a) (finiteExactAbelianEquivalence Y).functor)
set_option backward.defeqAttrib.useBackward false in
private noncomputable def finiteExactToModelForgetIso (X : Scheme.{u})
    (A : Sheaf (ProEt.topology X) RingCat.{u + 1}) :
    proEtaleModuleToModel A ⋙
      SheafOfModules.toSheaf
      (((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous RingCat.{u + 1}
          (proEtaleModelTopology X) (ProEt.topology X)).obj A) ≅
    SheafOfModules.toSheaf A ⋙ (finiteExactAbelianEquivalence X).inverse :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro M N g
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl)

set_option backward.defeqAttrib.useBackward false in
private noncomputable def finiteExactFromModelForgetIso (X : Scheme.{u})
    (A : Sheaf (ProEt.topology X) RingCat.{u + 1}) :
    proEtaleModuleFromModel A ⋙ SheafOfModules.toSheaf A ≅
    SheafOfModules.toSheaf
      (((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous RingCat.{u + 1}
        (proEtaleModelTopology X) (ProEt.topology X)).obj A) ⋙
      (finiteExactAbelianEquivalence X).functor :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro M N g
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl)

private theorem finiteExactUnderlying :
    Nonempty (finiteCoefficientModuleInverseImage f Λ ⋙
      SheafOfModules.toSheaf (finiteCoefficientInverseRing f Λ) ≅
      SheafOfModules.toSheaf (finiteCoefficientRingSheaf V Λ) ⋙
        proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}) := by
  let A := finiteCoefficientRingSheaf V Λ
  let B := finiteCoefficientInverseRing f Λ
  let : (AsSmall.down : proEtaleSiteModel V ⥤ V.ProEt).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := V.ProEt)).inverse.IsEquivalence
  let : (AsSmall.up : U.ProEt ⥤ proEtaleSiteModel U).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := U.ProEt)).functor.IsEquivalence
  let : PreservesFiniteLimits (proEtaleModelBaseChange f) := by
    change PreservesFiniteLimits (AsSmall.down ⋙ proEtaleBaseChange f ⋙ AsSmall.up)
    infer_instance
  let : RepresentablyFlat (proEtaleModelBaseChange f) := flat_of_preservesFiniteLimits _
  obtain ⟨pr, hpr⟩ := finiteExactRingPresentation f A
  obtain ⟨e, _⟩ := SheafOfModules.inverseImage_underlying_of_ring_presentation
    (finiteCoefficientModelRingUnit f Λ) pr (by ext W r; exact hpr W r)
  let L := SheafOfModules.pullback (finiteCoefficientModelRingUnit f Λ)
  let La := Functor.sheafPullbackConstruction.sheafPullback (proEtaleModelBaseChange f)
    AddCommGrpCat.{u + 1} (proEtaleModelTopology V) (proEtaleModelTopology U)
  let p := Functor.isoWhiskerLeft (proEtaleModuleToModel A ⋙ L) (finiteExactFromModelForgetIso U B)
  let s := Functor.isoWhiskerLeft (proEtaleModuleToModel A)
    (Functor.isoWhiskerRight e (finiteExactAbelianEquivalence U).functor)
  let t := Functor.isoWhiskerRight (finiteExactToModelForgetIso V A)
    (La ⋙ (finiteExactAbelianEquivalence U).functor)
  exact ⟨p ≪≫ s ≪≫ t ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.toSheaf A) (finiteExactAbelianPullbackIso f)⟩
end

/-- The specified pullback preserves kernels, cokernels and all short exact sequences.
Finite-limit and finite-colimit preservation encode the two exactness clauses in these
abelian categories; the final clause explicitly records short exact sequences.
Source: blueprint order 1236; Stacks Tags 04JC and 03DA
(blueprint: prop-weil-pbc-proetale-constant-exact).
Proof:
1. The arbitrary scheme map gives a morphism of small pro-etale sites, by
   def-weil-proetale-inverse-image. Apply lem-weil-pbc-site-pullback-abelian-exact
   after transporting to the equivalent small models of def-weil-pbc-proetale-site.
   Its abelian inverse image preserves kernels, cokernels and short exact sequences.
2. Finite-product preservation transports the ring multiplication and the left module
   action, together with all unit, associativity and distributivity identities.
   Naturality transports the linearity identities. This is the module Kan extension
   along the ring unit by its universal property. The canonical coefficient map of
   prop-weil-pbc-proetale-constant-ring-map is invertible; restrict the action along
   its inverse. Commutativity is unnecessary. The commutative tensor identification
   is stated separately below, using def-weil-pbc-proetale-operations.
3. By def-weil-sheaf-of-modules-category, module kernels and cokernels have the
   corresponding underlying abelian sheaves. The abelian comparison isomorphisms
   from step 1 are linear by their inclusions and quotient maps; their inverses are
   linear as inverses of bijective linear maps. Scalar transport leaves underlying
   abelian groups and maps unchanged. Thus kernels, cokernels and short exact
   sequences are preserved. In additive categories finite products are biproducts;
   kernel and cokernel preservation therefore give the two finite-preservation clauses. -/
theorem finiteCoefficientModulePullback_exact :
    PreservesFiniteLimits (finiteCoefficientModulePullback f Λ) ∧
    PreservesFiniteColimits (finiteCoefficientModulePullback f Λ) ∧
    ∀ S : ShortComplex (FiniteCoefficientModules V Λ),
      S.ShortExact → (S.map (finiteCoefficientModulePullback f Λ)).ShortExact := by
  let F := finiteCoefficientModulePullback f Λ
  let A := finiteCoefficientRingSheaf V Λ
  let B := finiteCoefficientRingSheaf U Λ
  let L := Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}
  let Q := SheafOfModules.toSheaf.{u + 1} B
  obtain ⟨e⟩ := finiteExactUnderlying f Λ
  let t₀ : F ⋙ Q ≅ finiteCoefficientModuleInverseImage f Λ ⋙
      SheafOfModules.toSheaf (finiteCoefficientInverseRing f Λ) :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      intro M N g
      simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      rfl)
  let t : F ⋙ Q ≅ SheafOfModules.toSheaf A ⋙ L := t₀ ≪≫ e
  let : PreservesFiniteLimits L := by
    change PreservesFiniteLimits (upperStar AddCommGrpCat.{u + 1} f)
    infer_instance
  let : PreservesColimitsOfSize.{0, 0} L :=
    (Scheme.proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).leftAdjoint_preservesColimits
  let : PreservesFiniteColimits L := inferInstance
  have hs (S : ShortComplex (FiniteCoefficientModules V Λ)) (hS : S.ShortExact) :
      (S.map F).ShortExact := by
    apply CategoryTheory.ShortExact.reflects_shortExact_of_faithful Q
    exact ShortComplex.shortExact_of_iso (S.mapNatIso t.symm)
      ((hS.map_of_exact (SheafOfModules.toSheaf A)).map_of_exact L)
  obtain ⟨hlim, hcol⟩ := (Functor.exact_tfae F).out 0 3 |>.mp hs
  exact ⟨hlim, hcol, hs⟩

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

variable {U V : Scheme.{u}} (f : U ⟶ V) (Λ : Type (u + 1))
  [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ]

/-- The canonical commutative constant coefficient presentation for the tensor comparison.
Source: blueprint order 1236 (blueprint: prop-weil-pbc-proetale-constant-exact). -/
noncomputable abbrev finiteCoefficientCommRing (T : Scheme.{u}) :=
  (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).obj (CommRingCat.of Λ)

/-- Compatibility of the commutative presentation with ring sheafification.
This supplies the construction obligation of the canonical coefficient comparison below.
Source: Stacks Tags 00W1 and 00YV; blueprint order 1236
(blueprint: prop-weil-pbc-proetale-constant-exact).
Proof: sheafification is the double-plus construction, formed from matching-family
limits and filtered colimits of covers. Forgetting commutativity preserves these
limits and filtered colimits and reflects isomorphisms. It therefore carries each
plus construction, its unit, and the resulting sheafification equivalences to their
ring-valued counterparts. This changes no ring data or constant sections. -/
theorem finiteCoefficientCommRing_preservesSheafification (T : Scheme.{u}) :
    (Scheme.ProEt.topology T).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := by
  constructor
  intro P Q g hg
  change (Scheme.ProEt.topology T).W
    (Functor.whiskerRight g (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
  have hi : Presheaf.IsLocallyInjective (Scheme.ProEt.topology T) g := hg.isLocallyInjective
  have hs : Presheaf.IsLocallySurjective (Scheme.ProEt.topology T) g := hg.isLocallySurjective
  apply ((Scheme.ProEt.topology T).W_iff_isLocallyBijective _).mpr
  constructor
  · exact ⟨fun x y h ↦ Presheaf.equalizerSieve_mem (Scheme.ProEt.topology T) g x y h⟩
  · exact ⟨fun x ↦ Presheaf.imageSieve_mem (Scheme.ProEt.topology T) g x⟩

attribute [instance] finiteCoefficientCommRing_preservesSheafification

/-- The canonical constant-preserving comparison from the commutative presentation.
Source: blueprint order 1236; Stacks Tag 0H7J
(blueprint: prop-weil-pbc-proetale-constant-exact). -/
noncomputable def finiteCoefficientCommRingComparison (T : Scheme.{u}) :
    (sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (finiteCoefficientCommRing Λ T) ⟶ finiteCoefficientRingSheaf T Λ :=
  (constantCommuteCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).hom.app (CommRingCat.of Λ) ≫
      finiteCoefficientConstantComparison Λ T

set_option linter.unusedSectionVars false in
/-- The canonical commutative coefficient map is invertible too.
Source: blueprint order 1236; Stacks Tags 0H7J and 09A5
(blueprint: prop-weil-pbc-proetale-constant-exact).
Proof: inverse image of the constant sheaf is constant, by the ring-sheaf adjunction
and the constant-preserving identifications of prop-weil-pbc-proetale-constant-ring-map.
Forgetting commutativity commutes with the inverse-image construction, since that
construction lifts the finite-product-preserving set inverse image. The resulting ring
map is the canonical invertible map of that proposition. The forgetful functor reflects
isomorphisms, so the commutative map is invertible. -/
theorem finiteCoefficientCommRingMap_isIso :
    IsIso (Scheme.proEtaleConstantInverseImageMap f CommRingCat.{u + 1}
      (CommRingCat.of Λ)) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.defeqAttrib.useBackward true in
  let G := Scheme.proEtaleBaseChange f
  let hV : IsTerminal (⊤_ V.ProEt) := terminalIsTerminal
  let hU := hV.isTerminalObj G _
  let aV := constantSheafAdj (Scheme.ProEt.topology V) CommRingCat.{u + 1} hV
  let adj := Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}
  let a := (aV.comp adj).ofNatIsoRight (Iso.refl _)
  let b := constantSheafAdj (Scheme.ProEt.topology U) CommRingCat.{u + 1} hU
  let e := a.leftAdjointUniq b
  have he : Scheme.proEtaleConstantInverseImageMap f CommRingCat.{u + 1}
      (CommRingCat.of Λ) = e.hom.app (CommRingCat.of Λ) := by
    apply (a.homEquiv _ _).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    simp only [a, Adjunction.homEquiv_ofNatIsoRight_apply, Iso.refl_hom,
      NatTrans.id_app, Category.comp_id, Adjunction.comp_homEquiv]
    dsimp [Scheme.proEtaleConstantInverseImageMap]
    rw [← Adjunction.homEquiv_counit]
    dsimp only [adj]
    rw [Equiv.apply_symm_apply]
    dsimp only [Scheme.proEtaleConstantDirectImageMap, aV, constantSheafAdj]
    rw [Adjunction.comp_homEquiv]
    change (constantPresheafAdj CommRingCat.{u + 1} hV).homEquiv _ _
      (((sheafificationAdjunction (Scheme.ProEt.topology V) CommRingCat.{u + 1}).homEquiv
        _ _)
        (((sheafificationAdjunction (Scheme.ProEt.topology V) CommRingCat.{u + 1}).homEquiv
          _ _).symm _)) = _
    rw [Equiv.apply_symm_apply]
    rfl
  rw [he]
  infer_instance

attribute [instance] finiteCoefficientCommRingMap_isIso

/-- The commutative tensor pullback is naturally isomorphic to the specified transport
pullback under the canonical constant-preserving coefficient identifications.
Source: blueprint order 1236; Stacks Tag 03D2 and tensor cancellation along an isomorphism
(blueprint: prop-weil-pbc-proetale-constant-exact).
Proof: the coefficient comparisons preserve constants and carry the canonical structure
map to the canonical commutative one, by prop-weil-pbc-proetale-constant-ring-map.
For a module M, the map from tensor pullback to transported inverse image sends
r tensor m to c inverse(r)m; its inverse sends m to 1 tensor m. The balancing relation
makes both composites identities. These maps commute with restrictions and module
morphisms, so extend by sheafification and give inverse natural transformations.
The coefficient comparisons are isomorphisms: constantCommuteCompose is an isomorphism,
and finiteCoefficientConstantComparison_isIso identifies constants with the prescribed
continuous-function sheaf. Thus both sides compare precisely the original module
categories through restriction of scalars, without changing the coefficient objects. -/
theorem finiteCoefficientModulePullback_tensor :
    Nonempty
      (finiteCoefficientModulePullback f Λ ⋙
          SheafOfModules.restrictScalars (finiteCoefficientCommRingComparison Λ U) ≅
        SheafOfModules.restrictScalars (finiteCoefficientCommRingComparison Λ V) ⋙
          Scheme.proEtaleRingModulePullback f
            (finiteCoefficientCommRing Λ V) (finiteCoefficientCommRing Λ U)
            (asIso (Scheme.proEtaleConstantInverseImageMap f CommRingCat.{u + 1}
              (CommRingCat.of Λ)))) := by
  sorry

end AlgebraicGeometry.ProEtale
