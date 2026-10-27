/- Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D7 -/
module

public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
import all Sheaf.Paper.ConstantCompletionEquivalence
import all Sheaf.Paper.ConstantCompletionCore
import all Sheaf.Paper.CompletedKoszulConstantTransport
import Sheaf.Paper.IntegralCoefficientCompletenessTransport
import all Sheaf.Paper.CompletedConstantCoefficientEquivalence
import all Sheaf.Paper.PbcCompletedPullbackActual
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Detection of maps into complete objects after constant restriction

Source: Stacks Tag 099I, proof of restriction-derived-complete-equivalence.
-/

@[expose] public section
set_option autoImplicit false
attribute [local instance] HasDerivedCategory.standard
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.PurStrictScalar

private theorem constantCompletion_map_injective
    {C : Type v} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Type v) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {M N : ConstantCompletion.D (ConstantCompletion.completed J A I)}
    (hN : ConstantCompletion.IsComplete (ConstantCompletion.projection J A I 0) N) :
    Function.Injective
      (fun a : M ⟶ N ↦ (ConstantCompletion.dres (ConstantCompletion.coefficientMap J A I)).map
        a) := by
  let U := ConstantCompletion.dres (ConstantCompletion.coefficientMap J A I)
  let CB := ConstantCompletion.completion J A I true
  let CA := ConstantCompletion.completion J A I false
  let ηB := ConstantCompletion.completionUnit J A I true
  let ηA := ConstantCompletion.completionUnit J A I false
  let P : ObjectProperty _ := ConstantCompletion.IsComplete (ConstantCompletion.quotient J A I 0)
  let Q : ObjectProperty _ := ConstantCompletion.IsComplete (ConstantCompletion.projection J A I 0)
  obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    I.fg_of_isNoetherianRing
  obtain ⟨_, _, hCB, hB, _⟩ := ConstantCompletion.koszul_quotient_reflector J A I true r a ha
  obtain ⟨_, _, _, hA, _⟩ := ConstantCompletion.koszul_quotient_reflector J A I false r a ha
  obtain ⟨e, ⟨he⟩⟩ := ConstantCompletion.equivalence J A I
  have : (Q.ι ⋙ U).Faithful := Functor.Faithful.of_iso he
  let NR : Q.FullSubcategory := ⟨N, hN⟩
  let MR : Q.FullSubcategory := ⟨CB.obj M, hCB M⟩
  have hUN : P (U.obj N) := by
    let := HasDerivedCategory.standard (ConstantCompletion.Mod (ConstantCompletion.constant J A))
    let := HasDerivedCategory.standard (ConstantCompletion.Mod (ConstantCompletion.completed J A I))
    let (V : C) := HasDerivedCategory.standard
      (ConstantCompletion.Mod ((ConstantCompletion.constant J A).over V))
    let (V : C) := HasDerivedCategory.standard
      (ConstantCompletion.Mod ((ConstantCompletion.completed J A I).over V))
    apply (siteDerivedRestrictScalars_locallyDerivedComplete_iff
      (ConstantCompletion.coefficientMap J A I)
      (ConstantCompletion.kernelIdeal (ConstantCompletion.quotient J A I 0)) N).mpr
    rw [ConstantCompletion.coefficientKernel_extension (J := J) A I]
    exact hN
  obtain ⟨χ, hχ⟩ := ConstantCompletion.completion_restriction (J := J) (A := A) (I := I)
  intro f g hfg
  obtain ⟨f', hf'⟩ := (hB M N hN).surjective f
  obtain ⟨g', hg'⟩ := (hB M N hN).surjective g
  change ηB.app M ≫ f' = f at hf'
  change ηB.app M ≫ g' = g at hg'
  have hres : U.map f' = U.map g' := by
    apply (cancel_epi (χ.hom.app M)).mp
    apply (hA (U.obj M) (U.obj N) hUN).injective
    change ηA.app (U.obj M) ≫ (χ.hom.app M ≫ U.map f') =
      ηA.app (U.obj M) ≫ (χ.hom.app M ≫ U.map g')
    rw [← Category.assoc, ← Category.assoc, hχ, ← U.map_comp, ← U.map_comp,
      hf', hg']
    exact hfg
  have h' : (ObjectProperty.homMk f' : MR ⟶ NR) = ObjectProperty.homMk g' :=
    (Q.ι ⋙ U).map_injective hres
  exact hf'.symm.trans ((congrArg (fun k : MR ⟶ NR ↦ ηB.app M ≫ k.hom) h').trans hg')

private theorem cechConstant_preserves_complete
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
    (β : Scheme.completedCechRing W (Scheme.pbcIntegralDatum l E) ≅
      ConstantCompletion.completed (Scheme.completedCechTopology W)
        (Scheme.PbcIntegralRing l E) (Scheme.pbcIntegralDatum l E).ideal)
    (hβ : ∀ (V : (Scheme.completedCechSite W)ᵒᵖ) (x : Scheme.PbcIntegralRing l E),
      β.hom.hom.app V ((Scheme.completedCechScalar W (Scheme.pbcIntegralDatum l E) x).val V) =
        (ConstantCompletion.algebraSection (ConstantCompletion.coefficientMap
          (Scheme.completedCechTopology W) (Scheme.PbcIntegralRing l E)
          (Scheme.pbcIntegralDatum l E).ideal) x).val V)
    (N : Scheme.PbcCompletedDerived W (Scheme.pbcIntegralDatum l E))
    (hN : Scheme.PbcIsIntrinsicallyComplete W (Scheme.pbcIntegralDatum l E) N) :
    ConstantCompletion.IsComplete (ConstantCompletion.projection
      (Scheme.completedCechTopology W) (Scheme.PbcIntegralRing l E)
      (Scheme.pbcIntegralDatum l E).ideal 0)
      ((Scheme.cechConstantDerivedEquiv W (Scheme.pbcIntegralDatum l E) β).functor.obj N) := by
  let d := Scheme.pbcIntegralDatum l E
  let : IsNoetherianRing (Scheme.PbcIntegralRing l E) := d.noetherian
  let a : Fin 1 → Scheme.PbcIntegralRing l E := fun _ ↦ Scheme.pbcUniformizer l E
  have ha : Ideal.span (Set.range a) = d.ideal := by
    change Ideal.span (Set.range (fun _ : Fin 1 ↦ Scheme.pbcUniformizer l E)) =
      Ideal.span {Scheme.pbcUniformizer l E}
    rw [Set.range_const]
  let F := Scheme.cechConstantDerivedEquiv W d β
  let C := Scheme.wfCompletionRepresentative W d N
  let eN := DerivedCategory.Q.objObjPreimageIso N
  obtain ⟨e, he⟩ := Scheme.completed_koszul_constant_transport W d β hβ F.functor
    (Iso.refl _) 1 a ha C
  let j := e ≪≫ (ConstantCompletion.completion (Scheme.completedCechTopology W)
    (Scheme.PbcIntegralRing l E) d.ideal true).mapIso (F.functor.mapIso eN)
  have hunit : F.functor.map (Scheme.wfCompletionUnit W d 1 a ha N) ≫ j.hom =
      (ConstantCompletion.completionUnit (Scheme.completedCechTopology W)
        (Scheme.PbcIntegralRing l E) d.ideal true).app (F.functor.obj N) := by
    change F.functor.map (eN.inv ≫ _) ≫ _ = _
    rw [Functor.map_comp]
    change (F.functor.map eN.inv ≫ _) ≫ e.hom ≫ _ = _
    rw [Category.assoc, ← Category.assoc _ e.hom, he]
    have hn := (ConstantCompletion.completionUnit (Scheme.completedCechTopology W)
      (Scheme.PbcIntegralRing l E) d.ideal true).naturality (F.functor.map eN.hom)
    dsimp only [Functor.id_map, Functor.comp_map] at hn
    simp only [Functor.mapIso_hom]
    erw [← hn, ← Category.assoc, ← F.functor.map_comp, eN.inv_hom_id,
      F.functor.map_id, Category.id_comp]
  have : IsIso (Scheme.wfCompletionUnit W d 1 a ha N) :=
    (Scheme.wfComplete_iff_presentation W d 1 a ha N).mpr hN
  obtain ⟨_, _, _, _, hcrit⟩ := ConstantCompletion.koszul_quotient_reflector
    (Scheme.completedCechTopology W) (Scheme.PbcIntegralRing l E) d.ideal true 1 a ha
  apply (hcrit (F.functor.obj N)).mp
  rw [← hunit]
  infer_instance

private theorem map_injective_of_square
    {B A B' A' : Type*} [Category* B] [Category* A] [Category* B'] [Category* A']
    (U : B ⥤ A) (F : B ⥤ B') (G : A ⥤ A') (V : B' ⥤ A') [F.Faithful]
    (α : U ⋙ G ≅ F ⋙ V) {M N : B}
    (h : Function.Injective (fun f : F.obj M ⟶ F.obj N ↦ V.map f)) :
    Function.Injective (fun f : M ⟶ N ↦ U.map f) := by
  intro f g hfg
  apply F.map_injective
  apply h
  apply (cancel_epi (α.hom.app M)).mp
  change α.hom.app M ≫ (F ⋙ V).map f = α.hom.app M ≫ (F ⋙ V).map g
  rw [← α.hom.naturality f, ← α.hom.naturality g]
  exact congrArg (fun k ↦ G.map k ≫ α.hom.app N) hfg

private theorem nativeConstant_map_injective
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
    [HasDerivedCategory (Scheme.pbcModules W
      (Scheme.adicLisseConstantRing W (Scheme.PbcIntegralRing l E)))]
    {M N : Scheme.PbcCompletedDerived W (Scheme.pbcIntegralDatum l E)}
    (hN : Scheme.PbcIsIntrinsicallyComplete W (Scheme.pbcIntegralDatum l E) N) :
    Function.Injective (fun f : M ⟶ N ↦
      (Scheme.pbcRestrict (Scheme.adicDatumScalar W
        (Scheme.intrinsicPresentationDatum (Scheme.pbcIntegralDatum l E)) ≫
          (Scheme.pbcCompletedComparison W
            (Scheme.pbcIntegralDatum l E)).hom)).mapDerivedCategory.map f) := by
  let d := Scheme.pbcIntegralDatum l E
  let A := Scheme.PbcIntegralRing l E
  let : IsNoetherianRing A := d.noetherian
  let J := Scheme.completedCechTopology W
  let R := Scheme.adicLisseConstantRing W A
  let B := Scheme.pbcAdicCompletion W d
  let c := Scheme.adicDatumScalar W (Scheme.intrinsicPresentationDatum d) ≫
    (Scheme.pbcCompletedComparison W d).hom
  let β := Scheme.CechConstantAlgebra.algebraIso W d.ideal (Scheme.pbcCompletedComparison W d)
  let γ := (Scheme.CechConstantAlgebra.constantsIso W).app (CommRingCat.of A)
  have hc : ∀ n : ℕ, c ≫ (Scheme.pbcCompletedComparison W d).inv ≫
      limit.π (Scheme.adicLisseRingSystem W d.ideal) (Opposite.op n) =
      (constantSheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1)))) := by
    intro n
    dsimp only [c]
    rw [Category.assoc, Iso.hom_inv_id_assoc]
    exact (Scheme.adicDatumScalar_exists W
      (Scheme.intrinsicPresentationDatum d)).exists.choose_spec n
  have hp : γ.hom ≫ ConstantCompletion.coefficientMap J A d.ideal =
      (Scheme.CechConstantAlgebra.pushRing W).map c ≫ β.hom :=
    (Scheme.CechConstantAlgebra.algebraIso_scalar W d.ideal
      (Scheme.pbcCompletedComparison W d) c hc).symm
  let ER := Scheme.smallModulesEquiv W R (ConstantCompletion.constant J A) γ
  let EB := Scheme.comparisonModulesEquiv W d
  let U := Scheme.pbcRestrict c
  let V := ConstantCompletion.res (ConstantCompletion.coefficientMap J A d.ideal)
  let T : ConstantCompletion.Mod (Scheme.completedCechRing W d) ⥤
      ConstantCompletion.Mod (ConstantCompletion.completed J A d.ideal) :=
    ConstantCompletion.res β.inv
  have : PreservesFiniteLimits T := (siteRestrictScalars_exact β.inv).1
  have : PreservesFiniteColimits T := (siteRestrictScalars_exact β.inv).2
  have : T.Additive := Functor.additive_of_preserves_binary_products _
  have : PreservesFiniteLimits V :=
    (siteRestrictScalars_exact (ConstantCompletion.coefficientMap J A d.ideal)).1
  have : PreservesFiniteColimits V :=
    (siteRestrictScalars_exact (ConstantCompletion.coefficientMap J A d.ideal)).2
  have : V.Additive := Functor.additive_of_preserves_binary_products _
  have : EB.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : (Scheme.completedCechModulesEquiv W d).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  have : ER.functor.Additive := Functor.additive_of_preserves_binary_products _
  let α : U ⋙ ER.functor ≅ EB.functor ⋙ V :=
    Scheme.restrictionTransport ER EB U V (Scheme.smallRestrictionComparison W γ β c
      (ConstantCompletion.coefficientMap J A d.ideal) hp)
  let αD := Functor.mapDerivedCategorySquareIso α
  let EB' := EB.mapDerivedCategory
  let eB0 : EB.functor ≅ (Scheme.completedCechModulesEquiv W d).functor ⋙
      T := Scheme.comparisonModulesEquiv_to_cech W d
  let eB : EB'.functor ≅ (Scheme.cechConstantDerivedEquiv W d β).functor :=
    Functor.mapDerivedCategoryNatIso eB0 ≪≫
      Functor.mapDerivedCategoryCompIso (Scheme.completedCechModulesEquiv W d).functor
        T
  have hβ : ∀ (T : (Scheme.completedCechSite W)ᵒᵖ) (x : A),
      β.hom.hom.app T ((Scheme.completedCechScalar W d x).val T) =
        (ConstantCompletion.algebraSection
          (ConstantCompletion.coefficientMap J A d.ideal) x).val T :=
    Scheme.comparisonCompletedRingIso_scalar W d
  have hcomplete := cechConstant_preserves_complete l E W β hβ N hN
  have : ConstantCompletion.IsComplete (ConstantCompletion.projection J A d.ideal 0)
      (EB'.functor.obj N) :=
    CategoryTheory.locallyDerivedRingedIdealComplete_of_iso _ _ (eB.app N) hcomplete
  exact map_injective_of_square U.mapDerivedCategory EB'.functor ER.functor.mapDerivedCategory
    V.mapDerivedCategory αD (constantCompletion_map_injective J A d.ideal this)

private theorem nativeScalar_detailed
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u}) :
    (Scheme.adicLisseForget W).map
      (Scheme.adicDatumScalar W (Scheme.intrinsicPresentationDatum (Scheme.pbcIntegralDatum l E)) ≫
        (Scheme.pbcCompletedComparison W (Scheme.pbcIntegralDatum l E)).hom) ≫
      (Scheme.integralDetailedCoefficientComparison W l E).hom =
        integralConstantToCompletionOfUniverses l E W := by
  let d := Scheme.pbcIntegralDatum l E
  let F := Scheme.adicLisseForget W
  let c := Scheme.adicDatumScalar W (Scheme.intrinsicPresentationDatum d) ≫
    (Scheme.pbcCompletedComparison W d).hom
  apply limit.hom_ext
  intro n
  change (F.map c ≫ (Scheme.integralDetailedCoefficientComparison W l E).hom) ≫
    limit.π (integralCoefficientSheafSystem l E W) n = _
  rw [Category.assoc]
  erw [(Scheme.integralDetailedCoefficientComparison_exists W l E).exists.choose_spec n.unop]
  rw [← Category.assoc, ← F.map_comp]
  have hc : c ≫ Scheme.pbcAdicProjection W d n.unop =
      (constantSheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n.unop + 1)))) ≫
          (Scheme.pbcLevelConstantComparison W d n.unop).hom := by
    change c ≫ Scheme.completedReductionProjection W d n.unop = _
    rw [Scheme.completedProjection_comparison]
    dsimp only [c]
    rw [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc]
    exact congrArg (fun k ↦ k ≫ (Scheme.pbcLevelConstantComparison W d n.unop).hom)
      ((Scheme.adicDatumScalar_exists W
        (Scheme.intrinsicPresentationDatum d)).exists.choose_spec n.unop)
  rw [hc]
  simp only [Functor.map_comp, Scheme.integralDetailedLevelComparison, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  change F.map _ ≫ F.map (Scheme.pbcLevelConstantComparison W d n.unop).hom ≫
    F.map (Scheme.pbcLevelConstantComparison W d n.unop).inv ≫ F.map _ = _
  erw [← F.map_comp_assoc (Scheme.pbcLevelConstantComparison W d n.unop).hom,
    Iso.hom_inv_id, F.map_id, Category.id_comp]
  rw [← F.map_comp, ← Functor.map_comp]
  rw [integralConstantToCompletionOfUniverses]
  erw [limit.lift_π]
  change F.map ((constantSheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}).map _) =
    integralConstantQuotientOfUniverses l E W n.unop
  unfold integralConstantQuotientOfUniverses
  congr 2
  ext x
  exact congrArg ULift.down
    ((Scheme.integralCoefficientULift_exists l E n.unop).exists.choose_spec x)

/-- Restriction to constant integral scalars detects maps into a derived-complete target.
Source: Stacks Tag 099I, proof of restriction-derived-complete-equivalence
(blueprint: lem-pur-complete-constant-restriction-map-injective).

Proof: put A = O_E and B = its completed constant sheaf. The coefficient map
is flat and is an isomorphism modulo every power of the uniformizer. Let K be
an extended Cech complex for that uniformizer. Its scalar extension K' satisfies
K = res K' in the derived category. Write Q = RHom_A(B, res N), with its B-action
from the first argument. Both N and Q are complete: for Q use tensor-Hom
adjunction to test against B[1/t], obtaining RHom_A(B[1/t],res N) = 0. Thus
Q = RHom_B(K',Q) = RHom_A(res K',res N). The canonical comparison N -> Q
becomes, after restriction and the identification res K' = K, precisely the
completion isomorphism res N -> RHom_A(K,res N). Restriction reflects
isomorphisms, so N -> Q is invertible. This is the unit of restriction followed
by its derived right adjoint. The adjunction then identifies Hom_B(M,N) with
Hom_A(res M,res N) for arbitrary M, and this bijection is restriction on maps.
In particular the restriction map is injective.
All identifications use the coefficient map and its quotient augmentations;
transport to the pro-etale site preserves them. This includes N = 0, M = 0,
empty sites and arbitrary shifts, and needs no completeness hypothesis on M. -/
theorem scalarConstantRestriction_complete_map_injective
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
    [HasDerivedCategory (SheafOfModules.{u + 1} (integralConstantRingOfUniverses l E W))]
    [(SheafOfModules.restrictScalars.{u + 1}
      (integralConstantToCompletionOfUniverses l E W)).Additive]
    [PreservesFiniteLimits (SheafOfModules.restrictScalars.{u + 1}
      (integralConstantToCompletionOfUniverses l E W))]
    [PreservesFiniteColimits (SheafOfModules.restrictScalars.{u + 1}
      (integralConstantToCompletionOfUniverses l E W))]
    {M N : DerivedCategory (scalarReductionSource l E W)}
    (hN : IsSfDerivedComplete l E W N) :
    Function.Injective (fun a : M ⟶ N ↦
      (SheafOfModules.restrictScalars.{u + 1}
        (integralConstantToCompletionOfUniverses l E W)).mapDerivedCategory.map a) := by
  let d := Scheme.pbcIntegralDatum l E
  let c := Scheme.adicDatumScalar W (Scheme.intrinsicPresentationDatum d) ≫
    (Scheme.pbcCompletedComparison W d).hom
  let H := SheafOfModules.restrictScalars.{u + 1}
    (Scheme.integralDetailedCoefficientComparison W l E).hom
  have : PreservesFiniteLimits H := (Scheme.integralDetailedCoefficientRestriction_exact W l E).1
  have : PreservesFiniteColimits H := (Scheme.integralDetailedCoefficientRestriction_exact W l E).2
  let U := SheafOfModules.restrictScalars.{u + 1}
    (integralConstantToCompletionOfUniverses l E W)
  let V := Scheme.pbcRestrict c
  have hc := nativeScalar_detailed l E W
  let eM (P : scalarReductionSource l E W) : (H ⋙ V).obj P ≅ U.obj P :=
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun T ↦
        (ModuleCat.restrictScalarsComp'App
          (((Scheme.adicLisseForget W).map c).hom.app T).hom
          ((Scheme.integralDetailedCoefficientComparison W l E).hom.hom.app T).hom
          ((integralConstantToCompletionOfUniverses l E W).hom.app T).hom
          ((congrArg (fun f ↦ (f.hom.app T).hom) hc).symm) (P.val.obj T)).symm)
        (fun {_ _} _ ↦ by ext x; rfl))
  let e : H ⋙ V ≅ U := NatIso.ofComponents eM (by intro P Q f; ext T x; rfl)
  let eD : H.mapDerivedCategory ⋙ V.mapDerivedCategory ≅ U.mapDerivedCategory :=
    (Functor.mapDerivedCategoryCompIso H V).symm ≪≫ Functor.mapDerivedCategoryNatIso e
  have hcomplete := (purDetailedTransport_complete_iff l E W N).mp hN
  have hinj := nativeConstant_map_injective l E W
    (M := H.mapDerivedCategory.obj M) (N := H.mapDerivedCategory.obj N) hcomplete
  have : H.mapDerivedCategory.Faithful :=
    inferInstanceAs (Scheme.integralDetailedTransport W l E).Faithful
  intro f g hfg
  apply H.mapDerivedCategory.map_injective
  apply hinj
  apply (cancel_mono (eD.hom.app N)).mp
  change (H.mapDerivedCategory ⋙ V.mapDerivedCategory).map f ≫ eD.hom.app N =
    (H.mapDerivedCategory ⋙ V.mapDerivedCategory).map g ≫ eD.hom.app N
  rw [eD.hom.naturality f, eD.hom.naturality g]
  exact congrArg (fun k ↦ eD.hom.app M ≫ k) hfg

end WeilConjectures.PurStrictScalar
