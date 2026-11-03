/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ModuleDerivedCategory
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization

/-!
# Open pro-etale pullback evaluation and its specified adjunction unit

Source: Stacks Project, Tags 09BN, 00VE, 00WH, 00WX, 00XZ and 03D3
(blueprint: lem-pur-proetale-open-unit-evaluation).

The pullback and unit are the published small-model module constructions.
The coefficient comparison below is normalized on constant sections.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Compose a pro-etale object's structure map with an open immersion, retaining its
underlying scheme and arrows. Source: Stacks Project, Tags 00XZ and 09BN
(blueprint: lem-pur-proetale-open-unit-evaluation). -/
def proEtaleOpenComposition {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    U.ProEt ⥤ X.ProEt :=
  MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)

/-- The first projection from the base-changed object, viewed over the ambient scheme.
It is the counit of the existing composition/base-change adjunction.
Source: Stacks Project, Tags 00VE and 09BN
(blueprint: lem-pur-proetale-open-unit-evaluation). -/
noncomputable def proEtaleOpenSectionProjection {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (V : X.ProEt) :
    (proEtaleOpenComposition j).obj ((proEtaleBaseChange j).obj V) ⟶ V :=
  (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
    (inferInstance : WeaklyEtale j) trivial).counit.app V

private noncomputable def openRingComparison {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (A : Type u) [CommRing A] :
    (proEtaleConstantRing U A).obj ≅
      (proEtaleOpenComposition j).op ⋙ (proEtaleConstantRing X A).obj := by
  let G := proEtaleOpenComposition j
  have : G.IsContinuous (ProEt.topology U) (ProEt.topology X) :=
    ProEt.isContinuous_overMap (inferInstance : WeaklyEtale j)
  have : G.IsCocontinuous (ProEt.topology U) (ProEt.topology X) :=
    ProEt.isCocontinuous_overMap (inferInstance : WeaklyEtale j)
  exact (sheafToPresheaf _ _).mapIso
    ((G.pushforwardContinuousSheafificationCompatibility CommRingCat.{u + 1}
      (ProEt.topology U) (ProEt.topology X)).app
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A))))

private theorem openRingComparison_constant {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (A : Type u) [CommRing A]
    (W : U.ProEt) (a : ULift.{u + 1, u} A) :
    ((openRingComparison j A).hom.app (op W))
        ((toSheafify (ProEt.topology U)
          ((Functor.const U.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{u + 1, u} A)))).app (op W) a) =
      (toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1, u} A)))).app
            (op ((proEtaleOpenComposition j).obj W)) a := by
  let G := proEtaleOpenComposition j
  have : G.IsContinuous (ProEt.topology U) (ProEt.topology X) :=
    ProEt.isContinuous_overMap (inferInstance : WeaklyEtale j)
  have : G.IsCocontinuous (ProEt.topology U) (ProEt.topology X) :=
    ProEt.isCocontinuous_overMap (inferInstance : WeaklyEtale j)
  exact congrArg (fun f ↦ (f.app (op W)) a)
    (G.toSheafify_pullbackSheafificationCompatibility CommRingCat.{u + 1}
      (ProEt.topology U) (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A))))

private theorem ringDirectImage_constant {U X : Scheme.{u}}
    (j : U ⟶ X) (A : Type u) [CommRing A] :
    proEtaleRingDirectImageMap j (proEtaleConstantRing X A) (proEtaleConstantRing U A)
        (proEtaleConstantRingComparison j A) = proEtaleCoefficientDirectImageMap j A := by
  change (proEtaleSheafAdjunction j CommRingCat.{u + 1}).homEquiv _ _
    (proEtaleCoefficientInverseImageMap j A) = _
  change (proEtaleSheafAdjunction j CommRingCat.{u + 1}).homEquiv _ _
    (((proEtaleSheafAdjunction j CommRingCat.{u + 1}).homEquiv _ _).symm
      (proEtaleCoefficientDirectImageMap j A)) = _
  exact Equiv.apply_symm_apply _ _

/-- Open inverse image is evaluation on the same scheme over the ambient base,
with both naturalities, coefficient linearity and the specified unit normalization.
The ring-presheaf isomorphism `d` is the constant-section-preserving restriction
identification of the localization lemma; its naturality is built into its type.

Source: Stacks Project, Tags 09BN, 00VE, 00WH, 00WX, 00XZ and 03D3
(blueprint: lem-pur-proetale-open-unit-evaluation).

Proof plan:
1. For W over U put v(W) = (W → U → X). The canonical map W → u(v(W))
   is invertible because j is a monomorphism. The pair (v(W), e_W) is initial
   in the actual inverse-image index: a map to (V, phi) must be pr_V phi,
   and the two pullback projections prove existence and uniqueness.
2. The restriction maps M(V) → M(v(W)) form a cocone. Its map from the
   colimit is inverse to the coprojection at this initial object. Check both
   composites on coprojections, using their colimit relations.
3. These maps commute with restrictions in W and morphisms in M. The target
   is already a sheaf by weakly-etale localization. Extend the comparison and
   its inverse through sheafification; its universal property proves the inverse
   laws and both naturalities.
4. Transport the indexing object to the specified compatible small models.
   Full faithfulness preserves its initiality. A change of representative cancels
   in the restriction formula, so the same comparison identifies the actual
   published inverse image and adjunction.
5. Apply the calculation to coefficients. The canonical coefficient map sends
   each constant to itself (the constant-ring-map and constant-exact nodes).
   Uniqueness of the constant-presheaf sheafification extension identifies it
   with the inverse of the localization restriction comparison d.
6. The module comparison respects scalar actions on the cocones and hence after
   sheafification. Extend over the sheaf tensor by r tensor m ↦ r • theta(m).
   The inverse is n ↦ 1 tensor theta⁻¹(n); balancing and step 5 prove the two
   inverse laws. These maps are natural in both variables.
7. The Kan adjunction unit is the coprojection indexed by (V, id), followed
   by sheafification and the tensor unit. Under the comparison at u(V), the
   unique indexing arrow is the first projection u(V) → V. Therefore this
   specified unit becomes exactly restriction along that projection. No
   quasi-compactness, support or constructibility condition is used. -/
theorem proEtaleOpenUnitEvaluation {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type u) [CommRing A] [Finite A] :
    ∃ d : (proEtaleConstantRing U A).obj ≅
        (proEtaleOpenComposition j).op ⋙ (proEtaleConstantRing X A).obj,
      (∀ (W : U.ProEt) (a : ULift.{u + 1, u} A),
        (d.hom.app (op W))
            ((toSheafify (ProEt.topology U)
              ((Functor.const U.ProEtᵒᵖ).obj
                (CommRingCat.of (ULift.{u + 1, u} A)))).app (op W) a) =
          (toSheafify (ProEt.topology X)
            ((Functor.const X.ProEtᵒᵖ).obj
              (CommRingCat.of (ULift.{u + 1, u} A)))).app
                (op ((proEtaleOpenComposition j).obj W)) a) ∧
      ∃ rho : ∀ (M : proEtaleRingModules X (proEtaleConstantRing X A)) (W : U.ProEt),
          ((proEtaleConstantRingPullback A j).obj M).val.obj (op W) ≃+
            M.val.obj (op ((proEtaleOpenComposition j).obj W)),
        (∀ (M : proEtaleRingModules X (proEtaleConstantRing X A)) (W : U.ProEt)
          (r : (proEtaleConstantRing U A).obj.obj (op W))
          (m : ((proEtaleConstantRingPullback A j).obj M).val.obj (op W)),
          rho M W (r • m) = (d.hom.app (op W) r) • rho M W m) ∧
        (∀ (M : proEtaleRingModules X (proEtaleConstantRing X A))
          (W W' : U.ProEt) (b : W' ⟶ W)
          (m : ((proEtaleConstantRingPullback A j).obj M).val.obj (op W)),
          rho M W' (((proEtaleConstantRingPullback A j).obj M).val.map b.op m) =
            M.val.map ((proEtaleOpenComposition j).map b).op (rho M W m)) ∧
        (∀ (M N : proEtaleRingModules X (proEtaleConstantRing X A)) (h : M ⟶ N)
          (W : U.ProEt) (m : ((proEtaleConstantRingPullback A j).obj M).val.obj (op W)),
          rho N W (((proEtaleConstantRingPullback A j).map h).val.app (op W) m) =
            h.val.app (op ((proEtaleOpenComposition j).obj W)) (rho M W m)) ∧
        (∀ (M : proEtaleRingModules X (proEtaleConstantRing X A))
          (V : X.ProEt) (m : M.val.obj (op V)),
          rho M ((proEtaleBaseChange j).obj V)
              (((proEtaleConstantRingAdjunction A j).unit.app M).val.app (op V) m) =
            M.val.map (proEtaleOpenSectionProjection j V).op m) := by
  let F := proEtaleOpenComposition j
  let G := proEtaleBaseChange j
  have : F.IsContinuous (ProEt.topology U) (ProEt.topology X) :=
    ProEt.isContinuous_overMap (inferInstance : WeaklyEtale j)
  let adj : F ⊣ G := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
    (inferInstance : WeaklyEtale j) trivial
  let R := proEtaleConstantRing X A
  let S := proEtaleConstantRing U A
  let d := openRingComparison j A
  let φ : ((sheafCompose (ProEt.topology U) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) ⟶
      (F.sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology U) (ProEt.topology X)).obj
          ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) :=
    ⟨Functor.whiskerRight d.hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  let ψ : ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ⟶
      (G.sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology X) (ProEt.topology U)).obj
          ((sheafCompose (ProEt.topology U) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) :=
    ⟨Functor.whiskerRight
      (proEtaleRingDirectImageMap j R S (proEtaleConstantRingComparison j A)).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  let ηX := toSheafify (ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))
  let ηU := toSheafify (ProEt.topology U)
    ((Functor.const U.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))
  have hψ : ηX ≫ (proEtaleCoefficientDirectImageMap j A).hom =
      Functor.whiskerLeft G.op ηU := by
    exact toSheafify_sheafifyLift (ProEt.topology X) _ _
  have H₁c : Functor.whiskerRight (NatTrans.op adj.counit) R.obj =
      (proEtaleCoefficientDirectImageMap j A).hom ≫ G.op.whiskerLeft d.hom := by
    apply sheafify_hom_ext (ProEt.topology X) _ _
      ((G.sheafPushforwardContinuous CommRingCat.{u + 1}
        (ProEt.topology X) (ProEt.topology U)).obj
          ((F.sheafPushforwardContinuous CommRingCat.{u + 1}
            (ProEt.topology U) (ProEt.topology X)).obj R)).property
    apply NatTrans.ext
    funext V
    ext a
    change R.obj.map (adj.counit.app V.unop).op (ηX.app V a) =
      d.hom.app (op (G.obj V.unop))
        ((proEtaleCoefficientDirectImageMap j A).hom.app V (ηX.app V a))
    rw [show (proEtaleCoefficientDirectImageMap j A).hom.app V (ηX.app V a) =
      ηU.app (op (G.obj V.unop)) a from congrArg (fun f ↦ f.app V a) hψ]
    rw [openRingComparison_constant]
    exact (congrArg (fun f ↦ f a) (ηX.naturality (adj.counit.app V.unop).op)).symm
  have H₂c : d.hom ≫ F.op.whiskerLeft (proEtaleCoefficientDirectImageMap j A).hom ≫
      Functor.whiskerRight (NatTrans.op adj.unit) S.obj = 𝟙 S.obj := by
    apply sheafify_hom_ext (ProEt.topology U) _ _ S.property
    apply NatTrans.ext
    funext W
    ext a
    change S.obj.map (adj.unit.app W.unop).op
      ((proEtaleCoefficientDirectImageMap j A).hom.app (op (F.obj W.unop))
        (d.hom.app W (ηU.app W a))) = ηU.app W a
    rw [openRingComparison_constant]
    rw [show (proEtaleCoefficientDirectImageMap j A).hom.app (op (F.obj W.unop))
      (ηX.app (op (F.obj W.unop)) a) = ηU.app (op (G.obj (F.obj W.unop))) a from
        congrArg (fun f ↦ f.app (op (F.obj W.unop)) a) hψ]
    exact (congrArg (fun f ↦ f a) (ηU.naturality (adj.unit.app W.unop).op)).symm
  have H₁ : Functor.whiskerRight (NatTrans.op adj.counit)
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj =
          ψ.hom ≫ G.op.whiskerLeft φ.hom := by
    dsimp only [ψ]
    rw [ringDirectImage_constant]
    exact congrArg (fun f ↦ Functor.whiskerRight f
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) H₁c
  have H₂ : φ.hom ≫ F.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op adj.unit)
        ((sheafCompose (ProEt.topology U)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S).obj = 𝟙 _ := by
    dsimp only [ψ]
    rw [ringDirectImage_constant]
    exact congrArg (fun f ↦ Functor.whiskerRight f
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) H₂c
  let radj := SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂
  let e := (proEtaleConstantRingAdjunction A j).leftAdjointUniq radj
  refine ⟨d, openRingComparison_constant j A, ?_⟩
  let rho : ∀ (M : proEtaleRingModules X R) (W : U.ProEt),
      ((proEtaleConstantRingPullback A j).obj M).val.obj (op W) ≃+
        M.val.obj (op (F.obj W)) := fun M W ↦
    { toFun := ((e.app M).hom.val.app (op W))
      invFun := ((e.app M).inv.val.app (op W))
      left_inv := by
        intro m
        exact congrArg (fun f ↦ f.val.app (op W) m) (e.app M).hom_inv_id
      right_inv := by
        intro m
        exact congrArg (fun f ↦ f.val.app (op W) m) (e.app M).inv_hom_id
      map_add' := map_add _ }
  refine ⟨rho, ?_, ?_, ?_, ?_⟩
  · intro M W r m
    exact (((e.app M).hom.val.app (op W)).hom.map_smul r m)
  · intro M W W' b m
    exact PresheafOfModules.naturality_apply (e.app M).hom.val b.op m
  · intro M N h W m
    exact congrArg (fun f ↦ f.val.app (op W) m) (e.hom.naturality h)
  · intro M V m
    exact congrArg (fun f ↦ f.val.app (op V) m)
      ((proEtaleConstantRingAdjunction A j).unit_leftAdjointUniq_hom_app radj M)

end AlgebraicGeometry.Scheme
