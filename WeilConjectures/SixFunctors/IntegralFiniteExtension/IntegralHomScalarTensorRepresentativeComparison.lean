/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralFiniteExtension.IntegralHomTensorAdjointNaturality
public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import WeilConjectures.SixFunctors.IntegralFiniteExtension.IntegralScalarTensorOrdinaryTransport
import WeilConjectures.SixFunctors.IntegralFiniteExtension.IntegralScalarComplexCounitComparison
import all WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportScalarTensor

/-! # Representative normalization of the transported scalar tensor comparison

Source: paragraph 5 of the finite coefficient extension proof; Stacks Project,
Tags 06YY, 07A4 and 08J9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u a₀ b₀ v₀ w₀
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralFiniteExtension

/-- Conjugate a tensor comparison by two tensor isomorphisms with swapped inputs.
Source: the formal transport in Stacks Tags 06YY and 07A4
(blueprint: new-sf-integral-hom-scalar-tensor-representatives). -/
def scalarTensorTransportOfSwap
    {A : Type a₀} [Category.{v₀} A] {B : Type b₀} [Category.{w₀} B]
    {TA SA : A × A ⥤ A} {TB SB : B × B ⥤ B}
    (i : TA ≅ CategoryTheory.Prod.swap A A ⋙ SA)
    (j : TB ≅ CategoryTheory.Prod.swap B B ⋙ SB)
    (G : A ⥤ B) (μ : SA ⋙ G ≅ G.prod G ⋙ SB) :
    TA ⋙ G ≅ G.prod G ⋙ TB :=
  Functor.isoWhiskerRight i G ≪≫
    Functor.isoWhiskerLeft (CategoryTheory.Prod.swap A A) μ ≪≫
    Functor.isoWhiskerLeft (G.prod G) j.symm

private theorem scalarTensorTransportOfSwap_app
    {A : Type a₀} [Category.{v₀} A] {B : Type b₀} [Category.{w₀} B]
    {TA SA : A × A ⥤ A} {TB SB : B × B ⥤ B}
    (i : TA ≅ CategoryTheory.Prod.swap A A ⋙ SA)
    (j : TB ≅ CategoryTheory.Prod.swap B B ⋙ SB)
    (G : A ⥤ B) (μ : SA ⋙ G ≅ G.prod G ⋙ SB)
    (X Y : A) (X' Y' : B) (cX : G.obj X ⟶ X') (cY : G.obj Y ⟶ Y') :
    (scalarTensorTransportOfSwap i j G μ).hom.app (X, Y) ≫
        TB.map (Prod.mkHom cX cY) ≫ j.hom.app (X', Y') =
      G.map (i.hom.app (X, Y)) ≫ μ.hom.app (Y, X) ≫ SB.map (Prod.mkHom cY cX) := by
  rw [j.hom.naturality]
  simp only [scalarTensorTransportOfSwap, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom,
    Functor.comp_obj, Functor.prod_obj, Category.assoc]
  change G.map (i.hom.app (X, Y)) ≫ μ.hom.app (Y, X) ≫
    j.inv.app (G.obj X, G.obj Y) ≫ j.hom.app (G.obj X, G.obj Y) ≫
      SB.map (Prod.mkHom cY cX) = _
  rw [Iso.inv_hom_id_app_assoc]

private theorem scalarTensorTransportOfSwap_app_comparison
    {A : Type a₀} [Category.{v₀} A] {B : Type b₀} [Category.{w₀} B]
    {TA SA : A × A ⥤ A} {TB SB : B × B ⥤ B}
    (i : TA ≅ CategoryTheory.Prod.swap A A ⋙ SA)
    (j : TB ≅ CategoryTheory.Prod.swap B B ⋙ SB)
    (F G : A ⥤ B) (e : F ≅ G) (μ : SA ⋙ F ≅ F.prod F ⋙ SB)
    (X Y : A) (DX DY X' Y' : B)
    (dX : F.obj X ⟶ DX) (dY : F.obj Y ⟶ DY)
    (tX : DX ⟶ X') (tY : DY ⟶ Y')
    (cX : G.obj X ⟶ X') (cY : G.obj Y ⟶ Y')
    (hX : e.hom.app X ≫ cX = dX ≫ tX)
    (hY : e.hom.app Y ≫ cY = dY ≫ tY) :
    (scalarTensorTransportOfSwap i j G
      (Functor.isoWhiskerLeft SA e.symm ≪≫ μ ≪≫
        Functor.isoWhiskerRight (NatIso.prod e e) SB)).hom.app (X, Y) ≫
        TB.map (Prod.mkHom cX cY) ≫ j.hom.app (X', Y') =
      G.map (i.hom.app (X, Y)) ≫ e.inv.app (SA.obj (Y, X)) ≫
        μ.hom.app (Y, X) ≫ SB.map (Prod.mkHom dY dX) ≫
          SB.map (Prod.mkHom tY tX) := by
  rw [scalarTensorTransportOfSwap_app]
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Iso.symm_hom, Category.assoc]
  change G.map (i.hom.app (X, Y)) ≫ e.inv.app (SA.obj (Y, X)) ≫
    μ.hom.app (Y, X) ≫ SB.map (Prod.mkHom (e.hom.app Y) (e.hom.app X)) ≫
      SB.map (Prod.mkHom cY cX) = _
  rw [← SB.map_comp]
  change G.map (i.hom.app (X, Y)) ≫ e.inv.app (SA.obj (Y, X)) ≫
    μ.hom.app (Y, X) ≫ SB.map (Prod.mkHom (e.hom.app Y ≫ cY)
      (e.hom.app X ≫ cX)) = _
  rw [hX, hY]
  change G.map (i.hom.app (X, Y)) ≫ e.inv.app (SA.obj (Y, X)) ≫
    μ.hom.app (Y, X) ≫ SB.map (Prod.mkHom dY dX ≫ Prod.mkHom tY tX) = _
  rw [SB.map_comp]

private theorem map_three_comp_eq
    {A : Type a₀} [Category.{v₀} A] {B : Type b₀} [Category.{w₀} B]
    (F : A ⥤ B) {V W U Z T Y : A}
    (f : V ⟶ W) (g : W ⟶ U) (h : U ⟶ Z)
    (i : V ⟶ T) (j : T ⟶ Y) (k : Y ⟶ Z)
    (e : f ≫ g ≫ h = i ≫ j ≫ k) :
    F.map f ≫ F.map g ≫ F.map h = F.map i ≫ F.map j ≫ F.map k := by
  simpa only [Functor.map_comp] using congrArg F.map e

private theorem scalarTensorRepresentativePasting
    {A : Type a₀} [Category.{v₀} A] {B : Type b₀} [Category.{w₀} B]
    (F G : A ⥤ B) (e : F ≅ G)
    {V W I J : A} {N₀ N₁ N₂ H K M Z V' W' I' : B}
    (ra : V ⟶ I) (ia : I ⟶ J) (s : V ⟶ W) (m : W ⟶ J)
    (η : G.obj I ⟶ I') (ib : I' ⟶ N₂) [Mono ib]
    (rb : V' ⟶ I') (sb : V' ⟶ W') (mb : W' ⟶ N₂)
    (μ : F.obj J ⟶ N₀) (d : N₀ ⟶ N₁) (v : N₁ ⟶ N₂)
    (δV : F.obj V ⟶ H) (δW : F.obj W ⟶ K)
    (fs : H ⟶ K) (κ : K ⟶ M) (mF : M ⟶ N₁) (τ : M ⟶ W')
    (t : H ⟶ Z) (β : Z ⟶ V') (c : G.obj V ⟶ Z)
    (hrep : ra ≫ ia = s ≫ m) (hrep' : rb ≫ ib = sb ≫ mb)
    (hη : η ≫ ib = G.map ia ≫ e.inv.app J ≫ μ ≫ d ≫ v)
    (hn : F.map m ≫ μ ≫ d = δW ≫ κ ≫ mF)
    (hnat : mF ≫ v = τ ≫ mb)
    (hδ : F.map s ≫ δW = δV ≫ fs)
    (ho : fs ≫ κ ≫ τ = t ≫ β ≫ sb)
    (hc : e.hom.app V ≫ c = δV ≫ t) :
    G.map ra ≫ η = c ≫ β ≫ rb := by
  apply (cancel_mono ib).1
  simp only [Category.assoc]
  rw [hη, ← G.map_comp_assoc, hrep, G.map_comp]
  rw [hrep']
  apply (cancel_epi (e.hom.app V)).1
  simp only [Category.assoc]
  rw [← e.hom.naturality_assoc, ← e.hom.naturality_assoc]
  simp only [Iso.hom_inv_id_app_assoc]
  have hc' := congrArg (fun f ↦ f ≫ β ≫ sb ≫ mb) hc
  simp only [Category.assoc] at hc'
  rw [hc']
  have hn' := congrArg (fun f ↦ f ≫ v) hn
  simp only [Category.assoc] at hn'
  rw [hn']
  rw [hnat]
  rw [← Category.assoc (F.map s) δW]
  rw [hδ]
  simpa only [Category.assoc] using congrArg (fun f ↦ δV ≫ f ≫ mb) ho

private theorem scalarTensorTransportOfSwap_representative
    {A : Type a₀} [Category.{v₀} A] {B : Type b₀} [Category.{w₀} B]
    {TA SA : A × A ⥤ A} {TB SB : B × B ⥤ B}
    (i : TA ≅ CategoryTheory.Prod.swap A A ⋙ SA)
    (j : TB ≅ CategoryTheory.Prod.swap B B ⋙ SB)
    (F G : A ⥤ B) (e : F ≅ G) (μ : SA ⋙ F ≅ F.prod F ⋙ SB)
    (P Q : A) (FP FQ GP GQ : B)
    (dP : F.obj P ⟶ FP) (dQ : F.obj Q ⟶ FQ)
    (tP : FP ⟶ GP) (tQ : FQ ⟶ GQ)
    (cP : G.obj P ⟶ GP) (cQ : G.obj Q ⟶ GQ)
    (hcP : e.hom.app P ≫ cP = dP ≫ tP)
    (hcQ : e.hom.app Q ≫ cQ = dQ ≫ tQ)
    {V W : A} {H K M Z U U' : B}
    (ra : V ⟶ TA.obj (P, Q)) (s : V ⟶ W) (m : W ⟶ SA.obj (Q, P))
    (rb : U ⟶ TB.obj (GP, GQ)) (sb : U ⟶ U') (mb : U' ⟶ SB.obj (GQ, GP))
    (δV : F.obj V ⟶ H) (δW : F.obj W ⟶ K)
    (fs : H ⟶ K) (κ : K ⟶ M) (mF : M ⟶ SB.obj (FQ, FP)) (τ : M ⟶ U')
    (t : H ⟶ Z) (β : Z ⟶ U) (c : G.obj V ⟶ Z)
    (hrep : ra ≫ i.hom.app (P, Q) = s ≫ m)
    (hrep' : rb ≫ j.hom.app (GP, GQ) = sb ≫ mb)
    (hn : F.map m ≫ μ.hom.app (Q, P) ≫ SB.map (Prod.mkHom dQ dP) = δW ≫ κ ≫ mF)
    (hnat : mF ≫ SB.map (Prod.mkHom tQ tP) = τ ≫ mb)
    (hδ : F.map s ≫ δW = δV ≫ fs)
    (ho : fs ≫ κ ≫ τ = t ≫ β ≫ sb)
    (hc : e.hom.app V ≫ c = δV ≫ t) :
    G.map ra ≫ (scalarTensorTransportOfSwap i j G
      (Functor.isoWhiskerLeft SA e.symm ≪≫ μ ≪≫
        Functor.isoWhiskerRight (NatIso.prod e e) SB)).hom.app (P, Q) ≫
        TB.map (Prod.mkHom cP cQ) = c ≫ β ≫ rb := by
  exact scalarTensorRepresentativePasting F G e ra (i.hom.app (P, Q)) s m
    (_ ≫ TB.map (Prod.mkHom cP cQ)) (j.hom.app (GP, GQ)) rb sb mb
    (μ.hom.app (Q, P)) (SB.map (Prod.mkHom dQ dP)) (SB.map (Prod.mkHom tQ tP))
    δV δW fs κ mF τ t β c hrep hrep'
    (by
      have h := scalarTensorTransportOfSwap_app_comparison i j F G e μ
        P Q FP FQ GP GQ dP dQ tP tQ cP cQ hcP hcQ
      convert h using 1
      all_goals first | rfl | exact Category.assoc _ _ _)
    hn hnat hδ ho hc

attribute [local irreducible] scalarIntegralClosed
  completedIntegralCommRingSheafUnrestricted completedIntegralCoefficientSheafUnrestricted
  HasDerivedCategory.standard tensorAdjointComparison scalarIntegralModels
  scalarOrdinaryTensorChain completedCoefficientMap completedScalarCounit pbcComplexCounit
  integralOrdinaryScalar tensorComplexSwap SheafOfModules.monoidalCategory
  CategoryTheory.Functor.mapBifunctorHomologicalComplex HomologicalComplex₂.total
  PurCompactSupport.scalarTensorTotal CategoryTheory.Functor.mapHomologicalComplex
  CategoryTheory.Functor.mapDerivedCategory

/-- Transport the canonical tensor comparison using the explicitly specified
adjoint comparisons in both coefficient categories. No witness is chosen here.
Source: Stacks Tags 06YY and 07A4
(blueprint: new-sf-integral-hom-scalar-tensor-representatives). -/
def scalarTensorTransport
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (b : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l L X))
    (e : integralOrdinaryDerivedScalar l E L ι X ≅
      completedDerivedScalarExtension.{u, u} l E L ι X) :
    a.tensor ⋙ pbcDerivedExtend (completedCoefficientMap l E L ι X) ≅
      ((pbcDerivedExtend (completedCoefficientMap l E L ι X)).prod
        (pbcDerivedExtend (completedCoefficientMap l E L ι X))) ⋙ b.tensor :=
  scalarTensorTransportOfSwap (tensorAdjointComparison l E X a) (tensorAdjointComparison l L X b)
    (pbcDerivedExtend (completedCoefficientMap l E L ι X))
    (Functor.isoWhiskerLeft (scalarIntegralClosed l E X).tensor e.symm ≪≫
      scalarClosedTensor l E L ι X ≪≫
      Functor.isoWhiskerRight (NatIso.prod e e) (scalarIntegralClosed l L X).tensor)

set_option maxHeartbeats 800000 in
-- The derived comparison calculation crosses the two explicit scalar implementations.
/-- On flat-term K-flat representatives the transported comparison is normalized
by the ordinary scalar tensor map and the fixed cochain counits.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-tower/
lem-coef-integral-finite-extension.proof.md, paragraph 5; Stacks Tags 06YY, 07A4, 08J9.

Proof: first identify the source adjoint comparison on a K-flat pair (P,Q) with
its canonical reversed representative after Koszul interchange. Test maps into
a K-injective complex and apply TensorPresentation.evaluation and
coefficientTensorCurry_normalize. The same argument applies over L to the
termwise scalar-extended pair. Base change preserves flat terms and K-flatness,
so these target representatives are allowed. The section equation ht identifies
the ordinary scalar extension units, hence identifies the ordinary scalar tensor
maps: check their values on s tensor (x tensor y), which generate after module
sheafification. Naturality of t and the signed interchange then give the same
equality on total tensor complexes. The two Koszul interchanges cancel, since
their signs multiply to one. The cochain equation he identifies the two derived
counits. Substitute these equations in scalarClosedTensorNormalization and use
naturality of the two representative isomorphisms to move the termwise map t
across them. The adjacent inverse comparison maps cancel, leaving exactly the
displayed representative square. This is a calculation on the stated complexes;
it does not identify global natural transformations or use scalarTensor itself.
Zero complexes, zero coefficient rings and the empty scheme require no exception.
(blueprint: new-sf-integral-hom-scalar-tensor-representatives). -/
theorem scalarTensorTransport_normalization
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (b : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l L X))
    (t : integralOrdinaryScalar l E L ι X ≅
      completedOrdinaryScalarExtension.{u, u} l E L ι X)
    (e : integralOrdinaryDerivedScalar l E L ι X ≅
      completedDerivedScalarExtension.{u, u} l E L ι X)
    (ht : ∀ (N : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l L X).obj.obj U)
      (x : N.val.obj U),
      (t.hom.app N).val.app U (integralOrdinaryTensorSection l E L ι X N U s x) =
        completedScalarTensorSection.{u, u} l E L ι X N U s x)
    (he : ∀ P : CochainComplex (integralTowerModules l E X) ℤ,
      e.hom.app (DerivedCategory.Q.obj P) ≫ completedScalarCounit.{u, u} l E L ι X P =
        (integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.hom.app P ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex t (.up ℤ)).hom.app P))
    (P Q : CochainComplex (integralTowerModules l E X) ℤ)
    (hp : proEtaleFlatRepresentatives X
      (completedIntegralCommRingSheafUnrestricted l E X) P)
    (hq : proEtaleFlatRepresentatives X
      (completedIntegralCommRingSheafUnrestricted l E X) Q) :
    ∃ (hp' : proEtaleFlatRepresentatives X
          (completedIntegralCommRingSheafUnrestricted l L X)
          (((pbcExtend (completedCoefficientMap l E L ι X)).mapHomologicalComplex
            (.up ℤ)).obj P))
      (hq' : proEtaleFlatRepresentatives X
          (completedIntegralCommRingSheafUnrestricted l L X)
          (((pbcExtend (completedCoefficientMap l E L ι X)).mapHomologicalComplex
            (.up ℤ)).obj Q)),
      (pbcDerivedExtend (completedCoefficientMap l E L ι X)).map
          ((tensorModel X a).representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
        (scalarTensorTransport l E L ι X a b e).hom.app
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        b.tensor.map (Prod.mkHom (pbcComplexCounit (completedCoefficientMap l E L ι X) P)
          (pbcComplexCounit (completedCoefficientMap l E L ι X) Q)) =
      pbcComplexCounit (completedCoefficientMap l E L ι X)
          (((IntegralHom.totalTensor.{u, u} X
            (completedIntegralCommRingSheafUnrestricted l E X)).obj P).obj Q) ≫
        DerivedCategory.Q.map
          (@inv _ _ _ _ (PurCompactSupport.scalarTensorTotal
              (completedCoefficientMap l E L ι X) P Q)
            (PurCompactSupport.scalarTensorTotal_isIso
              (completedCoefficientMap l E L ι X) P Q)) ≫
        (tensorModel X b).representative.hom.app (⟨_, hp'⟩, ⟨_, hq'⟩) := by
  let R := completedIntegralCommRingSheafUnrestricted l E X
  let S := completedIntegralCommRingSheafUnrestricted l L X
  let φ := completedCoefficientMap l E L ι X
  let F := integralOrdinaryDerivedScalar l E L ι X
  let G := pbcDerivedExtend φ
  let e' : F ≅ G := by
    with_unfolding_all exact e
  let SE := scalarIntegralClosed l E X
  let SL := scalarIntegralClosed l L X
  let TE := scalarIntegralModels l E X
  let TL := scalarIntegralModels l L X
  let F₀ := (integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)
  let G₀ := (pbcExtend φ).mapHomologicalComplex (.up ℤ)
  let FP := F₀.obj P
  let FQ := F₀.obj Q
  let GP := G₀.obj P
  let GQ := G₀.obj Q
  let V := (((IntegralHom.totalTensor.{u, u} X R).obj P).obj Q)
  let W := (((IntegralHom.totalTensor.{u, u} X R).obj Q).obj P)
  let U := (((IntegralHom.totalTensor.{u, u} X S).obj GP).obj GQ)
  let U' := (((IntegralHom.totalTensor.{u, u} X S).obj GQ).obj GP)
  let U_F := (((IntegralHom.totalTensor.{u, u} X S).obj FQ).obj FP)
  let τ := NatIso.mapHomologicalComplex t (.up ℤ)
  let δ := (integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.hom
  let c := pbcComplexCounit φ
  have hp' := PurCompactSupport.scalar_preservesFlatRepresentatives φ P hp
  have hq' := PurCompactSupport.scalar_preservesFlatRepresentatives φ Q hq
  refine ⟨hp', hq', ?_⟩
  have hP : integralOperationsGoodComplex l E X P := by
    with_unfolding_all exact hp
  have hQ : integralOperationsGoodComplex l E X Q := by
    with_unfolding_all exact hq
  have hFP := scalarGood l E L ι X ⟨P, hP⟩
  have hFQ := scalarGood l E L ι X ⟨Q, hQ⟩
  have hc (V : CochainComplex (integralTowerModules l E X) ℤ) :
      e'.hom.app (DerivedCategory.Q.obj V) ≫ c V =
        δ.app V ≫ DerivedCategory.Q.map (τ.hom.app V) := by
    exact completedScalarCounit_comparison l E L ι X t e he V
  have hpK : IntegralHom.flat.{u, u} X R P := hp.1
  have hqK : IntegralHom.flat.{u, u} X R Q := hq.1
  have hgpK : IntegralHom.flat.{u, u} X S GP := hp'.1
  have hgqK : IntegralHom.flat.{u, u} X S GQ := hq'.1
  have hfpK : IntegralHom.flat.{u, u} X S FP := hFP.1
  have hfqK : IntegralHom.flat.{u, u} X S FQ := hFQ.1
  have hrepE := tensorAdjointComparison_representative l E X a P Q hpK hqK
  have hrepL := tensorAdjointComparison_representative l L X b GP GQ hgpK hgqK
  have hn := (scalarClosedTensor_existsUnique l E L ι X).exists.choose_spec
    ⟨Q, hQ⟩ ⟨P, hP⟩
  have hnat := (CoefficientTensorModels.comparison.{u, u + 1, u, u + 2}
    (scalarIntegralModels l L X)).hom.naturality
    (X := (⟨FQ, hfqK⟩, ⟨FP, hfpK⟩))
    (Y := (⟨GQ, hgqK⟩, ⟨GP, hgpK⟩))
    (ObjectProperty.homMk (τ.hom.app Q), ObjectProperty.homMk (τ.hom.app P))
  have ho := scalarTensor_ordinary_transport l E L ι X t ht P Q
  have hd := δ.naturality
    (tensorComplexSwap X (completedIntegralCommRingSheafUnrestricted l E X) P Q).hom
  simp only [Functor.comp_map] at hd
  have ho' := map_three_comp_eq
    (A := CochainComplex (integralTowerModules l L X) ℤ)
    (B := IntegralHom.Derived.{u, u} X S) DerivedCategory.Q
    (F₀.map (tensorComplexSwap X R P Q).hom)
    ((scalarOrdinaryTensorChain l E L ι X).hom.app (Q, P))
    ((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X) S).map
      (Prod.mkHom (τ.hom.app Q) (τ.hom.app P)))
    (τ.hom.app V)
    (@inv _ _ _ _ (PurCompactSupport.scalarTensorTotal φ P Q)
      (PurCompactSupport.scalarTensorTotal_isIso φ P Q))
    (tensorComplexSwap X S GP GQ).hom ho
  exact scalarTensorTransportOfSwap_representative
    (A := IntegralHom.Derived.{u, u} X R) (B := IntegralHom.Derived.{u, u} X S)
    (tensorAdjointComparison l E X a) (tensorAdjointComparison l L X b)
    F G e' (scalarClosedTensor l E L ι X)
    (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
    (DerivedCategory.Q.obj FP) (DerivedCategory.Q.obj FQ)
    (DerivedCategory.Q.obj GP) (DerivedCategory.Q.obj GQ)
    (δ.app P) (δ.app Q)
    (DerivedCategory.Q.map (τ.hom.app P)) (DerivedCategory.Q.map (τ.hom.app Q))
    (c P) (c Q) (hc P) (hc Q)
    (V := DerivedCategory.Q.obj V) (W := DerivedCategory.Q.obj W)
    (H := DerivedCategory.Q.obj (F₀.obj V)) (K := DerivedCategory.Q.obj (F₀.obj W))
    (M := DerivedCategory.Q.obj U_F) (Z := DerivedCategory.Q.obj (G₀.obj V))
    (U := DerivedCategory.Q.obj U) (U' := DerivedCategory.Q.obj U')
    (ra := a.representative.hom.app (⟨P, hpK⟩, ⟨Q, hqK⟩))
    (s := DerivedCategory.Q.map (tensorComplexSwap X R P Q).hom)
    (m := (CoefficientTensorModels.iso.{u, u + 1, u, u + 2}
      (ProEt.topology X) R SE TE Q P hqK hpK).hom)
    (rb := b.representative.hom.app (⟨GP, hgpK⟩, ⟨GQ, hgqK⟩))
    (sb := DerivedCategory.Q.map (tensorComplexSwap X S GP GQ).hom)
    (mb := (CoefficientTensorModels.iso.{u, u + 1, u, u + 2}
      (ProEt.topology X) S SL TL GQ GP hgqK hgpK).hom)
    (δV := δ.app V) (δW := δ.app W)
    (fs := DerivedCategory.Q.map (F₀.map (tensorComplexSwap X R P Q).hom))
    (κ := DerivedCategory.Q.map ((scalarOrdinaryTensorChain l E L ι X).hom.app (Q, P)))
    (mF := (CoefficientTensorModels.iso.{u, u + 1, u, u + 2}
      (ProEt.topology X) S SL TL FQ FP hfqK hfpK).hom)
    (τ := DerivedCategory.Q.map
      ((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X) S).map
        (Prod.mkHom (τ.hom.app Q) (τ.hom.app P))))
    (t := DerivedCategory.Q.map (τ.hom.app V))
    (β := DerivedCategory.Q.map (@inv _ _ _ _ (PurCompactSupport.scalarTensorTotal φ P Q)
      (PurCompactSupport.scalarTensorTotal_isIso φ P Q)))
    (c := c V)
    (hrep := hrepE) (hrep' := hrepL) (hn := hn)
    (hnat := hnat.symm) (hδ := hd) (ho := ho') (hc := hc V)

end WeilConjectures.IntegralFiniteExtension
