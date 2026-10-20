/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import WeilConjectures.AlgebraicGeometry.PicardExternalRightCechModels
public import Sheaf.Paper.CechCupProductCore
public import Sheaf.Paper.ModuleCupResolutionData
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import Sheaf.Paper.CechRefinementCochainMap

/-! # Ordinary module Cech representatives of the external pairing

Source: Stacks Project, Cohomology, Tags 01FD, 07MB and 0FKV;
Varieties, Tag 0BED, equation-kunneth-on-cech.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

private theorem map_pi {R : Type w} [Ring R]
    (S : ShortComplex (ModuleCat.{w} R)) [S.HasHomology] :
    (S.map (forget₂ _ AddCommGrpCat)).homologyπ ≫
      (S.mapHomologyIso (forget₂ _ AddCommGrpCat)).hom =
    (S.mapCyclesIso (forget₂ _ AddCommGrpCat)).hom ≫
      (forget₂ _ AddCommGrpCat).map S.homologyπ := by
  let F := forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}
  rw [S.homologyData.left.mapHomologyIso_eq F,
    S.homologyData.left.mapCyclesIso_eq F]
  simp only [Iso.trans_hom, Category.assoc]
  rw [← Category.assoc,
    (S.homologyData.left.map F).homologyπ_comp_homologyIso_hom]
  simp only [Functor.mapIso_hom, Iso.symm_hom, ShortComplex.LeftHomologyData.map_π,
    Category.assoc, ← F.map_comp,
    S.homologyData.left.π_comp_homologyIso_inv]
  simp only [F, Functor.map_comp]

section AdditiveTransport
variable {R T : Type w} [Ring R] [Ring T]
  (K : CochainComplex (ModuleCat.{w} R) ℕ) (L : CochainComplex (ModuleCat.{w} T) ℕ)
  (φ : ((forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}).mapHomologicalComplex _).obj K ⟶
    ((forget₂ (ModuleCat.{w} T) AddCommGrpCat.{w}).mapHomologicalComplex _).obj L)

private def transportCycle (n : ℕ) (a : K.cycles n) :
    (L.sc n).moduleCatLeftHomologyData.K :=
  (L.sc n).moduleCatCyclesIso.hom (((L.sc n).mapCyclesIso (forget₂ _ AddCommGrpCat)).hom
    (HomologicalComplex.cyclesMap φ n
      (((K.sc n).mapCyclesIso (forget₂ _ AddCommGrpCat)).inv a)))

private theorem transportCycle_val (n : ℕ) (a : K.cycles n) :
    (transportCycle K L φ n a).val = φ.f n (K.iCycles n a) := by
  let VK := forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}
  let VL := forget₂ (ModuleCat.{w} T) AddCommGrpCat.{w}
  have h : ((K.sc n).mapCyclesIso VK).inv ≫
      HomologicalComplex.cyclesMap φ n ≫ ((L.sc n).mapCyclesIso VL).hom ≫
      VL.map (L.sc n).moduleCatCyclesIso.hom ≫
      VL.map (L.sc n).moduleCatLeftHomologyData.i =
      VK.map (K.iCycles n) ≫ φ.f n := by
    rw [← VL.map_comp, ShortComplex.moduleCatCyclesIso_hom_i]
    rw [ShortComplex.mapCyclesIso_hom_iCycles]
    change ((K.sc n).mapCyclesIso VK).inv ≫
      HomologicalComplex.cyclesMap φ n ≫
      (((VL.mapHomologicalComplex (ComplexShape.up ℕ)).obj L).iCycles n) = _
    rw [HomologicalComplex.cyclesMap_i]
    change ((K.sc n).mapCyclesIso VK).inv ≫
      ((K.sc n).map VK).iCycles ≫ φ.f n = _
    rw [← ShortComplex.mapCyclesIso_hom_iCycles]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rfl
  exact ConcreteCategory.congr_hom h a

private theorem transportCycle_class (n : ℕ) (a : K.cycles n) :
    cupCycleClass L n (transportCycle K L φ n a) =
      ((L.sc n).mapHomologyIso (forget₂ _ AddCommGrpCat)).hom
        (HomologicalComplex.homologyMap φ n
          (((K.sc n).mapHomologyIso (forget₂ _ AddCommGrpCat)).inv (K.homologyπ n a))) := by
  let VK := forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}
  let VL := forget₂ (ModuleCat.{w} T) AddCommGrpCat.{w}
  have h : ((K.sc n).mapCyclesIso VK).inv ≫
      HomologicalComplex.cyclesMap φ n ≫ ((L.sc n).mapCyclesIso VL).hom ≫
      VL.map (L.sc n).moduleCatCyclesIso.hom ≫
      VL.map (L.sc n).moduleCatCyclesIso.inv ≫ VL.map (L.homologyπ n) =
      VK.map (K.homologyπ n) ≫ ((K.sc n).mapHomologyIso VK).inv ≫
        HomologicalComplex.homologyMap φ n ≫ ((L.sc n).mapHomologyIso VL).hom := by
    simp only [← VL.map_comp, Iso.hom_inv_id_assoc]
    erw [← map_pi (L.sc n)]
    change ((K.sc n).mapCyclesIso VK).inv ≫
      HomologicalComplex.cyclesMap φ n ≫
        ((VL.mapHomologicalComplex _).obj L).homologyπ n ≫ _ = _
    erw [← HomologicalComplex.homologyπ_naturality_assoc]
    have hs := map_pi (K.sc n)
    have hs' := congrArg (fun t ↦ ((K.sc n).mapCyclesIso VK).inv ≫ t ≫
      ((K.sc n).mapHomologyIso VK).inv) hs
    dsimp only [VK] at hs'
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id] at hs'
    have hs'' := congrArg (fun u ↦ u ≫ HomologicalComplex.homologyMap φ n ≫
      ((L.sc n).mapHomologyIso VL).hom) hs'
    simpa only [Category.assoc, HomologicalComplex.homologyπ,
      HomologicalComplex.homology, VK, VL, HomologicalComplex.sc,
      HomologicalComplex.shortComplexFunctor, HomologicalComplex.shortComplexFunctor',
      ShortComplex.map, Functor.mapHomologicalComplex] using hs'' 
  exact ConcreteCategory.congr_hom h a
end AdditiveTransport

private def scalarIso {k : Type w} [Field k] {X : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) {ι : Type w} (U : ι → X.Opens) (F : X.Modules) :=
  (TopCat.Presheaf.cechComplexFunctorIso U (scalarPresheaf f F)) ≪≫
    (TopCat.Presheaf.cechComplexFunctorIso U F.presheafModuleCat).symm

private def scalarCycle {k : Type w} [Field k] {X : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) {ι : Type w} (U : ι → X.Opens) (F : X.Modules)
    (n : ℕ) (a : ((picardCechFunctor f U).obj F).cycles n) :
    (((cechComplexFunctor U).obj F.presheafModuleCat).sc n).moduleCatLeftHomologyData.K :=
  transportCycle ((picardCechFunctor f U).obj F)
    ((cechComplexFunctor U).obj F.presheafModuleCat) (scalarIso f U F).hom n a

private theorem scalarCycle_cochain {k : Type w} [Field k] {X : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) {ι : Type w} (U : ι → X.Opens) (F : X.Modules)
    (n : ℕ) (a : ((picardCechFunctor f U).obj F).cycles n) :
    (scalarCycle f U F n a).val = (scalarIso f U F).hom.f n
      (((picardCechFunctor f U).obj F).iCycles n a) := by
  exact transportCycle_val ((picardCechFunctor f U).obj F)
    ((cechComplexFunctor U).obj F.presheafModuleCat) (scalarIso f U F).hom n a

private theorem scalarCycle_class {k : Type w} [Field k] {X : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) {ι : Type w} (U : ι → X.Opens) (F : X.Modules)
    (n : ℕ) (a : ((picardCechFunctor f U).obj F).cycles n) :
    cupCycleClass _ n (scalarCycle f U F n a) =
    (TopCat.Presheaf.cechComplexFunctorHomologyIso U F.presheafModuleCat n).inv
      ((TopCat.Presheaf.cechComplexFunctorHomologyIso U (scalarPresheaf f F) n).hom
        (((picardCechFunctor f U).obj F).homologyπ n a)) := by
  let S := (picardCechFunctor f U).obj F
  let M := (cechComplexFunctor U).obj F.presheafModuleCat
  let VS := forget₂ (ModuleCat.{w} k) AddCommGrpCat.{w}
  let VM := forget₂ (ModuleCat.{w} Γ(X, ⊤)) AddCommGrpCat.{w}
  let e := scalarIso f U F
  have h := transportCycle_class S M e.hom n a
  have he : ((S.sc n).mapHomologyIso VS).inv ≫
      HomologicalComplex.homologyMap e.hom n ≫ ((M.sc n).mapHomologyIso VM).hom =
      (TopCat.Presheaf.cechComplexFunctorHomologyIso U (scalarPresheaf f F) n).hom ≫
        (TopCat.Presheaf.cechComplexFunctorHomologyIso U F.presheafModuleCat n).inv := by
    simp only [e, scalarIso, Iso.trans_hom, Iso.symm_hom,
      HomologicalComplex.homologyMap_comp,
      TopCat.Presheaf.cechComplexFunctorHomologyIso, Iso.trans_inv, Iso.symm_inv,
      HomologicalComplex.homologyMapIso_hom, HomologicalComplex.homologyMapIso_inv,
      Category.assoc]
    rfl
  exact h.trans (ConcreteCategory.congr_hom he (S.homologyπ n a))

private theorem scalarCycle_val {k : Type w} [Field k] {X : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) {ι : Type w} (U : ι → X.Opens) (F : X.Modules)
    (n : ℕ) (a : ((picardCechFunctor f U).obj F).cycles n) :
    TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat n
      (scalarCycle f U F n a).val =
    TopCat.Presheaf.cechComplexFunctorXAddEquiv U (scalarPresheaf f F) n
      (((picardCechFunctor f U).obj F).iCycles n a) := by
  rw [scalarCycle_cochain]
  change TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat n
    ((TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat n).symm
      (TopCat.Presheaf.cechComplexFunctorXAddEquiv U (scalarPresheaf f F) n
        (((picardCechFunctor f U).obj F).iCycles n a))) = _
  exact AddEquiv.apply_symm_apply _ _

private theorem restriction_comp {X : Scheme.{w}}
    (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w}) {V W Z : X.Opensᵒᵖ}
    (i : V ⟶ W) (j : W ⟶ Z) (k : V ⟶ Z) (a : P.obj V) :
    P.map j (P.map i a) = P.map k a := by
  rw [← ConcreteCategory.comp_apply, ← P.map_comp]
  congr 2

set_option maxHeartbeats 800000 in
-- The three cycle transports and coordinate restrictions need additional elaboration.
/-- Scalar external cocycles admit ordinary module Cech representatives compatible
with the two specified refinements and the front/back cup cochain.
Source: Stacks Project, Tags 01FD, 07MB and 0BED, equation-kunneth-on-cech.
(blueprint: lem-sc-picard-external-cech-module-representatives).

Proof: Forget scalars in the three Cech complexes and identify each with the
explicit additive intersection complex by cechComplexFunctorIso. Scalar and
ordinary module sections have the same underlying additive presheaf, so the
composite identification carries scalar cycles to ordinary module cycles and
carries their homology classes through exactly the two homology isomorphisms
shown below. Apply gammaF and gammaG to the transported factor cycles; cochain
maps preserve cycles, and naturality of the homology projection gives the first
two equations. Transport t by the same identification. Evaluate its inclusion
on every product-cover tuple and use the assumed inclusion equality and hh.
The refinement formulas identify the front and back sections with pullback by
the adjunction units followed by restriction. Restriction composition identifies
their further restrictions with the two factors in n2CechCupCochain. The coordinate
equivalence is injective, giving the last equation; the homology transport gives
the third. This is a statement about Cech cycles only, independent of any
comparison with derived module cohomology or any covering hypothesis. In degree
zero both faces use the single vertex. Empty index sets and zero coefficients
have zero coordinate groups and the same construction and equations apply. -/
theorem picardExternalCech_moduleRepresentatives
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) [F.IsQuasicoherent] (G : Y.Modules) [G.IsQuasicoherent]
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens)
    (p q : ℕ)
    (h : ((curriedTensor (ModuleCat.{w} k)).obj
        (((picardCechFunctor f U).obj F).X p)).obj
          (((picardCechFunctor g V).obj G).X q) ⟶
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X (p + q))
    (hh :
      ∀ (a : ((picardCechFunctor f U).obj F).X p)
              (b : ((picardCechFunctor g V).obj G).X q) (y : Fin (p + q + 1) → ι × κ),
              TopCat.Presheaf.cechComplexFunctorXAddEquiv
                (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
                  pullback.snd f g ⁻¹ᵁ V ij.2)
                (scalarPresheaf (pullback.fst f g ≫ f) (externalCupCoefficients f g F G))
                (p + q) (h (a ⊗ₜ[k] b)) y =
                tmulSection
                  (((fun (Q : X.Opens) (W : (Limits.pullback f g).Opens)
                      (h : W ≤ pullback.fst f g ⁻¹ᵁ Q) (s : Γ(F, Q)) ↦
                    ((tensorPullback (pullback.fst f g)).obj F).presheaf.map (homOfLE h).op
                      (((Classical.choose (exists_tensorPullbackAdjunction
                        (pullback.fst f g))).unit.app F).val.app (op Q) s))
                    (⨅ l, U (y (n2CupFront p q l)).1) _
                    (by
                      intro x hx
                      change (pullback.fst f g).base x ∈ ⨅ l, U (y (n2CupFront p q l)).1
                      rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
                      intro l
                      exact (iInf_le (fun j ↦ pullback.fst f g ⁻¹ᵁ U (y j).1 ⊓
                        pullback.snd f g ⁻¹ᵁ V (y j).2) (n2CupFront p q l) hx).1)
                    (TopCat.Presheaf.cechComplexFunctorXAddEquiv U (scalarPresheaf f F) p a
                      (fun l ↦ (y (n2CupFront p q l)).1))))
                  (((fun (Q : Y.Opens) (W : (Limits.pullback f g).Opens)
                      (h : W ≤ pullback.snd f g ⁻¹ᵁ Q) (s : Γ(G, Q)) ↦
                    ((tensorPullback (pullback.snd f g)).obj G).presheaf.map (homOfLE h).op
                      (((Classical.choose (exists_tensorPullbackAdjunction
                        (pullback.snd f g))).unit.app G).val.app (op Q) s))
                    (⨅ l, V (y (n2CupBack p q l)).2) _
                    (by
                      intro x hx
                      change (pullback.snd f g).base x ∈ ⨅ l, V (y (n2CupBack p q l)).2
                      rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
                      intro l
                      exact (iInf_le (fun j ↦ pullback.fst f g ⁻¹ᵁ U (y j).1 ⊓
                        pullback.snd f g ⁻¹ᵁ V (y j).2) (n2CupBack p q l) hx).2)
                    (TopCat.Presheaf.cechComplexFunctorXAddEquiv V (scalarPresheaf g G) q b
                      (fun l ↦ (y (n2CupBack p q l)).2)))))
    (hrefineF : ∀ ij : ι × κ,
      (pullback.fst f g ⁻¹ᵁ U ij.1 ⊓ pullback.snd f g ⁻¹ᵁ V ij.2) ≤
        pullback.fst f g ⁻¹ᵁ U ij.1)
    (hrefineG : ∀ ij : ι × κ,
      (pullback.fst f g ⁻¹ᵁ U ij.1 ⊓ pullback.snd f g ⁻¹ᵁ V ij.2) ≤
        pullback.snd f g ⁻¹ᵁ V ij.2)
    (gammaF : ((forget₂ (ModuleCat.{w} Γ(X, ⊤)) AddCommGrpCat.{w}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj ((cechComplexFunctor U).obj F.presheafModuleCat) ⟶
      ((forget₂ (ModuleCat.{w} Γ(Limits.pullback f g, ⊤))
        AddCommGrpCat.{w}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((cechComplexFunctor (fun ij : ι × κ ↦
          pullback.fst f g ⁻¹ᵁ U ij.1 ⊓ pullback.snd f g ⁻¹ᵁ V ij.2)).obj
          ((tensorPullback (pullback.fst f g)).obj F).presheafModuleCat))
    (hgammaF : IsCechRefinementMap (pullback.fst f g) U
      (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
        pullback.snd f g ⁻¹ᵁ V ij.2) Prod.fst hrefineF F gammaF)
    (gammaG : ((forget₂ (ModuleCat.{w} Γ(Y, ⊤)) AddCommGrpCat.{w}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj ((cechComplexFunctor V).obj G.presheafModuleCat) ⟶
      ((forget₂ (ModuleCat.{w} Γ(Limits.pullback f g, ⊤))
        AddCommGrpCat.{w}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((cechComplexFunctor (fun ij : ι × κ ↦
          pullback.fst f g ⁻¹ᵁ U ij.1 ⊓ pullback.snd f g ⁻¹ᵁ V ij.2)).obj
          ((tensorPullback (pullback.snd f g)).obj G).presheafModuleCat))
    (hgammaG : IsCechRefinementMap (pullback.snd f g) V
      (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
        pullback.snd f g ⁻¹ᵁ V ij.2) Prod.snd hrefineG G gammaG) :
    let A := (picardCechFunctor f U).obj F
    let B := (picardCechFunctor g V).obj G
    let W := fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
      pullback.snd f g ⁻¹ᵁ V ij.2
    let E := externalCupCoefficients f g F G
    let P := (picardCechFunctor (pullback.fst f g ≫ f) W).obj E
    ∀ (a : A.cycles p) (b : B.cycles q) (t : P.cycles (p + q)),
      P.iCycles (p + q) t = h ((A.iCycles p a) ⊗ₜ[k] (B.iCycles q b)) →
      ∃ (a' : (((cechComplexFunctor W).obj
          ((tensorPullback (pullback.fst f g)).obj F).presheafModuleCat).sc
            p).moduleCatLeftHomologyData.K)
        (b' : (((cechComplexFunctor W).obj
          ((tensorPullback (pullback.snd f g)).obj G).presheafModuleCat).sc
            q).moduleCatLeftHomologyData.K)
        (t' : (((cechComplexFunctor W).obj E.presheafModuleCat).sc
          (p + q)).moduleCatLeftHomologyData.K),
        cupCycleClass _ p a' = cechRefinementHomology gammaF p
          ((TopCat.Presheaf.cechComplexFunctorHomologyIso U F.presheafModuleCat p).inv
            ((TopCat.Presheaf.cechComplexFunctorHomologyIso U
              (scalarPresheaf f F) p).hom (A.homologyπ p a))) ∧
        cupCycleClass _ q b' = cechRefinementHomology gammaG q
          ((TopCat.Presheaf.cechComplexFunctorHomologyIso V G.presheafModuleCat q).inv
            ((TopCat.Presheaf.cechComplexFunctorHomologyIso V
              (scalarPresheaf g G) q).hom (B.homologyπ q b))) ∧
        cupCycleClass _ (p + q) t' =
          (TopCat.Presheaf.cechComplexFunctorHomologyIso W E.presheafModuleCat
            (p + q)).inv
            ((TopCat.Presheaf.cechComplexFunctorHomologyIso W
              (scalarPresheaf (pullback.fst f g ≫ f) E) (p + q)).hom
                (P.homologyπ (p + q) t)) ∧
        t'.val = n2CechCupCochain W ((tensorPullback (pullback.fst f g)).obj F)
          ((tensorPullback (pullback.snd f g)).obj G) p q a'.val b'.val := by
  set_option backward.isDefEq.respectTransparency true in
    classical
    intro A B W E P a b t ht
    let KF := (cechComplexFunctor U).obj F.presheafModuleCat
    let KG := (cechComplexFunctor V).obj G.presheafModuleCat
    let LF := (cechComplexFunctor W).obj
      ((tensorPullback (pullback.fst f g)).obj F).presheafModuleCat
    let LG := (cechComplexFunctor W).obj
      ((tensorPullback (pullback.snd f g)).obj G).presheafModuleCat
    let sa := scalarCycle f U F p a
    let sb := scalarCycle g V G q b
    let a' := transportCycle KF LF gammaF p ((KF.sc p).moduleCatCyclesIso.inv sa)
    let b' := transportCycle KG LG gammaG q ((KG.sc q).moduleCatCyclesIso.inv sb)
    let t' := scalarCycle (pullback.fst f g ≫ f) W E (p + q) t
    have ha : a'.val = gammaF.f p sa.val := by
      have h := transportCycle_val KF LF gammaF p ((KF.sc p).moduleCatCyclesIso.inv sa)
      have hi := ConcreteCategory.congr_hom
        (ShortComplex.moduleCatCyclesIso_inv_iCycles (KF.sc p)) sa
      exact h.trans (congrArg (fun x ↦ gammaF.f p x) hi)
    have hb : b'.val = gammaG.f q sb.val := by
      have h := transportCycle_val KG LG gammaG q ((KG.sc q).moduleCatCyclesIso.inv sb)
      have hi := ConcreteCategory.congr_hom
        (ShortComplex.moduleCatCyclesIso_inv_iCycles (KG.sc q)) sb
      exact h.trans (congrArg (fun x ↦ gammaG.f q x) hi)
    refine ⟨a', b', t', ?_, ?_, scalarCycle_class _ W E (p + q) t, ?_⟩
    · have h := transportCycle_class KF LF gammaF p ((KF.sc p).moduleCatCyclesIso.inv sa)
      change cupCycleClass LF p a' = cechRefinementHomology gammaF p
        (cupCycleClass KF p sa) at h
      exact h.trans (congrArg (fun x ↦ cechRefinementHomology gammaF p x)
        (scalarCycle_class f U F p a))
    · have h := transportCycle_class KG LG gammaG q ((KG.sc q).moduleCatCyclesIso.inv sb)
      change cupCycleClass LG q b' = cechRefinementHomology gammaG q
        (cupCycleClass KG q sb) at h
      exact h.trans (congrArg (fun x ↦ cechRefinementHomology gammaG q x)
        (scalarCycle_class g V G q b))
    · apply (TopCat.Presheaf.cechComplexFunctorXAddEquiv W E.presheafModuleCat
        (p + q)).injective
      funext y
      have hc := congrFun (scalarCycle_val (pullback.fst f g ≫ f) W E (p + q) t) y
      refine hc.trans ?_
      rw [ht, hh]
      unfold n2CechCupCochain
      rw [AddEquiv.apply_symm_apply, ha, hb, hgammaF, hgammaG]
      conv_rhs => rw [scalarCycle_val f U F p a, scalarCycle_val g V G q b]
      congr 1
      · exact (restriction_comp ((tensorPullback (pullback.fst f g)).obj F).presheaf
          _ _ _ _).symm
      · exact (restriction_comp ((tensorPullback (pullback.snd f g)).obj G).presheaf
          _ _ _ _).symm

end
end AlgebraicGeometry.Scheme.Modules
