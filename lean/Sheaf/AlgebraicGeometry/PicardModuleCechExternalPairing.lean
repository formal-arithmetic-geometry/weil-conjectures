/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.AlgebraicGeometry.PicardExternalRightCechModels
public import Sheaf.Paper.CechCupProductCore
public import Sheaf.Paper.ModuleCupResolutionData
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap
public import Sheaf.AlgebraicGeometry.ModuleCechComparison
import Sheaf.AlgebraicGeometry.PicardExternalCechModuleRepresentatives
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import Sheaf.Paper.CechComparisonMapNaturality
import Sheaf.Paper.CechRefinementComparisonSquare
import Sheaf.Paper.CechCupResolutionComparisonExists
import Sheaf.Paper.CechCupSignedAxisPairing

/-! # Ordinary module comparison for external Cech pairing

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

attribute [local irreducible] tensorPullback tensorPullbackObj
  moduleCohomologyPullback moduleCohomologyFMap cechRefinementHomology
attribute [local instance 2000]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf

private theorem tensorPullback_qcoh {X Y : Scheme.{w}} (a : X ⟶ Y)
    (F : Y.Modules) [F.IsQuasicoherent] : ((tensorPullback a).obj F).IsQuasicoherent := by
  let e := (nonempty_tensorPullbackAdjunction a).some.leftAdjointUniq
    (pullbackPushforwardAdjunction a)
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (e.app F).symm (isQuasicoherent_pullback a F)

private theorem cupCycleClass_surjective {R : Type w} [Ring R]
    (K : CochainComplex (ModuleCat.{w} R) ℕ) (n : ℕ) :
    Function.Surjective (cupCycleClass K n) := by
  exact (ModuleCat.epi_iff_surjective
    ((K.sc n).moduleCatCyclesIso.inv ≫ (K.sc n).homologyπ)).mp inferInstance

private theorem cupResolutionClass_surjective {X : Scheme.{w}} {F : X.Modules}
    (D : CupAcyclicResolution F) (n : ℕ) : Function.Surjective (D.class n) := by
  let : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let := RingedSpace.globalSectionsFunctor_additive X.toRingedSpace
  let T := (RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
    (ComplexShape.up ℕ)
  have : IsIso (HomologicalComplex.homologyMap (T.map D.comparison) n) := D.computes n
  exact ((ModuleCat.epi_iff_surjective
    (D.I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) n).inv).mp
      inferInstance).comp
    (((ModuleCat.epi_iff_surjective
      (HomologicalComplex.homologyMap (T.map D.comparison) n)).mp inferInstance).comp
        (cupCycleClass_surjective (T.obj D.K) n))

private theorem cupPair_exists_cycle {X : Scheme.{w}} {F G : X.Modules}
    (D : CupResolutionPairing F G) (p q : ℕ)
    (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
    (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K) :
    ∃ c : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.target.K).sc (p + q)).moduleCatLeftHomologyData.K,
      c.val = D.pair p q ⊤ a.val b.val := by
  have ha := a.property
  have hb := b.property
  change (D.left.K.d p ((ComplexShape.up ℕ).next p)).val.app (op ⊤) a.val = 0 at ha
  change (D.right.K.d q ((ComplexShape.up ℕ).next q)).val.app (op ⊤) b.val = 0 at hb
  rw [ComplexShape.next_eq' (ComplexShape.up ℕ) (by simp :
    (ComplexShape.up ℕ).Rel p (p + 1))] at ha
  rw [ComplexShape.next_eq' (ComplexShape.up ℕ) (by simp :
    (ComplexShape.up ℕ).Rel q (q + 1))] at hb
  refine ⟨⟨D.pair p q ⊤ a.val b.val, ?_⟩, rfl⟩
  change (D.target.K.d (p + q) ((ComplexShape.up ℕ).next (p + q))).val.app (op ⊤)
    (D.pair p q ⊤ a.val b.val) = 0
  rw [ComplexShape.next_eq' (ComplexShape.up ℕ) (by simp :
    (ComplexShape.up ℕ).Rel (p + q) (p + q + 1))]
  rw [D.leibniz, ha, hb]
  simp


set_option maxHeartbeats 800000 in
-- The signed-axis comparison transports three homology classes.
/-- Compare the class of an ordinary Cech cup cocycle with any module cup. -/
private theorem cechCup_comparison_cycles (X : Scheme.{w}) {ι : Type w}
    (U : ι → X.Opens) (hU : iSup U = ⊤)
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] (p q : ℕ)
    (cF : ((cechComplexFunctor U).obj F.presheafModuleCat).homology p ⟶
      (RingedSpace.moduleCohomology X.toRingedSpace p).obj F)
    (hcF : IsModuleCechComparison U F p cF)
    (cG : ((cechComplexFunctor U).obj G.presheafModuleCat).homology q ⟶
      (RingedSpace.moduleCohomology X.toRingedSpace q).obj G)
    (hcG : IsModuleCechComparison U G q cG)
    (cFG : ((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).homology (p + q) ⟶
      (RingedSpace.moduleCohomology X.toRingedSpace (p + q)).obj (@id X.Modules (F ⊗ G)))
    (hcFG : IsModuleCechComparison U (F ⊗ G) (p + q) cFG)
    (a : (((cechComplexFunctor U).obj F.presheafModuleCat).sc p).moduleCatLeftHomologyData.K)
    (b : (((cechComplexFunctor U).obj G.presheafModuleCat).sc q).moduleCatLeftHomologyData.K)
    (c : (((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).sc
      (p + q)).moduleCatLeftHomologyData.K)
    (hc : c.val = n2CechCupCochain U F G p q a.val b.val)
    (cup : (RingedSpace.moduleCohomology X.toRingedSpace p).obj F →ₗ[Γ(X, ⊤)]
      (RingedSpace.moduleCohomology X.toRingedSpace q).obj G →ₗ[Γ(X, ⊤)]
      (RingedSpace.moduleCohomology X.toRingedSpace (p + q)).obj (@id X.Modules (F ⊗ G)))
    (hcup :
      ∀ (D : CupResolutionPairing F G)
          (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
          (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K)
          (c : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj D.target.K).sc (p + q)).moduleCatLeftHomologyData.K),
          c.val = D.pair p q ⊤ a.val b.val →
            cup (D.left.class p a) (D.right.class q b) = D.target.class (p + q) c) :
    cFG (cupCycleClass _ (p + q) c) =
      cup (cF (cupCycleClass _ p a)) (cG (cupCycleClass _ q b)) := by
  classical
  obtain ⟨D, ⟨LC⟩, ⟨RC⟩, ⟨TC⟩⟩ := exists_cupCechResolutionComparison X U hU F G
  obtain ⟨a', ha⟩ := cupResolutionClass_surjective D.left p (cF (cupCycleClass _ p a))
  obtain ⟨b', hb⟩ := cupResolutionClass_surjective D.right q (cG (cupCycleClass _ q b))
  obtain ⟨c', hpair⟩ := cupPair_exists_cycle D p q a' b'
  obtain ⟨pair, halpha, hbeta⟩ := cupCech_signed_axis_pairing U D
    LC.alpha LC.beta LC.alpha_f LC.beta_f
    RC.alpha RC.beta RC.alpha_f RC.beta_f
    TC.alpha TC.beta TC.alpha_f TC.beta_f p q
  apply (ModuleCat.mono_iff_injective (TC.iso (p + q)).hom).mp inferInstance
  calc
    _ = HomologicalComplex.homologyMap TC.beta (p + q)
        (cupCycleClass _ (p + q) c) := TC.beta_class (p + q) cFG hcFG c
    _ = pair (HomologicalComplex.homologyMap LC.beta p (cupCycleClass _ p a))
        (HomologicalComplex.homologyMap RC.beta q (cupCycleClass _ q b)) :=
      (hbeta a b c hc).symm
    _ = pair (HomologicalComplex.homologyMap LC.alpha p (cupCycleClass _ p a'))
        (HomologicalComplex.homologyMap RC.alpha q (cupCycleClass _ q b')) := by
      rw [← LC.beta_class p cF hcF a, ← RC.beta_class q cG hcG b,
        ← LC.alpha_class p a', ← RC.alpha_class q b', ha, hb]
    _ = HomologicalComplex.homologyMap TC.alpha (p + q)
        (cupCycleClass _ (p + q) c') := halpha a' b' c' hpair
    _ = _ := by
      rw [← TC.alpha_class (p + q) c', ← hcup D a' b' c' hpair, ha, hb]

set_option maxHeartbeats 800000 in
-- Three Cech homology transports require additional elaboration steps.
/-- A prescribed external front/back cochain pairing compares to the module cup.
This assertion concerns ordinary module cohomology, with no scalar Ext cup.
Source: Stacks Project, Cohomology, Tags 01FD, 07MB and 0FKV;
Varieties, Tag 0BED, equation-kunneth-on-cech.
(blueprint: lem-sc-picard-module-cech-external-pairing).

Proof: On the product scheme use the cover W indexed by pairs, and refine the
projection inverse images of U and V to W using the two index projections.
The refinement maps exist by the restriction and tensor-pullback unit formulas;
W covers because inverse image preserves unions and intersections distribute over
unions. Transport the factor cocycles through the explicit additive Cech complex
identifications. Their refinements are cocycles. The prescribed bidegree formula
for h says, tuple by tuple, that the inclusion of t is their front/back Cech cup.
The additive identifications preserve restrictions and sections, so this remains
true for the ordinary module Cech complexes. Monicity of the cycle inclusion
identifies the cycles. Apply Tag 01FD comparison naturality for each projection,
then Tag 0FKV compatibility of the ordinary Cech and module cups on W. The three
canonical comparisons are exactly cX, cY and cP. The two identities give the
claimed module cup of module pullback classes. Comparisons need not be invertible
and the covers need not be affine. In degree zero this is the section tensor
formula. For zero coefficients or an empty cover of the empty scheme all cycles
and classes vanish. -/
theorem picardModuleCech_externalPairing
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) [F.IsQuasicoherent] (G : Y.Modules) [G.IsQuasicoherent]
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens)
    (hUc : iSup U = ⊤) (hVc : iSup V = ⊤) (p q : ℕ)
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
    (cX : ((cechComplexFunctor U).obj F.presheafModuleCat).homology p ⟶
      (RingedSpace.moduleCohomology X.toRingedSpace p).obj F)
    (hcX : IsModuleCechComparison U F p cX)
    (cY : ((cechComplexFunctor V).obj G.presheafModuleCat).homology q ⟶
      (RingedSpace.moduleCohomology Y.toRingedSpace q).obj G)
    (hcY : IsModuleCechComparison V G q cY)
    (cP : ((cechComplexFunctor
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj
            (externalCupCoefficients f g F G).presheafModuleCat).homology (p + q) ⟶
      (RingedSpace.moduleCohomology (Limits.pullback f g).toRingedSpace (p + q)).obj
        (externalCupCoefficients f g F G))
    (hcP : IsModuleCechComparison
      (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
        pullback.snd f g ⁻¹ᵁ V ij.2) (externalCupCoefficients f g F G) (p + q) cP)
    (cup : (RingedSpace.moduleCohomology (Limits.pullback f g).toRingedSpace p).obj
        ((tensorPullback (pullback.fst f g)).obj F) →ₗ[Γ(Limits.pullback f g, ⊤)]
      (RingedSpace.moduleCohomology (Limits.pullback f g).toRingedSpace q).obj
        ((tensorPullback (pullback.snd f g)).obj G) →ₗ[Γ(Limits.pullback f g, ⊤)]
      (RingedSpace.moduleCohomology (Limits.pullback f g).toRingedSpace (p + q)).obj
        (externalCupCoefficients f g F G))
    (hcup :
      ∀ (D : CupResolutionPairing
                ((tensorPullback (pullback.fst f g)).obj F)
                ((tensorPullback (pullback.snd f g)).obj G))
          (a : ((((RingedSpace.globalSectionsFunctor
          (Limits.pullback f g).toRingedSpace).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
          (b : ((((RingedSpace.globalSectionsFunctor
          (Limits.pullback f g).toRingedSpace).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K)
          (c : ((((RingedSpace.globalSectionsFunctor
          (Limits.pullback f g).toRingedSpace).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj D.target.K).sc (p + q)).moduleCatLeftHomologyData.K),
          c.val = D.pair p q ⊤ a.val b.val →
            cup (D.left.class p a) (D.right.class q b) = D.target.class (p + q) c) :
    let A := (picardCechFunctor f U).obj F
    let B := (picardCechFunctor g V).obj G
    let W := fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
      pullback.snd f g ⁻¹ᵁ V ij.2
    let E := externalCupCoefficients f g F G
    let P := (picardCechFunctor (pullback.fst f g ≫ f) W).obj E
    ∀ (a : A.cycles p) (b : B.cycles q) (t : P.cycles (p + q)),
      P.iCycles (p + q) t = h ((A.iCycles p a) ⊗ₜ[k] (B.iCycles q b)) →
      cP ((TopCat.Presheaf.cechComplexFunctorHomologyIso W E.presheafModuleCat
          (p + q)).inv
        ((TopCat.Presheaf.cechComplexFunctorHomologyIso W
          (scalarPresheaf (pullback.fst f g ≫ f) E) (p + q)).hom
            (P.homologyπ (p + q) t))) =
      cup (moduleCohomologyPullback (pullback.fst f g) F p
        (cX ((TopCat.Presheaf.cechComplexFunctorHomologyIso U F.presheafModuleCat p).inv
          ((TopCat.Presheaf.cechComplexFunctorHomologyIso U
            (scalarPresheaf f F) p).hom (A.homologyπ p a)))))
        (moduleCohomologyPullback (pullback.snd f g) G q
          (cY ((TopCat.Presheaf.cechComplexFunctorHomologyIso V G.presheafModuleCat q).inv
            ((TopCat.Presheaf.cechComplexFunctorHomologyIso V
              (scalarPresheaf g G) q).hom (B.homologyπ q b))))) := by
  set_option backward.isDefEq.respectTransparency true in
    classical
    intro A B W₀ E P a b t ht
    let W : ι × κ → (Limits.pullback f g).Opens :=
      fun ij ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓ pullback.snd f g ⁻¹ᵁ V ij.2
    let x := (TopCat.Presheaf.cechComplexFunctorHomologyIso U F.presheafModuleCat p).inv
      ((TopCat.Presheaf.cechComplexFunctorHomologyIso U
        (scalarPresheaf f F) p).hom (((picardCechFunctor f U).obj F).homologyπ p a))
    let y := (TopCat.Presheaf.cechComplexFunctorHomologyIso V G.presheafModuleCat q).inv
      ((TopCat.Presheaf.cechComplexFunctorHomologyIso V
        (scalarPresheaf g G) q).hom (((picardCechFunctor g V).obj G).homologyπ q b))
    let z := (TopCat.Presheaf.cechComplexFunctorHomologyIso W
      (externalCupCoefficients f g F G).presheafModuleCat (p + q)).inv
      ((TopCat.Presheaf.cechComplexFunctorHomologyIso W
        (scalarPresheaf (pullback.fst f g ≫ f) (externalCupCoefficients f g F G))
        (p + q)).hom
        (((picardCechFunctor (pullback.fst f g ≫ f) W).obj
          (externalCupCoefficients f g F G)).homologyπ (p + q) t))
    change cP z = cup (moduleCohomologyPullback (pullback.fst f g) F p (cX x))
      (moduleCohomologyPullback (pullback.snd f g) G q (cY y))
    have hW : iSup W = ⊤ := by
      apply top_unique
      intro x hx
      have hxU : (pullback.fst f g).base x ∈ iSup U := by rw [hUc]; trivial
      have hxV : (pullback.snd f g).base x ∈ iSup V := by rw [hVc]; trivial
      obtain ⟨i, hi⟩ := (TopologicalSpace.Opens.mem_iSup).mp hxU
      obtain ⟨j, hj⟩ := (TopologicalSpace.Opens.mem_iSup).mp hxV
      exact (TopologicalSpace.Opens.mem_iSup).mpr ⟨(i, j), hi, hj⟩
    have hrefineF : ∀ ij : ι × κ, W ij ≤ pullback.fst f g ⁻¹ᵁ U ij.1 :=
      fun _ ↦ inf_le_left
    have hrefineG : ∀ ij : ι × κ, W ij ≤ pullback.snd f g ⁻¹ᵁ V ij.2 :=
      fun _ ↦ inf_le_right
    obtain ⟨gammaF, hgammaF, _⟩ := exists_unique_cechRefinementMap
      (pullback.fst f g) U W Prod.fst hrefineF F
    obtain ⟨gammaG, hgammaG, _⟩ := exists_unique_cechRefinementMap
      (pullback.snd f g) V W Prod.snd hrefineG G
    obtain ⟨a', b', t', ha, hb, ht', hpair⟩ :=
      picardExternalCech_moduleRepresentatives f g F G U V p q h hh
        hrefineF hrefineG gammaF hgammaF gammaG hgammaG a b t ht
    have hF : ((tensorPullback (pullback.fst f g)).obj F).IsQuasicoherent :=
      tensorPullback_qcoh (pullback.fst f g) F
    have hG : ((tensorPullback (pullback.snd f g)).obj G).IsQuasicoherent :=
      tensorPullback_qcoh (pullback.snd f g) G
    obtain ⟨cF, hcF⟩ := ((cechComparisonMapNaturality (Limits.pullback f g) W hW).2 p).1
      ((tensorPullback (pullback.fst f g)).obj F)
    obtain ⟨cG, hcG⟩ := ((cechComparisonMapNaturality (Limits.pullback f g) W hW).2 q).1
      ((tensorPullback (pullback.snd f g)).obj G)
    have hproducts := cechCup_comparison_cycles (Limits.pullback f g) W hW
      ((tensorPullback (pullback.fst f g)).obj F)
      ((tensorPullback (pullback.snd f g)).obj G) p q
      cF hcF cG hcG cP hcP a' b' t' hpair cup hcup
    have hleft := cechRefinement_comparison_square X (Limits.pullback f g)
      (pullback.fst f g) U hUc W hW Prod.fst hrefineF F p
        cX hcX cF hcF gammaF hgammaF
    have hright := cechRefinement_comparison_square Y (Limits.pullback f g)
      (pullback.snd f g) V hVc W hW Prod.snd hrefineG G q
        cY hcY cG hcG gammaG hgammaG
    change cupCycleClass _ p a' = cechRefinementHomology gammaF p x at ha
    change cupCycleClass _ q b' = cechRefinementHomology gammaG q y at hb
    calc
      _ = cP (cupCycleClass _ (p + q) t') := by
        exact congrArg (fun x ↦ cP x) ht'.symm
      _ = cup (cF (cupCycleClass _ p a')) (cG (cupCycleClass _ q b')) := by
        exact hproducts
      _ = cup (cF (cechRefinementHomology gammaF p x))
          (cG (cechRefinementHomology gammaG q y)) :=
        congrArg₂ (fun x y ↦ cup (cF x) (cG y)) ha hb
      _ = _ := congrArg₂ (fun x y ↦ cup x y)
        (ConcreteCategory.congr_hom hleft x) (ConcreteCategory.congr_hom hright y)

end AlgebraicGeometry.Scheme.Modules
