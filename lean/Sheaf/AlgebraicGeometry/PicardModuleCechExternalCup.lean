/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import Sheaf.AlgebraicGeometry.PicardExternalRightCechModels
public import Sheaf.Paper.CechCupProductCore
public import Sheaf.Paper.ModuleCupResolutionData
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap
public import Sheaf.AlgebraicGeometry.ModuleCechComparison
import Sheaf.AlgebraicGeometry.PicardModuleCechExternalPairing

/-! # Module comparison of an external Cech cup cocycle

Source: Stacks Project, Tags 01FD, 07MB, 0FKV and 0BED.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules

/-- The ordinary module comparison sends the front/back external Cech cocycle to
an ordinary module cup of the projection-pulled-back classes. This concerns one
bidegree pairing, not a map from the tensor total complex, and uses no scalar Ext
cup or scalar cohomology operations.
Source: Stacks Project, Tags 01FD (refinement comparison), 07MB (front/back cup),
0FKV (cup comparison), and 0BED (equation-kunneth-on-cech).
(blueprint: lem-sc-picard-module-cech-external-cup).

Proof: W covers the product: each product point has projections in some U_i,V_j.
Use cechComparisonMapNaturality on W to obtain canonical comparisons for the
two projection-pulled-back modules. Each comparison is uniquely determined by
its alpha/beta equation, since moduleCechAlpha_isIso makes alpha invertible.
Use exists_unique_cechRefinementMap with the two index projections to refine
U,V along the projections to W. The unit and restriction formula of each refinement
identifies its cocycle coordinates with the corresponding factor in hl. Apply
the refinement comparison square of 01FD: the comparison of each refined factor
class is moduleCohomologyPullback of its original comparison. On W the ordinary
Cech cup has the front/back formula of 07MB. Compose restrictions from a front
or back intersection to the full intersection; presheaf functoriality and
naturality of the tensor-pullback adjunction unit identify these with hl.
Transport the two refined cycles through the additive homology identifications,
and use exists_unique_cechCupProduct on W. Leibniz supplies their cup cycle.
The additive Cech identifications identify the prescribed product cycle t with
this ordinary cup cycle, since their coordinates agree and cycle inclusion is
monic. The cup comparison square of 0FKV identifies its ordinary module
comparison with cup of the two refined comparison classes. Substitute the two
pullback comparison equalities. All three are genuine covers; the product is a
cover because each pair of factor cover members contains the corresponding
projections of a product point. No affine intersection hypothesis is required.
Zero coefficients give zero classes. Empty covering index sets force an empty
scheme. Degree zero is the tensor of the two pulled-back sections. -/
theorem picardModuleCech_externalCup
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) [F.IsQuasicoherent] (G : Y.Modules) [G.IsQuasicoherent]
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens)
    (hUc : iSup U = ⊤) (hVc : iSup V = ⊤) (p q : ℕ)
    (cF : ((cechComplexFunctor U).obj F.presheafModuleCat).homology p ⟶
      (RingedSpace.moduleCohomology X.toRingedSpace p).obj F)
    (hcF : IsModuleCechComparison U F p cF)
    (cG : ((cechComplexFunctor V).obj G.presheafModuleCat).homology q ⟶
      (RingedSpace.moduleCohomology Y.toRingedSpace q).obj G)
    (hcG : IsModuleCechComparison V G q cG)
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
            cup (D.left.class p a) (D.right.class q b) = D.target.class (p + q) c)
    (l : ((curriedTensor (ModuleCat.{w} k)).obj
      (((picardCechFunctor f U).obj F).X p)).obj
        (((picardCechFunctor g V).obj G).X q) ⟶
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj
            (externalCupCoefficients f g F G)).X (p + q))
    (hl :
      ∀ (a : ((picardCechFunctor f U).obj F).X p)
              (b : ((picardCechFunctor g V).obj G).X q) (y : Fin (p + q + 1) → ι × κ),
              TopCat.Presheaf.cechComplexFunctorXAddEquiv
                (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
                  pullback.snd f g ⁻¹ᵁ V ij.2)
                (scalarPresheaf (pullback.fst f g ≫ f) (externalCupCoefficients f g F G))
                (p + q) (l (a ⊗ₜ[k] b)) y =
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
    (a : ((picardCechFunctor f U).obj F).cycles p)
    (b : ((picardCechFunctor g V).obj G).cycles q)
    (t : ((picardCechFunctor (pullback.fst f g ≫ f)
      (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
        pullback.snd f g ⁻¹ᵁ V ij.2)).obj
          (externalCupCoefficients f g F G)).cycles (p + q))
    (ht : ((picardCechFunctor (pullback.fst f g ≫ f)
      (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
        pullback.snd f g ⁻¹ᵁ V ij.2)).obj
          (externalCupCoefficients f g F G)).iCycles (p + q) t =
      l ((((picardCechFunctor f U).obj F).iCycles p a) ⊗ₜ[k]
        (((picardCechFunctor g V).obj G).iCycles q b))) :
    cP ((TopCat.Presheaf.cechComplexFunctorHomologyIso _
      (externalCupCoefficients f g F G).presheafModuleCat (p + q)).inv
      ((TopCat.Presheaf.cechComplexFunctorHomologyIso _
        (scalarPresheaf (pullback.fst f g ≫ f) (externalCupCoefficients f g F G))
          (p + q)).hom
        (((picardCechFunctor (pullback.fst f g ≫ f)
          (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
            pullback.snd f g ⁻¹ᵁ V ij.2)).obj
              (externalCupCoefficients f g F G)).homologyπ (p + q) t))) =
      cup (moduleCohomologyPullback (pullback.fst f g) F p
        (cF ((TopCat.Presheaf.cechComplexFunctorHomologyIso U F.presheafModuleCat p).inv
          ((TopCat.Presheaf.cechComplexFunctorHomologyIso U (scalarPresheaf f F) p).hom
            (((picardCechFunctor f U).obj F).homologyπ p a)))))
        (moduleCohomologyPullback (pullback.snd f g) G q
          (cG ((TopCat.Presheaf.cechComplexFunctorHomologyIso V G.presheafModuleCat q).inv
            ((TopCat.Presheaf.cechComplexFunctorHomologyIso V (scalarPresheaf g G) q).hom
              (((picardCechFunctor g V).obj G).homologyπ q b))))) := by
  exact picardModuleCech_externalPairing f g F G U V hUc hVc p q l hl
    cF hcF cG hcG cP hcP cup hcup a b t ht

end AlgebraicGeometry.Scheme.Modules
