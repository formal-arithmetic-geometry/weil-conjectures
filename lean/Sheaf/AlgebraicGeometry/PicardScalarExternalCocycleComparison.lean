/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Sheaf.AlgebraicGeometry.PicardScalarCechComparison
public import Sheaf.Paper.CechCupProduct

/-! # Comparison of a scalar external cup cocycle

Source: Stacks Project, Tags 01FD, 07MB, 0FKV and 0BED.
-/

@[expose] public section
set_option autoImplicit false
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules

/-- A product-cover cocycle with the external front/back coordinates represents the
scalar external cup of the compared factor classes.
Source: Stacks Project, Tags 01FD, 07MB, 0FKV; Varieties Tag 0BED,
equation-kunneth-on-cech.
(blueprint: lem-sc-picard-scalar-external-cocycle-comparison).

Proof: use the module-comparison witnesses of the three scalar comparisons and
forget scalars through the explicit additive Cech identifications. Refine each
projection-pulled-back cover to the product cover by its index projection. The
hypothesis identifies the target cocycle with the front/back cup of the refined
factor cocycles. The Tag 01FD comparison squares identify their classes with the
pullbacks of the compared factor classes. The Tag 0FKV Cech-to-resolution diagram
identifies the class of their cup with the module cohomology cup. Finally apply the existing
scalarExternalCup_moduleComparison to this module cup and the two compared factor
classes. Its pullback classes are precisely those given by the refinement squares,
so its equality identifies the computed target class with externalCup.
The factor cover equalities imply that the product intersections cover the fibre
product. The resolution augmentation is therefore a quasi-isomorphism, so these
comparison equations uniquely determine all three comparison maps. No affine
intersection hypothesis or invertibility of the Cech comparison itself is used.
Degree zero is the section pairing; zero coefficients or empty index types give zero cocycles. -/
theorem picardScalar_externalCocycle_comparison
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) [F.IsQuasicoherent] (G : Y.Modules) [G.IsQuasicoherent]
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens)
    (hUc : iSup U = ⊤) (hVc : iSup V = ⊤) (p q : ℕ)
    (eX : ((picardCechFunctor f U).obj F).homology p →ₗ[k] scalarCohomology f F p)
    (heX : IsPicardScalarCechComparison f U F p eX)
    (eY : ((picardCechFunctor g V).obj G).homology q →ₗ[k] scalarCohomology g G q)
    (heY : IsPicardScalarCechComparison g V G q eY)
    (eP : ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj
            (externalCupCoefficients f g F G)).homology (p + q) →ₗ[k]
        scalarCohomology (pullback.fst f g ≫ f) (externalCupCoefficients f g F G) (p + q))
    (heP : IsPicardScalarCechComparison (pullback.fst f g ≫ f)
      (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
        pullback.snd f g ⁻¹ᵁ V ij.2) (externalCupCoefficients f g F G) (p + q) eP) :
    let A := (picardCechFunctor f U).obj F
    let B := (picardCechFunctor g V).obj G
    let P := (picardCechFunctor (pullback.fst f g ≫ f)
      (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
        pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)
    ∀ (a : A.cycles p) (b : B.cycles q) (z : P.cycles (p + q)),
      (∀ y : Fin (p + q + 1) → ι × κ,
        TopCat.Presheaf.cechComplexFunctorXAddEquiv
          (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
            pullback.snd f g ⁻¹ᵁ V ij.2)
          (scalarPresheaf (pullback.fst f g ≫ f) (externalCupCoefficients f g F G))
          (p + q) (P.iCycles (p + q) z) y =
          tmulSection
            (((fun (Q : X.Opens) (W : (Limits.pullback f g).Opens)
                (h : W ≤ pullback.fst f g ⁻¹ᵁ Q) (s : Γ(F, Q)) ↦
              ((tensorPullback (pullback.fst f g)).obj F).presheaf.map (homOfLE h).op
                (((Classical.choose (exists_tensorPullbackAdjunction
                  (pullback.fst f g))).unit.app F).val.app (op Q) s))
              (⨅ l, U (y (cupFront p q l)).1) _
              (by
                intro x hx
                change (pullback.fst f g).base x ∈ ⨅ l, U (y (cupFront p q l)).1
                rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
                intro l
                exact (iInf_le (fun j ↦ pullback.fst f g ⁻¹ᵁ U (y j).1 ⊓
                  pullback.snd f g ⁻¹ᵁ V (y j).2) (cupFront p q l) hx).1)
              (TopCat.Presheaf.cechComplexFunctorXAddEquiv U (scalarPresheaf f F) p (A.iCycles p a)
                (fun l ↦ (y (cupFront p q l)).1))))
            (((fun (Q : Y.Opens) (W : (Limits.pullback f g).Opens)
                (h : W ≤ pullback.snd f g ⁻¹ᵁ Q) (s : Γ(G, Q)) ↦
              ((tensorPullback (pullback.snd f g)).obj G).presheaf.map (homOfLE h).op
                (((Classical.choose (exists_tensorPullbackAdjunction
                  (pullback.snd f g))).unit.app G).val.app (op Q) s))
              (⨅ l, V (y (cupBack p q l)).2) _
              (by
                intro x hx
                change (pullback.snd f g).base x ∈ ⨅ l, V (y (cupBack p q l)).2
                rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
                intro l
                exact (iInf_le (fun j ↦ pullback.fst f g ⁻¹ᵁ U (y j).1 ⊓
                  pullback.snd f g ⁻¹ᵁ V (y j).2) (cupBack p q l) hx).2)
              (TopCat.Presheaf.cechComplexFunctorXAddEquiv V (scalarPresheaf g G) q (B.iCycles q b)
                (fun l ↦ (y (cupBack p q l)).2))))) →
      eP (P.homologyπ (p + q) z) =
        externalCup f g F G p q (eX (A.homologyπ p a)) (eY (B.homologyπ q b)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
