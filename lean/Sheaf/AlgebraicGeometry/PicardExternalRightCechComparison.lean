/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M4
-/
module

public import WeilConjectures.AlgebraicGeometry.PicardExternalRightCechModels
public import WeilConjectures.AlgebraicGeometry.PicardExternalCupCochain
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

import Sheaf.AlgebraicGeometry.PicardRightCechCupHomology

/-! # Cup comparison for fixed right-coefficient Cech models

Source: Stacks Project, Varieties, Tag 0BED, equation-kunneth-on-cech.
(blueprint: lem-sc-picard-external-right-cech-comparison).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- Refinement and Cech cup give a morphism between the two fixed Cech sequences,
with scalar-model homology comparisons. This statement asserts no exactness.
Source: Stacks Project, Varieties, Tag 0BED, equation-kunneth-on-cech and the
following diagram; Cohomology, Tags 01FD, 07MB, 0FKV.
(blueprint: lem-sc-picard-external-right-cech-comparison).

Proof: Refine the pulled-back covers U and V to their product cover. The signed
Cech cup maps from the tensor total to the product Cech complex commute with
coefficient morphisms, so their three components give psi. Finite intersections
are affine, and external coefficients are quasi-coherent by pullback and tensor
quasi-coherence. The affine Cech comparison, followed by restriction of scalars
and the fixed resolution comparison, gives b1,b2,b3. For a1,a2,a3 apply tensor
Kunneth to the factor Cech complexes and to the fixed scalar models, composing
with the affine factor comparisons. Extend the natural complexes by zero; the
extension homology isomorphisms preserve these identifications in natural degrees.
Choose d1,d2,d3 by picardExternalCupCochain_exists. On tensor cycles the Cech
refinement and cup compatibility says that the transported psi component is
pullback followed by sheaf cup, precisely the normalization of d. Factor homology
projections are surjective; pure tensors span each tensor product and these span
the Kunneth direct sum. Thus the two linear maps coincide on all homology classes,
giving the displayed conjugation equations. Neither exactness nor invertibility
of the cup maps is used. Degree zero, zero sheaves and empty covering families
are included by the same coordinate formulas. -/
theorem picardExternal_right_cech_comparison
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [IsAffineHom (pullback.diagonal f)] [IsAffineHom (pullback.diagonal g)]
    (F : X.Modules) [F.IsQuasicoherent]
    (S : ShortComplex Y.Modules)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    {ι κ : Type w} [Finite ι] [Finite κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (hUc : iSup U = ⊤) (hVc : iSup V = ⊤)
    :
    ∃ (d1 : picardExternalTotal f g F S.X₁ ⟶
      picardScalarModel (pullback.fst f g ≫ f)
        (externalCupCoefficients f g F S.X₁)),
    ∃ (d2 : picardExternalTotal f g F S.X₂ ⟶
      picardScalarModel (pullback.fst f g ≫ f)
        (externalCupCoefficients f g F S.X₂)),
    ∃ (d3 : picardExternalTotal f g F S.X₃ ⟶
      picardScalarModel (pullback.fst f g ≫ f)
        (externalCupCoefficients f g F S.X₃)),
    let T := S.map (picardRightTensorCechFunctor f g U V F)
    let P := S.map (picardRightProductCechFunctor f g U V F)
    ∃ (ψ : T ⟶ P)
      (a1 : ∀ n : ℕ, T.X₁.homology (n : ℤ) ≅
        (picardExternalTotal f g F S.X₁).homology (n : ℤ))
      (b1 : ∀ n : ℕ, P.X₁.homology (n : ℤ) ≅
        (picardScalarModel (pullback.fst f g ≫ f)
          (externalCupCoefficients f g F S.X₁)).homology (n : ℤ))
      (a2 : ∀ n : ℕ, T.X₂.homology (n : ℤ) ≅
        (picardExternalTotal f g F S.X₂).homology (n : ℤ))
      (b2 : ∀ n : ℕ, P.X₂.homology (n : ℤ) ≅
        (picardScalarModel (pullback.fst f g ≫ f)
          (externalCupCoefficients f g F S.X₂)).homology (n : ℤ))
      (a3 : ∀ n : ℕ, T.X₃.homology (n : ℤ) ≅
        (picardExternalTotal f g F S.X₃).homology (n : ℤ))
      (b3 : ∀ n : ℕ, P.X₃.homology (n : ℤ) ≅
        (picardScalarModel (pullback.fst f g ≫ f)
          (externalCupCoefficients f g F S.X₃)).homology (n : ℤ)),
      IsPicardExternalCupCochain f g F S.X₁ d1 ∧
      IsPicardExternalCupCochain f g F S.X₂ d2 ∧
      IsPicardExternalCupCochain f g F S.X₃ d3 ∧
      (∀ n : ℕ, HomologicalComplex.homologyMap ψ.τ₁ (n : ℤ) =
        (a1 n).hom ≫ HomologicalComplex.homologyMap d1 (n : ℤ) ≫ (b1 n).inv) ∧
      (∀ n : ℕ, HomologicalComplex.homologyMap ψ.τ₂ (n : ℤ) =
        (a2 n).hom ≫ HomologicalComplex.homologyMap d2 (n : ℤ) ≫ (b2 n).inv) ∧
      (∀ n : ℕ, HomologicalComplex.homologyMap ψ.τ₃ (n : ℤ) =
        (a3 n).hom ≫ HomologicalComplex.homologyMap d3 (n : ℤ) ≫ (b3 n).inv) := by
  classical
  obtain ⟨d1, hd1⟩ := picardExternalCupCochain_exists f g F S.X₁
  obtain ⟨d2, hd2⟩ := picardExternalCupCochain_exists f g F S.X₂
  obtain ⟨d3, hd3⟩ := picardExternalCupCochain_exists f g F S.X₃
  obtain ⟨θ, hθ⟩ := picardRightCechCup_exists f g U V F
  have component (G : Y.Modules) [G.IsQuasicoherent]
      (d : picardExternalTotal f g F G ⟶
        picardScalarModel (pullback.fst f g ≫ f) (externalCupCoefficients f g F G))
      (hd : IsPicardExternalCupCochain f g F G d) :
      ∃ (a : ∀ n : ℕ,
          ((picardRightTensorCechFunctor f g U V F).obj G).homology (n : ℤ) ≅
            (picardExternalTotal f g F G).homology (n : ℤ))
        (b : ∀ n : ℕ,
          ((picardRightProductCechFunctor f g U V F).obj G).homology (n : ℤ) ≅
            (picardScalarModel (pullback.fst f g ≫ f)
              (externalCupCoefficients f g F G)).homology (n : ℤ)),
        ∀ n : ℕ, HomologicalComplex.homologyMap (θ.app G) (n : ℤ) =
          (a n).hom ≫ HomologicalComplex.homologyMap d (n : ℤ) ≫ (b n).inv := by
    obtain ⟨a, b, hab⟩ := picardRightCechCup_homology f g F U V hU hV hUc hVc θ hθ G
    refine ⟨a, b, fun n ↦ ?_⟩
    have hn := picardExternalCupHomology_unique f g F G _
      (fun n ↦ HomologicalComplex.homologyMap d (n : ℤ)) hab hd n
    calc
      HomologicalComplex.homologyMap (θ.app G) (n : ℤ) =
          (a n).hom ≫ ((a n).inv ≫
            HomologicalComplex.homologyMap (θ.app G) (n : ℤ) ≫ (b n).hom) ≫
              (b n).inv := by simp
      _ = (a n).hom ≫ HomologicalComplex.homologyMap d (n : ℤ) ≫ (b n).inv := by
        rw [hn]
  obtain ⟨a1, b1, h1⟩ := component S.X₁ d1 hd1
  obtain ⟨a2, b2, h2⟩ := component S.X₂ d2 hd2
  obtain ⟨a3, b3, h3⟩ := component S.X₃ d3 hd3
  exact ⟨d1, d2, d3, S.mapNatTrans θ, a1, b1, a2, b2, a3, b3,
    hd1, hd2, hd3, h1, h2, h3⟩

end AlgebraicGeometry.Scheme.Modules
