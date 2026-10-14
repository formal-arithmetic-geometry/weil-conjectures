module
public import Sheaf.AlgebraicGeometry.PicardExternalCechCupBidegree

@[expose] public section
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
variable {k : Type w} [Field k] {X Y : Scheme.{w}}

/-- Coordinate form of the external Cech Leibniz identity.
Proof: Expand the alternating face sum in the target Cech differential. The front
faces agree with d(a) cup b, the back faces agree with a cup d(b) with sign
(-1)^p, and the shared face cancels. Pullback-unit naturality and restriction
composition identify all coordinates.
(blueprint: lem-sc-picard-external-cech-cup-leibniz-coordinate). -/
theorem picardExternalCechCupBidegree_leibniz_coordinate
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens) (F : X.Modules) (G : Y.Modules)
    (p q : ℕ)
    (h : ((curriedTensor (ModuleCat.{w} k)).obj (((picardCechFunctor f U).obj F).X p)).obj
      (((picardCechFunctor g V).obj G).X q) ⟶
      ((picardCechFunctor (pullback.fst f g ≫ f) (fun ij : ι × κ ↦
        pullback.fst f g ⁻¹ᵁ U ij.1 ⊓ pullback.snd f g ⁻¹ᵁ V ij.2)).obj
          (externalCupCoefficients f g F G)).X (p + q))
    (h₁ : ((curriedTensor (ModuleCat.{w} k)).obj (((picardCechFunctor f U).obj F).X (p + 1))).obj
      (((picardCechFunctor g V).obj G).X q) ⟶
      ((picardCechFunctor (pullback.fst f g ≫ f) (fun ij : ι × κ ↦
        pullback.fst f g ⁻¹ᵁ U ij.1 ⊓ pullback.snd f g ⁻¹ᵁ V ij.2)).obj
          (externalCupCoefficients f g F G)).X ((p + 1) + q))
    (h₂ : ((curriedTensor (ModuleCat.{w} k)).obj (((picardCechFunctor f U).obj F).X p)).obj
      (((picardCechFunctor g V).obj G).X (q + 1)) ⟶
      ((picardCechFunctor (pullback.fst f g ≫ f) (fun ij : ι × κ ↦
        pullback.fst f g ⁻¹ᵁ U ij.1 ⊓ pullback.snd f g ⁻¹ᵁ V ij.2)).obj
          (externalCupCoefficients f g F G)).X (p + (q + 1)))
    (hh : IsPicardExternalCechCupBidegree f g U V F G p q h)
    (hh₁ : IsPicardExternalCechCupBidegree f g U V F G (p + 1) q h₁)
    (hh₂ : IsPicardExternalCechCupBidegree f g U V F G p (q + 1) h₂)
    (a : ((picardCechFunctor f U).obj F).X p)
    (b : ((picardCechFunctor g V).obj G).X q)
    (y : Fin (p + q + 2) → ι × κ) :
    TopCat.Presheaf.cechComplexFunctorXAddEquiv
      (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓ pullback.snd f g ⁻¹ᵁ V ij.2)
      (scalarPresheaf (pullback.fst f g ≫ f) (externalCupCoefficients f g F G))
      (p + q + 1)
      (((picardCechFunctor (pullback.fst f g ≫ f) (fun ij : ι × κ ↦
        pullback.fst f g ⁻¹ᵁ U ij.1 ⊓ pullback.snd f g ⁻¹ᵁ V ij.2)).obj
          (externalCupCoefficients f g F G)).d (p + q) (p + q + 1) (h (a ⊗ₜ[k] b))) y =
    TopCat.Presheaf.cechComplexFunctorXAddEquiv
      (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓ pullback.snd f g ⁻¹ᵁ V ij.2)
      (scalarPresheaf (pullback.fst f g ≫ f) (externalCupCoefficients f g F G))
      (p + q + 1)
      ((eqToHom (congrArg (fun n ↦
        ((picardCechFunctor (pullback.fst f g ≫ f) (fun ij : ι × κ ↦
          pullback.fst f g ⁻¹ᵁ U ij.1 ⊓ pullback.snd f g ⁻¹ᵁ V ij.2)).obj
            (externalCupCoefficients f g F G)).X n) (Nat.add_right_comm p 1 q)))
          (h₁ (((picardCechFunctor f U).obj F).d p (p + 1) a ⊗ₜ[k] b)) +
      (-1 : ℤ) ^ p • (eqToHom (congrArg (fun n ↦
        ((picardCechFunctor (pullback.fst f g ≫ f) (fun ij : ι × κ ↦
          pullback.fst f g ⁻¹ᵁ U ij.1 ⊓ pullback.snd f g ⁻¹ᵁ V ij.2)).obj
            (externalCupCoefficients f g F G)).X n) (Nat.add_assoc p q 1).symm))
          (h₂ (a ⊗ₜ[k] ((picardCechFunctor g V).obj G).d q (q + 1) b))) y := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
