module

public import Sheaf.AlgebraicGeometry.PicardExternalCechCupBidegree
import Sheaf.AlgebraicGeometry.PicardExternalCechCupBidegreeLeibnizCoordinate

/-! # External Alexander--Whitney pure-tensor Leibniz calculation
Source: Stacks Project, Tags 0BED and 07MB.
(blueprint: lem-sc-picard-external-cech-cup-leibniz).
-/

@[expose] public section
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
variable {k : Type w} [Field k] {X Y : Scheme.{w}}

/-- The signed face calculation on a pure tensor, before tensor-total assembly.
Source: Stacks Project, Tag 07MB, calculation after equation 20.25.3.2, coefficients in degree zero;
Tag 0BED, equation-kunneth-on-cech, for the external coordinates.
(blueprint: lem-sc-picard-external-cech-cup-leibniz).
Proof: Apply the target Cech coordinate equivalence and evaluate on a tuple y of
length p+q+2. Expand the target differential as its alternating restriction sum.
The three assumed bidegree formulas identify the cup coordinates. Naturality of
both pullback adjunction units identifies a pulled restricted section with the
restriction of its pullback. Presheaf composition and compatibility of tensor
sections with restriction identify the successive restrictions on each face.
Expand d(a) cup b and a cup d(b) using these identities and additivity. The front
terms indexed 0 through p agree with the first p+1 target faces, with signs
(-1)^j. The last front term and the first back term restrict the same two sections
to the same intersection, with signs (-1)^(p+1) and (-1)^p, and cancel. The back
terms indexed r=1 through q+1 agree with target faces p+r, with signs (-1)^(p+r).
Splitting the target face sum at p+1 thus gives the displayed identity. The two
degree transports only identify equal tuple lengths. Coordinate extensionality
concludes. For p=0 or q=0 the same shared terms cancel; in characteristic two
opposite terms still sum to zero. Empty index families have no tuples and zero
coefficients give zero sections. This calculation makes no use of a coproduct,
a tensor-total inclusion, or a family of maps in other bidegrees. -/
theorem picardExternalCechCupBidegree_leibniz
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens) (F : X.Modules) (G : Y.Modules)
    (p q : ℕ)
    (h : ((curriedTensor (ModuleCat.{w} k)).obj
        (((picardCechFunctor f U).obj F).X p)).obj (((picardCechFunctor g V).obj G).X q) ⟶
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X (p + q))
    (h₁ : ((curriedTensor (ModuleCat.{w} k)).obj
        (((picardCechFunctor f U).obj F).X (p + 1))).obj (((picardCechFunctor g V).obj G).X q) ⟶
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X ((p + 1) + q))
    (h₂ : ((curriedTensor (ModuleCat.{w} k)).obj
        (((picardCechFunctor f U).obj F).X p)).obj (((picardCechFunctor g V).obj G).X (q + 1)) ⟶
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X (p + (q + 1)))
    (hh : IsPicardExternalCechCupBidegree f g U V F G p q h)
    (hh₁ : IsPicardExternalCechCupBidegree f g U V F G (p + 1) q h₁)
    (hh₂ : IsPicardExternalCechCupBidegree f g U V F G p (q + 1) h₂)
    (a : ((picardCechFunctor f U).obj F).X p)
    (b : ((picardCechFunctor g V).obj G).X q) :
    ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).d
        (p + q) (p + q + 1) (h (a ⊗ₜ[k] b)) =
      (eqToHom (congrArg (fun n ↦
        ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X n)
        (Nat.add_right_comm p 1 q)))
          (h₁ (((picardCechFunctor f U).obj F).d p (p + 1) a ⊗ₜ[k] b)) +
    (-1 : ℤ) ^ p • (eqToHom (congrArg (fun n ↦
        ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X n)
        (Nat.add_assoc p q 1).symm))
          (h₂ (a ⊗ₜ[k] ((picardCechFunctor g V).obj G).d q (q + 1) b)) := by
  apply (TopCat.Presheaf.cechComplexFunctorXAddEquiv
    (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
      pullback.snd f g ⁻¹ᵁ V ij.2)
    (scalarPresheaf (pullback.fst f g ≫ f) (externalCupCoefficients f g F G))
    (p + q + 1)).injective
  funext y
  exact picardExternalCechCupBidegree_leibniz_coordinate f g U V F G p q h h₁ h₂
    hh hh₁ hh₂ a b y

end
end AlgebraicGeometry.Scheme.Modules
