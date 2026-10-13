/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Sheaf.AlgebraicGeometry.PicardExternalCupCochain
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.AlgebraicGeometry.Modules.Dual
import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-! # Exactness of the explicit left-coefficient Cech sequences

Source: Stacks Project, Varieties, Tag 0BED, lemma-kunneth, the short exact
coefficient diagram after equation-kunneth-on-cech.
(blueprint: lem-sc-picard-external-cup-left-cech-exact).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

variable {k : Type w} [Field k] {X Y : Scheme.{w}}

/-- The genuine finite subcover of the affine cover, as a family of opens.
Source: Stacks, Tag 0BED (blueprint: lem-sc-picard-external-cup-left-cech-exact). -/
def picardFiniteAffineOpens (X : Scheme.{w}) [CompactSpace X] :
    X.affineCover.finiteSubcover.I₀ → X.Opens :=
  fun i ↦ (X.affineCover.finiteSubcover.f i).opensRange

/-- Scalar-valued Cech cochains, functorially in the coefficient sheaf.
Source: Stacks, Tag 0BED (blueprint: lem-sc-picard-external-cup-left-cech-exact). -/
def picardScalarCechFunctor (f : X ⟶ Spec (CommRingCat.of k))
    {ι : Type w} (U : ι → X.Opens) : X.Modules ⥤ CochainComplex (ModuleCat.{w} k) ℕ :=
  scalarFunctor f ⋙ sheafToPresheaf _ _ ⋙ cechComplexFunctor U

private instance scalarCech_zero (f : X ⟶ Spec (CommRingCat.of k))
    {ι : Type w} (U : ι → X.Opens) : (picardScalarCechFunctor f U).PreservesZeroMorphisms where
  map_zero := by
    intro P Q
    apply HomologicalComplex.hom_ext
    intro n
    dsimp [picardScalarCechFunctor, cechComplexFunctor,
      Limits.FormalCoproduct.cochainComplexFunctor,
      Limits.FormalCoproduct.cosimplicialObjectFunctor,
      AlgebraicTopology.alternatingCofaceMapComplex,
      AlgebraicTopology.AlternatingCofaceMapComplex.map, Limits.FormalCoproduct.evalOp]
    apply Pi.hom_ext
    intro t
    simp only [Pi.map_π, zero_comp]
    change _ ≫ (0 : _ ⟶ _) = 0
    exact comp_zero

/-- Tensor with a fixed integer-index complex.
Source: Stacks, Tag 0BED (blueprint: lem-sc-picard-external-cup-left-cech-exact). -/
def picardCechTensorRight (C : CochainComplex (ModuleCat.{w} k) ℤ) :
    CochainComplex (ModuleCat.{w} k) ℤ ⥤ CochainComplex (ModuleCat.{w} k) ℤ :=
  ((curriedTensor (ModuleCat.{w} k)).map₂HomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)).flip.obj C

private instance cechTensorRight_zero (C : CochainComplex (ModuleCat.{w} k) ℤ) :
    (picardCechTensorRight C).PreservesZeroMorphisms where
  map_zero := by
    intro P Q
    apply HomologicalComplex.hom_ext
    intro n
    change (HomologicalComplex.mapBifunctorMap (0 : P ⟶ Q) (𝟙 C) _ _).f n = 0
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    simp

/-- Tensor-total Cech model for the left coefficient, extended by zero.
Source: Stacks, Tag 0BED (blueprint: lem-sc-picard-external-cup-left-cech-exact). -/
def picardLeftTensorCechFunctor
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y] (G : Y.Modules) :
    X.Modules ⥤ CochainComplex (ModuleCat.{w} k) ℤ :=
  picardScalarCechFunctor f (picardFiniteAffineOpens X) ⋙
    ComplexShape.embeddingUpNat.extendFunctor _ ⋙
    picardCechTensorRight
      (((picardScalarCechFunctor g (picardFiniteAffineOpens Y)).obj G).extend
        ComplexShape.embeddingUpNat)

/-- Product cover, indexed by pairs from the two finite affine covers.
Source: Stacks, Tag 0BED (blueprint: lem-sc-picard-external-cup-left-cech-exact). -/
def picardProductAffineOpens
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y] :
    X.affineCover.finiteSubcover.I₀ × Y.affineCover.finiteSubcover.I₀ →
      (Limits.pullback f g).Opens :=
  fun i ↦ pullback.fst f g ⁻¹ᵁ picardFiniteAffineOpens X i.1 ⊓
    pullback.snd f g ⁻¹ᵁ picardFiniteAffineOpens Y i.2

/-- Product-cover Cech model of the external coefficient, extended by zero.
Source: Stacks, Tag 0BED (blueprint: lem-sc-picard-external-cup-left-cech-exact). -/
def picardLeftProductCechFunctor
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y] (G : Y.Modules) :
    X.Modules ⥤ CochainComplex (ModuleCat.{w} k) ℤ :=
  tensorPullback (pullback.fst f g) ⋙
    tensorRight ((tensorPullback (pullback.snd f g)).obj G) ⋙
    picardScalarCechFunctor (pullback.fst f g ≫ f) (picardProductAffineOpens f g) ⋙
    ComplexShape.embeddingUpNat.extendFunctor _

/-- The tensor Cech functor sends zero coefficient morphisms to zero.
Source: termwise tensor maps (blueprint: lem-sc-picard-external-cup-left-cech-exact).
Proof: Scalar Cech maps, tensor maps and extension by zero all preserve zero. -/
instance picardLeftTensorCechFunctor_zero
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y] (G : Y.Modules) :
    (picardLeftTensorCechFunctor f g G).PreservesZeroMorphisms := by
  unfold picardLeftTensorCechFunctor
  infer_instance

set_option backward.isDefEq.respectTransparency.types true in
/-- The product Cech functor sends zero coefficient morphisms to zero.
Source: termwise coefficient maps (blueprint: lem-sc-picard-external-cup-left-cech-exact).
Proof: Pullback, tensor, scalar Cech and extension functors preserve zero. -/
instance picardLeftProductCechFunctor_zero
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y] (G : Y.Modules) :
    (picardLeftProductCechFunctor f g G).PreservesZeroMorphisms := by
  have : (tensorPullback (pullback.fst f g)).Additive :=
    (Classical.choose (exists_tensorPullbackAdjunction (pullback.fst f g))).left_adjoint_additive
  unfold picardLeftProductCechFunctor
  infer_instance

/-- Both explicit Cech sequences are short exact in the left coefficient.
Source: Stacks Project, Varieties, Tag 0BED, lemma-kunneth, the short exact
coefficient diagram after equation-kunneth-on-cech.
(blueprint: lem-sc-picard-external-cup-left-cech-exact).

Proof: The finite affine covers have affine finite intersections by the affine
relative diagonals over Spec k. On each intersection a quasi-coherent short exact
sequence has an exact sequence of sections: kernels are sectionwise, and the
quasi-coherent affine cokernel formula gives surjectivity. Scalar restriction to k
preserves this sequence. Tensoring with each section space of G is exact over the
field. Products indexed by cover tuples and the finite sums in each tensor-total
degree preserve short exactness, proving the tensor assertion degreewise. On each
intersection of the product cover, affine pullback and tensor section formulas
identify external coefficient sections with the tensor of the corresponding factor
sections, naturally in the left coefficient. Hence the product-cover sequence is
also degreewise short exact; no flatness of G over O_Y is needed. Extension by zero
preserves these sequences, and degreewise exactness, monicity and epicity give
short exactness of cochain complexes. Empty schemes and zero coefficients yield
zero terms and cause no exception. No cup map or cohomology comparison is used. -/
theorem picardExternalCup_left_cech_exact
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (pullback.diagonal f)] [IsAffineHom (pullback.diagonal g)]
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    (G : Y.Modules) [G.IsQuasicoherent] :
    (S.map (picardLeftTensorCechFunctor f g G)).ShortExact ∧
      (S.map (picardLeftProductCechFunctor f g G)).ShortExact := by sorry

end
end AlgebraicGeometry.Scheme.Modules
