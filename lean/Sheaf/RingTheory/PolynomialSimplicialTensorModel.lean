module

public import Sheaf.RingTheory.CotangentResolutionCoherence
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# The augmented polynomial simplicial tensor model

Source: Stacks Project, Cotangent Complex, Tags 08QI and 08QP
(blueprint: lem-trf-polynomial-simplicial-tensor-model).

The tensor factor order is the standard Mathlib scalar-extension convention,
`A' ⊗[A] P`, identified with `P ⊗[A] A'` by tensor symmetry.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w z

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped TensorProduct

namespace Algebra.CotangentResolution

/-- The simplicial algebra with the scalar action specified by the augmentation's
base map. Source: Stacks, Tag 08QI
(blueprint: lem-trf-polynomial-simplicial-tensor-model). -/
def tensorModelAlgebra {f : Arrow CommRingCat.{u}} (P : Augmentation f) :
    SimplicialObject (CommAlgCat.{u} f.left) :=
  Under.lift P.algebra P.base ⋙ (commAlgCatEquivUnder f.left).inverse

/-- The augmentation as a cocone of algebras, retaining the prescribed map to `B`.
Source: Stacks, Tag 08QI
(blueprint: lem-trf-polynomial-simplicial-tensor-model). -/
def tensorModelCocone {f : Arrow CommRingCat.{u}} (P : Augmentation f) :
    Cocone (tensorModelAlgebra P) :=
  (commAlgCatEquivUnder f.left).inverse.mapCocone
    (Under.liftCocone P.algebra P.base ⟨f.right, P.augmentation⟩ f.hom
      (fun n ↦ P.triangle n.unop.len))

/-- Forgetting multiplication in an augmented simplicial algebra. Source: Stacks,
Tag 08QP (blueprint: lem-trf-polynomial-simplicial-tensor-model). -/
def tensorModelModule {A : Type u} [CommRing A]
    {S : SimplicialObject (CommAlgCat.{u} A)} (c : Cocone S) :
    SimplicialObject.Augmented (ModuleCat.{u} A) :=
  ⟨S ⋙ forget₂ (CommAlgCat A) (AlgCat A) ⋙ forget₂ (AlgCat A) (ModuleCat A),
    ((forget₂ (CommAlgCat A) (AlgCat A) ⋙ forget₂ (AlgCat A) (ModuleCat A)).mapCocone c).pt,
    ((forget₂ (CommAlgCat A) (AlgCat A) ⋙ forget₂ (AlgCat A) (ModuleCat A)).mapCocone c).ι⟩

/-- Scalar extension of commutative algebras: operators send `a' ⊗ p` to `a' ⊗ h(p)`.
Source: Stacks, Tag 08QP
(blueprint: lem-trf-polynomial-simplicial-tensor-model). -/
def tensorModelExtension {A : Type u} [CommRing A] (A' : CommAlgCat.{u} A) :
    CommAlgCat.{u} A ⥤ CommAlgCat.{u} A' where
  obj S := CommAlgCat.of A' (A' ⊗[A] S)
  map h := CommAlgCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A' A') h.hom)
  map_id _ := CommAlgCat.hom_ext (Algebra.TensorProduct.map_id)
  map_comp h k :=
    CommAlgCat.hom_ext (Algebra.TensorProduct.map_id_comp k.hom h.hom)

/-- The augmentation of the alternating complex, extended by zero to positive
cohomological degrees. Source: Stacks, Tags 08QI and 08QP
(blueprint: lem-trf-polynomial-simplicial-tensor-model). -/
def tensorModelAugmentation {A : Type u} [CommRing A]
    (S : SimplicialObject.Augmented (ModuleCat.{u} A)) :=
  HomologicalComplex.extendMap (AlgebraicTopology.AlternatingFaceMapComplex.ε.app S)
    ComplexShape.embeddingDownNat

/-- Identification of degree `-n` of the alternating complex with simplicial degree `n`.
Source: Stacks, Tag 08QP
(blueprint: lem-trf-polynomial-simplicial-tensor-model). -/
def tensorModelTermIso {A : Type u} [CommRing A]
    (S : SimplicialObject.Augmented (ModuleCat.{u} A)) (n : ℕ) :
    ((negativeComplex (ModuleCat.{u} A)).obj S.left).X (-(n : ℤ)) ≅ S.left.obj (op ⦋n⦌) :=
  ((AlgebraicTopology.alternatingFaceMapComplex _).obj S.left).extendXIso
    ComplexShape.embeddingDownNat (i := n) rfl

/-- The target `B[0]` of the extended alternating augmentation. Source: Stacks,
Tag 08QP (blueprint: lem-trf-polynomial-simplicial-tensor-model). -/
def tensorModelTarget {A : Type u} [CommRing A]
    (S : SimplicialObject.Augmented (ModuleCat.{u} A)) :
    CochainComplex (ModuleCat.{u} A) ℤ :=
  ((ChainComplex.single₀ (ModuleCat.{u} A)).obj S.right).extend
    ComplexShape.embeddingDownNat

/-- Identification of the augmentation target in degree zero with its module.
Source: Stacks, Tag 08QP
(blueprint: lem-trf-polynomial-simplicial-tensor-model). -/
def tensorModelTargetIso {A : Type u} [CommRing A]
    (S : SimplicialObject.Augmented (ModuleCat.{u} A)) :
    (tensorModelTarget S).X 0 ≅ S.right :=
  ((ChainComplex.single₀ (ModuleCat.{u} A)).obj S.right).extendXIso
    ComplexShape.embeddingDownNat (i := 0) rfl

/-- Polynomial terms are monomial-free and flat, their coefficient tensor expansion
is natural, and scalar extension preserves the prescribed augmented simplicial model.
Source: Stacks, Tags 08QI and 08QP
(blueprint: lem-trf-polynomial-simplicial-tensor-model).

Proof:
1. Finite coefficient expansion in the chosen polynomial presentation gives the
   monomial basis, even for an empty or infinite variable set.
2. The tensor universal property gives the coefficient map. Its inverse is the finite
   sum of monomial tensors. Check both composites on single coordinates and pure tensors;
   balancing moves each coefficient between the factors. Applying a linear map to each
   coordinate proves naturality.
3. An injective module map remains injective coordinatewise in this expansion. Tensor
   symmetry gives injectivity for the other factor order. The flat tensor exactness
   theorem (lem-weil-pbc-flat-tensor-exact) then gives preservation of exact sequences.
4. Extend all operators and the augmentation by `a' ⊗ p ↦ a' ⊗ h(p)`; functoriality
   preserves the simplicial identities. Lift each coefficient of a finite sum of tensors
   along the original surjective augmentation to prove its new surjectivity.
5. The coefficient isomorphism for `M = A'` is multiplicative: on monomial tensors both
   products have coefficient `a'b'` and exponent `α + β`. It preserves the unit, giving
   the specified polynomial algebra isomorphism after base change.
6. In degree `-n` the two scalar-extended complexes have the same tensor module. Their
   differentials agree by additivity of tensoring the alternating face sum; positive
   degrees are zero. These identity components give the displayed chain isomorphism.
   At degree zero both augmentations send `a' ⊗ p` to `a' ⊗ ε(p)` and all other
   components vanish. Localizing the chain isomorphism and this equality gives the
   required derived isomorphism and augmentation square. No quasi-isomorphism of the
   original augmentation is assumed.
-/
theorem polynomial_simplicial_tensor_model
    {f : Arrow CommRingCat.{u}} (P : Augmentation f)
    (A' : CommAlgCat.{u} f.left) (I : ℕ → Type v)
    (e : ∀ n : ℕ, MvPolynomial (I n) f.left ≃ₐ[f.left]
      (tensorModelAlgebra P).obj (op ⦋n⦌))
    (hε : ∀ n : ℕ, Function.Surjective (P.augmentation.app (op ⦋n⦌)))
    [HasDerivedCategory.{z} (ModuleCat.{u} A')] :
    (∀ n : ℕ,
      (∃ b : Module.Basis (I n →₀ ℕ) f.left ((tensorModelAlgebra P).obj (op ⦋n⦌)),
        ∀ α : I n →₀ ℕ, b α = e n (MvPolynomial.monomial α 1)) ∧
      Module.Free f.left ((tensorModelAlgebra P).obj (op ⦋n⦌)) ∧
      Module.Flat f.left ((tensorModelAlgebra P).obj (op ⦋n⦌))) ∧
    (∀ (n : ℕ) (M N K : ModuleCat.{w} f.left) (g : M ⟶ N) (h : N ⟶ K),
      Function.Exact g h →
      Function.Exact (g.hom.lTensor ((tensorModelAlgebra P).obj (op ⦋n⦌)))
        (h.hom.lTensor ((tensorModelAlgebra P).obj (op ⦋n⦌))) ∧
      Function.Exact (g.hom.rTensor ((tensorModelAlgebra P).obj (op ⦋n⦌)))
        (h.hom.rTensor ((tensorModelAlgebra P).obj (op ⦋n⦌)))) ∧
    (∀ n : ℕ, ∃ F : ∀ M : ModuleCat.{w} f.left,
      ((tensorModelAlgebra P).obj (op ⦋n⦌) ⊗[f.left] M) ≃ₗ[f.left] ((I n →₀ ℕ) →₀ M),
      (∀ (M : ModuleCat.{w} f.left) (p : (tensorModelAlgebra P).obj (op ⦋n⦌))
        (m : M) (α : I n →₀ ℕ),
        F M (p ⊗ₜ m) α = MvPolynomial.coeff α ((e n).symm p) • m) ∧
      (∀ (M : ModuleCat.{w} f.left) (x : (I n →₀ ℕ) →₀ M),
        (F M).symm x = x.sum (fun α m ↦ e n (MvPolynomial.monomial α 1) ⊗ₜ m)) ∧
      (∀ (M N : ModuleCat.{w} f.left) (g : M ⟶ N)
        (x : (tensorModelAlgebra P).obj (op ⦋n⦌) ⊗[f.left] M),
        F N (g.hom.lTensor _ x) = Finsupp.mapRange.linearMap g.hom (F M x))) ∧
    (∀ n : ℕ, Function.Surjective
      (((tensorModelExtension A').mapCocone (tensorModelCocone P)).ι.app (op ⦋n⦌))) ∧
    (∀ n : ℕ, ∃ e' :
      (tensorModelExtension A').obj ((tensorModelAlgebra P).obj (op ⦋n⦌)) ≃ₐ[A']
        MvPolynomial (I n) A',
      ∀ (α : I n →₀ ℕ) (a' : A'),
        e' (a' ⊗ₜ[f.left] e n (MvPolynomial.monomial α 1)) =
          MvPolynomial.monomial α a') ∧
    (∃ ψ :
      ((ModuleCat.extendScalars (algebraMap f.left A')).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          ((negativeComplex (ModuleCat.{u} f.left)).obj
            (tensorModelModule (tensorModelCocone P)).left) ≅
      (negativeComplex (ModuleCat.{u} A')).obj
        (tensorModelModule ((tensorModelExtension A').mapCocone (tensorModelCocone P))).left,
      (∀ (n : ℕ) (a' : A') (p : (tensorModelAlgebra P).obj (op ⦋n⦌)),
        (tensorModelTermIso
          (tensorModelModule ((tensorModelExtension A').mapCocone (tensorModelCocone P))) n).hom
          (ψ.hom.f (-(n : ℤ))
            (a' ⊗ₜ[f.left] (tensorModelTermIso
              (tensorModelModule (tensorModelCocone P)) n).inv p)) = a' ⊗ₜ[f.left] p) ∧
      ∃ τ :
        ((ModuleCat.extendScalars (algebraMap f.left A')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
            (tensorModelTarget (tensorModelModule (tensorModelCocone P))) ≅
        (tensorModelTarget (tensorModelModule
          ((tensorModelExtension A').mapCocone (tensorModelCocone P)))),
        (∀ (a' : A') (b : (tensorModelModule (tensorModelCocone P)).right),
          (tensorModelTargetIso (tensorModelModule
            ((tensorModelExtension A').mapCocone (tensorModelCocone P)))).hom
            (τ.hom.f 0 (a' ⊗ₜ[f.left]
              (tensorModelTargetIso (tensorModelModule (tensorModelCocone P))).inv b)) =
                a' ⊗ₜ[f.left] b) ∧
        ∃ φ :
          DerivedCategory.Q.obj
            (((ModuleCat.extendScalars (algebraMap f.left A')).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj
                ((negativeComplex (ModuleCat.{u} f.left)).obj
                  (tensorModelModule (tensorModelCocone P)).left)) ≅
          DerivedCategory.Q.obj ((negativeComplex (ModuleCat.{u} A')).obj
            (tensorModelModule ((tensorModelExtension A').mapCocone (tensorModelCocone P))).left),
        φ = DerivedCategory.Q.mapIso ψ ∧
        φ.hom ≫
          DerivedCategory.Q.map (tensorModelAugmentation (tensorModelModule
            ((tensorModelExtension A').mapCocone (tensorModelCocone P)))) =
          DerivedCategory.Q.map
            (((ModuleCat.extendScalars (algebraMap f.left A')).mapHomologicalComplex
              (ComplexShape.up ℤ)).map
                (tensorModelAugmentation (tensorModelModule (tensorModelCocone P)))) ≫
            DerivedCategory.Q.map τ.hom) := by
  sorry

end Algebra.CotangentResolution
