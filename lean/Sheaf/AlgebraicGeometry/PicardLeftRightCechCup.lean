/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Sheaf.AlgebraicGeometry.PicardLeftCechCupConstruction
import Sheaf.Algebra.Homology.TensorTotalExtendNat

/-! # Cochain comparison of the left and right external Cech cups

Source: Stacks Project, Varieties, Tag 0BED, equation-kunneth-on-cech.
(blueprint: lem-sc-picard-left-right-cech-cup).
-/

@[expose] public section
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
variable {k : Type w} [Field k] {X Y : Scheme.{w}}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Left and right Cech cup coordinates agree after zero-extension reindexing.
Source: Stacks, Tag 0BED, equation-kunneth-on-cech; Cohomology Tag 01FD.
(blueprint: lem-sc-picard-left-right-cech-cup).

Proof: The source on the left is the tensor total of the zero-extended factor
complexes. The source on the right is the zero extension of their natural-degree
 tensor total. In nonnegative degree identify the summands by the bijection
between natural pairs p+q=n and integer pairs with nonnegative coordinates.
All remaining summands are zero because a factor is a negative extension term.
The summand identifications give mutually inverse linear maps. Their differential
compatibility follows from the identical tensor signs and extension differentials,
so they define a cochain isomorphism s. The product complexes are definitionally
the same. For each nonnegative summand and pure tensor, the two cup specifications
are precisely pullback of the front and back sections followed by section tensor.
Their tuple values coincide. The Cech tuple comparison is injective; pure tensors
span each tensor summand, and summand inclusions jointly generate the total term.
Thus s.hom followed by the right cup equals the left cup degreewise. In negative
degrees both sides have zero source. No cohomology, affine diagonal or
quasi-coherence assumption is needed. Empty covers and zero modules give zero
summands, and degree zero identifies the single (0,0) summand. -/
theorem picardLeftRightCechCup_compare
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y]
    (F : X.Modules) (G : Y.Modules)
    (θ : picardLeftTensorCechFunctor f g G ⟶ picardLeftProductCechFunctor f g G)
    (hθ : IsPicardLeftCechCup f g G θ)
    (ψ : picardRightTensorCechFunctor f g (picardFiniteAffineOpens X)
      (picardFiniteAffineOpens Y) F ⟶ picardRightProductCechFunctor f g
        (picardFiniteAffineOpens X) (picardFiniteAffineOpens Y) F)
    (hψ : IsPicardRightCechCup f g (picardFiniteAffineOpens X)
      (picardFiniteAffineOpens Y) F ψ) :
    ∃ s : (picardLeftTensorCechFunctor f g G).obj F ≅
        (picardRightTensorCechFunctor f g (picardFiniteAffineOpens X)
          (picardFiniteAffineOpens Y) F).obj G,
      s.hom ≫ ψ.app G = θ.app F := by
  classical
  let A := (picardScalarCechFunctor f (picardFiniteAffineOpens X)).obj F
  let B := (picardScalarCechFunctor g (picardFiniteAffineOpens Y)).obj G
  obtain ⟨s, hs⟩ := HomologicalComplex.tensorTotal_extend_nat A B
  obtain ⟨c, hc, hcoords⟩ := hψ G
  refine ⟨s, ?_⟩
  rw [hc]
  change s.hom ≫ HomologicalComplex.extendMap c ComplexShape.embeddingUpNat = θ.app F
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  have hzA (p : ℤ) (hp : p < 0) :
      IsZero ((A.extend ComplexShape.embeddingUpNat).X p) :=
    A.isZero_extend_X _ p (by intro i; change (i : ℤ) ≠ p; omega)
  have hzB (q : ℤ) (hq : q < 0) :
      IsZero ((B.extend ComplexShape.embeddingUpNat).X q) :=
    B.isZero_extend_X _ q (by intro i; change (i : ℤ) ≠ q; omega)
  by_cases hp : p < 0
  · exact ((tensorRight ((B.extend ComplexShape.embeddingUpNat).X q)).map_isZero
      (hzA p hp)).eq_of_src _ _
  by_cases hq : q < 0
  · exact ((tensorLeft ((A.extend ComplexShape.embeddingUpNat).X p)).map_isZero
      (hzB q hq)).eq_of_src _ _
  lift p to ℕ using (by omega : 0 ≤ p)
  lift q to ℕ using (by omega : 0 ≤ q)
  have hn : n = ((p + q : ℕ) : ℤ) := by
    change (p : ℤ) + (q : ℤ) = n at hpq
    omega
  rcases hn with rfl
  rw [HomologicalComplex.comp_f]
  erw [HomologicalComplex.extendMap_f c
    ComplexShape.embeddingUpNat (i := p + q) rfl]
  try simp only [Category.assoc]
  rw [← Category.assoc, ← Category.assoc]
  erw [hs p q]
  apply (cancel_mono (((picardScalarCechFunctor (pullback.fst f g ≫ f)
    (picardProductAffineOpens f g)).obj (externalCupCoefficients f g F G)).extendXIso
      ComplexShape.embeddingUpNat (i := p + q) rfl).hom).1
  simp only [Category.assoc]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  apply (TopCat.Presheaf.cechComplexFunctorXAddEquiv (picardProductAffineOpens f g)
    (scalarPresheaf (pullback.fst f g ≫ f) (externalCupCoefficients f g F G))
    (p + q)).injective
  funext t
  have hx := (A.extendXIso ComplexShape.embeddingUpNat (i := p) rfl).hom_inv_id
  have hy := (B.extendXIso ComplexShape.embeddingUpNat (i := q) rfl).hom_inv_id
  have hx' : (A.extendXIso ComplexShape.embeddingUpNat (i := p) rfl).inv
      ((A.extendXIso ComplexShape.embeddingUpNat (i := p) rfl).hom x) = x := by
    exact congrArg (fun m ↦ m x) hx
  have hy' : (B.extendXIso ComplexShape.embeddingUpNat (i := q) rfl).inv
      ((B.extendXIso ComplexShape.embeddingUpNat (i := q) rfl).hom y) = y := by
    exact congrArg (fun m ↦ m y) hy
  have hl := hθ F p q
    ((A.extendXIso ComplexShape.embeddingUpNat (i := p) rfl).hom x)
    ((B.extendXIso ComplexShape.embeddingUpNat (i := q) rfl).hom y) t
  have hr := hcoords p q
    ((A.extendXIso ComplexShape.embeddingUpNat (i := p) rfl).hom x)
    ((B.extendXIso ComplexShape.embeddingUpNat (i := q) rfl).hom y) t
  change _ = _ at hl
  simp only [A, B] at hx' hy'
  erw [hx', hy'] at hl
  have hcancel := (((picardScalarCechFunctor (pullback.fst f g ≫ f)
    (picardProductAffineOpens f g)).obj (externalCupCoefficients f g F G)).extendXIso
      ComplexShape.embeddingUpNat (i := p + q) rfl).inv_hom_id
  dsimp only [picardScalarCechFunctor, picardCechFunctor, picardProductAffineOpens] at *
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_tensorHom]
  have hcancel' := congrArg (fun m ↦ m (c.f (p + q)
    (HomologicalComplex.ιMapBifunctor A B (curriedTensor (ModuleCat.{w} k))
      (ComplexShape.up ℕ) p q (p + q) rfl
        (((A.extendXIso ComplexShape.embeddingUpNat (i := p) rfl).hom x) ⊗ₜ[k]
          ((B.extendXIso ComplexShape.embeddingUpNat (i := q) rfl).hom y))))) hcancel
  erw [hcancel']
  exact hr.trans hl.symm

end AlgebraicGeometry.Scheme.Modules
