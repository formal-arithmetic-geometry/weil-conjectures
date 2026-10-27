/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Sheaf.Paper.DerivedTensorRealization

/-! # The lisse heart specialization of a derived tensor calculation

Source: Bhatt--Scholze Remark 6.8.15; Stacks 07A4.
(blueprint: lem-real-tensor-heart-specialization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme MonoidalCategory
open scoped TensorProduct MonoidalCategory
namespace WeilConjectures.LisseRealization
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Specialization to finite locally free degree-zero sheaves of the specified
comparison, with tensor coherence and its cocycle normalization.
Source: Bhatt--Scholze Proposition 6.8.14(2), Remark 6.8.15; Stacks 06YU
(blueprint: lem-real-tensor-heart-specialization).

Proof: a.image and a.degree_zero identify lisse inputs with finite locally free
sheaves in degree zero. These are flat: on a trivializing pro-etale cover tensor
is a finite sum of the identity, also for the empty sum. The flat-single tensor
cohomology theorem therefore identifies the ordinary derived tensor with the
ordinary sheaf tensor in degree zero. Its cohomology-normalized identification
and d.raw define t.tensor. The lisse criterion, the completed unit calculation,
and d.unit give t.tensor_mem, t.unit_mem and t.unit. Naturality follows by taking
H0 of the natural derived comparison. Associativity, symmetry and unit equations
are checked on flat-term K-flat representatives using d.models: all maps are the
same balanced maps of the entire quotient towers, with zero shifted coordinate;
associativity rearranges three factors, symmetry has the signed interchange, and
the unit multiplies its coefficient. Descent and H0 give the four coherence laws.
For normalization, apply the two scalar counit equations in d.models to cocycles.
The pure-tensor quotient coordinates give the HomologyTensor pairing; its equality
on cocycles descends through the two homology quotients. This is exactly the
TensorNormalized.models equation. The same H0 identification defines e in the
last assertion, which hence uses d.raw itself. Rank zero and varying ranks are
covered by the same local argument, and torsion integral representatives are
allowed because no flatness of their cohomology was used. -/
theorem tensor_heart_specialization (X : Base D l hl) (a : At D l hl E X)
    (d : DerivedTensorRealization D l hl E X a) :
    ∃ t : TensorAt D l hl E X a, Nonempty (TensorNormalized D l hl E X a t) ∧
    (∀ (K L : Raw D l hl E X) (hK : Lisse D l hl E X K)
    (hL : Lisse D l hl E X L),
    ∃ e : (realizationOrdinaryTensor D l hl E X).obj (a.J.obj K, a.J.obj L) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((a.sheaf D l hl E).obj K ⊗ (a.sheaf D l hl E).obj L),
      (DerivedCategory.homologyFunctor _ 0).map ((d.raw.app (K, L)).hom ≫ e.hom) ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).hom.app _ =
      (t.tensor K L hK hL).hom) := by sorry

end WeilConjectures.LisseRealization
