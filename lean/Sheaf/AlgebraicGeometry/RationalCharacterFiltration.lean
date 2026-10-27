/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.AlgebraicGeometry.RationalRepresentationGZero
public import Sheaf.AlgebraicGeometry.GroupScheme.RationalHighestWeightData

/-! # Rational character filtrations and subquotients

Source: Andersen, The strong linkage principle (1980), pp.55--58; Milne,
Algebraic Groups (2017), Sections 4a--4b and 22.29--22.30.
(blueprint: def-sfb-rational-character-filtration)

## Main definitions

- `IsSubquotient`: coaction subquotients.
- `characterModule`: the character on the actual field.
- `Filtration`: finite flags with specified character quotients.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
open scoped TensorProduct MonObj
namespace AlgebraicGeometry.RationalCharacterFiltration
open EquivariantCoherent RationalHighestWeight

variable {F : Type u} [Field F]
variable {G : Grp (Over (Spec (.of F)))} [IsAffine G.X.left]

/-- A subquotient is a surjective comodule map from a stable subspace, with the
restricted coaction fixed by the inclusion. No rational-point test is substituted.
Source: Milne, Sections 4a--4b; Andersen, pp.57--58.
(blueprint: def-sfb-rational-character-filtration) -/
def IsSubquotient {V W : Type u} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]
    (cV : V →ₗ[F] V ⊗[F] coordinateAlgebra G)
    (cW : W →ₗ[F] W ⊗[F] coordinateAlgebra G) : Prop :=
  ∃ (N : Submodule F W) (d : N →ₗ[F] N ⊗[F] coordinateAlgebra G)
    (q : N →ₗ[F] V),
    IsStable cW N ∧ N.subtype.rTensor (coordinateAlgebra G) ∘ₗ d = cW ∘ₗ N.subtype ∧
      Function.Surjective q ∧ q.rTensor (coordinateAlgebra G) ∘ₗ d = cV ∘ₗ q

/-- The one-dimensional character coaction, written without any chosen module.
Source: Milne, Section 22.30. (blueprint: def-sfb-rational-character-filtration) -/
def characterCoaction (χ : G ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)) :
    F →ₗ[F] F ⊗[F] coordinateAlgebra G :=
  (TensorProduct.mk F F (coordinateAlgebra G)).flip (characterElement χ)

/-- The character tensor satisfies the coordinate counit law.
Source: Milne, Section 4a and 22.30.
(blueprint: def-sfb-rational-character-filtration)
Proof: pull back the Laurent coordinate along the character. Its value at the
identity is one because the character is a group homomorphism. The tensor unit
identification then sends v tensor one to v. -/
theorem characterCoaction_counital
    (χ : G ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)) :
    HopfAction.Counital F (coordinateAlgebra G) F (characterCoaction χ) := by
  sorry

/-- The character tensor satisfies the coordinate coassociativity law.
Source: Milne, Section 4a and 22.30.
(blueprint: def-sfb-rational-character-filtration)
Proof: the Laurent coordinate is group-like. Pullback along the group homomorphism
χ preserves comultiplication, so Delta(χ)=χ tensor χ. On a scalar v both composites
are v tensor χ tensor χ, with precisely the tensor associator in Coassociative. -/
theorem characterCoaction_coassociative
    (χ : G ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)) :
    HopfAction.Coassociative F (coordinateAlgebra G) F (characterCoaction χ) := by
  sorry

/-- The actual one-dimensional rational character module.
Source: Milne, Section 22.30. (blueprint: def-sfb-rational-character-filtration) -/
def characterModule (χ : G ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)) :
    Representation F G.X where
  space := ModuleCat.of F F
  finite := inferInstance
  coaction := characterCoaction χ
  counit := characterCoaction_counital χ
  coassoc := characterCoaction_coassociative χ

/-- A finite flag of actual rational subspaces, with surjective character quotient
maps and their restricted coactions. Constant tails allow length zero.
Source: Andersen, pp.57--58; Milne, Sections 4a--4b and 22.30.
(blueprint: def-sfb-rational-character-filtration) -/
structure Filtration (M : Representation F G.X) where
  length : ℕ
  step : ℕ → Submodule F M.space
  monotone : Monotone step
  first : step 0 = ⊥
  last : step length = ⊤
  stable : ∀ j, IsStable M.coaction (step j)
  character : Fin length → (G ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))
  factor : ∀ j : Fin length, step (j.val + 1) →ₗ[F] F
  surjective : ∀ j, Function.Surjective (factor j)
  kernel : ∀ j : Fin length,
    LinearMap.ker (factor j) = (step j.val).comap (step (j.val + 1)).subtype
  restricted : ∀ j : Fin length,
    step (j.val + 1) →ₗ[F] step (j.val + 1) ⊗[F] coordinateAlgebra G
  inclusion_equivariant : ∀ j : Fin length,
    (step (j.val + 1)).subtype.rTensor (coordinateAlgebra G) ∘ₗ restricted j =
      M.coaction ∘ₗ (step (j.val + 1)).subtype
  quotient_equivariant : ∀ j : Fin length,
    (factor j).rTensor (coordinateAlgebra G) ∘ₗ restricted j =
      characterCoaction (character j) ∘ₗ factor j

end AlgebraicGeometry.RationalCharacterFiltration
