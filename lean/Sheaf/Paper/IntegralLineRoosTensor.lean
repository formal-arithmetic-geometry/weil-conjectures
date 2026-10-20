/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Exact tensor by a coefficient line commutes with the strict Roos complex

Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 3.4.12(4); Stacks 08TC.
(blueprint: lem-sf-integral-line-roos-tensor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits
namespace WeilConjectures
open IntegralOnSlice

/-- Exact line tensor preserves good complexes and commutes with the actual augmented Roos
construction. The assertion is entirely on complexes and assumes no completeness.
Source: Bhatt--Scholze, Definition 3.4.10, Lemma 3.4.12(4); Stacks 06YN and 08TC
(blueprint: lem-sf-integral-line-roos-tensor).

Proof: locally trivialize T. Tensor by T is the identity on every trivializing slice;
restriction is exact and detects vanishing over a cover. Thus tensor by T is exact.
Its canonical countable-product comparison is also an isomorphism: restriction of
products is sectionwise and on each trivializing slice that comparison is the
identity. Tensoring complexes by T[0] is naturally isomorphic to this termwise exact
functor, since the only nonzero second degree is zero, with differential d tensor 1.
It therefore preserves acyclic complexes and quasi-isomorphisms. This proves
K-flatness of T[0]. Total tensor of K-flat complexes is K-flat, and tensor products
and coproducts of flat terms are flat, so good complexes remain good.
For any complex P, the balanced map from the reduction of P tensor T to the reduction
of P tensored over the completed ring with T sends a tensor (x tensor y) to
(a tensor x) tensor y, with inverse (a tensor x) tensor y to a tensor (x tensor y).
It is balanced, compatible with sheafification, natural in P and commutes with
quotient transitions and with the canonical reduction unit. Tensor by T commutes
with the countable products just described and with the finite biproducts of the
mapping cocone. These comparisons commute with 1 minus shift and with the signed
cocone differential. They give the displayed isomorphism rho. On the product
coordinate the tensored unit and roosUnit of the tensor have the same quotient
components; on the shifted product coordinate both are zero. The two projections
of the mapping cocone prove the displayed equation. No boundedness or finite
cover assumption enters; empty sites and zero complexes satisfy the same formulas. -/
theorem integralLine_roosTensor
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : AlgebraicGeometry.Scheme.{t})
    (T : Mod l E X none) [T.IsFiniteLocallyFreeOfRank 1] :
    let T₀ := (HomologicalComplex.single (Mod l E X none) (.up ℤ) 0).obj T
    let F := (Functor.prod' (𝟭 (Cx l E X none))
      ((Functor.const (Cx l E X none)).obj T₀)) ⋙
        coefficientTotalTensor.{u, t + 1, t} (topology X none) (ring l E X none)
    CochainComplex.IsKFlatIndependentCoefficients
        (J := topology X none) (R := ring l E X none) T₀ ∧
      (∀ (A B : Cx l E X none) (f : A ⟶ B), QuasiIso f → QuasiIso (F.map f)) ∧
      ∀ P : (Good l E X none).FullSubcategory,
        Good l E X none (F.obj P.obj) ∧
          ∃ ρ : F.obj (integralOperationsRoos ((tower l E X none).obj P.obj)) ≅
              integralOperationsRoos ((tower l E X none).obj (F.obj P.obj)),
            F.map (roosUnit l E X none P.obj) ≫ ρ.hom =
              roosUnit l E X none (F.obj P.obj) := by sorry

end WeilConjectures
