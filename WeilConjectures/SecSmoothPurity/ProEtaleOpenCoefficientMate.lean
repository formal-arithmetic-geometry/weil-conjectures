/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.OpenScalarExchange
public import WeilConjectures.SecSmoothPurity.ReductionDirectImageComparison
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Mate of the normalized pro-etale open coefficient comparison

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
`sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md`,
Locality paragraph, final mate identification for the source-open scalar comparison.
(blueprint: lem-sp-proetale-open-coefficient-mate)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- The canonical scalar/pullback comparison `a = (tensorPullbackIso φ j).inv` is the
adjunction mate of `E⁻¹ = (openScalarIso φ j).inv : J_B T_U → T_Z J_A` for the normalized
open adjunctions `J_A ⊣ j_A^*` and `J_B ⊣ j_B^*`. The equality of natural transformations
contains naturality in `L`; its component at `L` is
`a_L = j_B^* T_Z(ε_{A,L}) ∘ j_B^*(E_{j_A^* L})⁻¹ ∘ η_{B,T_U j_A^* L}`, and under the mate
bijection it is equivalent to `ε_{B,T_Z L} ∘ J_B(a_L) ∘ E_{j_A^* L} = T_Z(ε_{A,L})`.
The maps are the ordinary unbounded constant-ring pro-etale constructions, so no
flatness, boundedness, constructibility, or Tor-amplitude hypothesis is present.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
`sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md`,
Locality paragraph, final mate identification for the source-open scalar comparison.
(blueprint: lem-sp-proetale-open-coefficient-mate)

Proof. Step 1: by `mateEquiv_apply` the component of the mate at `L` is the displayed
unit/inverse-comparison/counit composite, and `mateEquiv_counit` gives the counit form.
Step 2: write `c = tensorPullbackIso φ j`, the canonical (balanced K-flat) tensor/pullback
comparison, natural in its argument. The open unit identity of
lem-sp-open-scalar-counit-square (in Lean the unit equation `openScalarIso_unit`) gives
`η_{B,T_U M} ≫ j_B^*(E⁻¹_M) = T_U(η_{A,M}) ≫ c⁻¹_{J_A M}`. Put `M = j_A^* L`, use
naturality of `c⁻¹` along `ε_{A,L}` and the triangle identity
`η_A j_A^* ≫ j_A^* ε_A = id`: the composite is `c⁻¹_L = a_L`.
Step 3: for `A = B` both comparisons are the scalar unitors and the formula reduces to the
triangle identity; for `U = ∅` all categories over `U` are zero and both sides vanish. -/
theorem proEtaleOpenCoefficientMate
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j] :
    (CategoryTheory.mateEquiv
      (Scheme.proEtaleRingDerivedOpenAdjunction j
        (Scheme.proEtaleConstantRing Z A) (Scheme.proEtaleConstantRing U A)
        (Scheme.proEtaleConstantRingComparison j A))
      (Scheme.proEtaleRingDerivedOpenAdjunction j
        (Scheme.proEtaleConstantRing Z B) (Scheme.proEtaleConstantRing U B)
        (Scheme.proEtaleConstantRingComparison j B))
      (CategoryTheory.TwoSquare.mk _ _ _ _ (openScalarIso φ j).inv)).natTrans =
      (tensorPullbackIso φ j).inv := by
  sorry

end AlgebraicGeometry.ProEtale
