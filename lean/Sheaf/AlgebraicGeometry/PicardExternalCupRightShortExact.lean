/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.AlgebraicGeometry.PicardExternalCupCochain
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

import Sheaf.AlgebraicGeometry.PicardExternalCupRightExactLadder
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four

/-! # External cup and a short exact sequence in the right coefficient

Source: Stacks Project, Varieties, Tag 0BED, the short exact sequence argument
following equation 33.29.1.1, applied in the right variable.
(blueprint: lem-sc-picard-external-cup-right-short-exact).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- In a short exact sequence of right coefficients, invertibility of the external
cup comparison for the middle and quotient coefficients implies invertibility for
its subobject. There is no cohomological bound or induction hypothesis here.

Source: Stacks Project, Varieties, Tag 0BED, the paragraph after equation 33.29.1.1
and its application to the right variable in the paragraph beginning "Arguing in
the same fashion" (blueprint: lem-sc-picard-external-cup-right-short-exact).

Proof:
1. Choose finite affine covers of X and Y and the product cover. Affine diagonal
makes all finite intersections affine. The quasi-coherent sequence S remains
exact on their sections. Over the field k, tensoring with sections of F is exact,
and the finite direct sums in each total degree preserve exactness. The affine
pullback and tensor section formulas similarly give a short exact sequence of
product Cech complexes for the external coefficients.
2. The signed Cech refinement and cup map of equation 33.29.1.1 is natural in
S. It therefore gives a morphism between these two short exact sequences of
complexes. The long exact homology sequences form a commuting ladder, including
connecting morphisms. Cech comparison isomorphisms transport this ladder to the
scalar resolution models, naturally in S.
3. The transported comparison agrees on homology with each specified c1, c2,
c3: use the tensor Kunneth isomorphism for the nonnegative scalar models, lift
factor homology classes to cycles, and apply the three normalization hypotheses.
Pure tensors span each summand, so the resulting equality holds on all homology.
Thus the hypotheses on c2 and c3 make the four outside maps of the five-term
ladder around H^n of c1 invertible. The five lemma makes its middle map invertible.
For n = 0 the two preceding terms are zero, and the same lemma applies. No
vanishing of positive cohomology is assumed, and the construction covers zero
coefficients and empty schemes. -/
theorem picardExternalCupCochain_isIso_of_right_shortExact
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (pullback.diagonal f)] [IsAffineHom (pullback.diagonal g)]
    (F : X.Modules) [F.IsQuasicoherent]
    (S : ShortComplex Y.Modules) (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    (c1 : picardExternalTotal f g F S.X₁ ⟶
      picardScalarModel (pullback.fst f g ≫ f) (externalCupCoefficients f g F S.X₁))
    (hc1 : IsPicardExternalCupCochain f g F S.X₁ c1)
    (c2 : picardExternalTotal f g F S.X₂ ⟶
      picardScalarModel (pullback.fst f g ≫ f) (externalCupCoefficients f g F S.X₂))
    (hc2 : IsPicardExternalCupCochain f g F S.X₂ c2)
    (c3 : picardExternalTotal f g F S.X₃ ⟶
      picardScalarModel (pullback.fst f g ≫ f) (externalCupCoefficients f g F S.X₃))
    (hc3 : IsPicardExternalCupCochain f g F S.X₃ c3)
    (h2 : ∀ n : ℕ, IsIso (HomologicalComplex.homologyMap c2 (n : ℤ)))
    (h3 : ∀ n : ℕ, IsIso (HomologicalComplex.homologyMap c3 (n : ℤ)))
    (n : ℕ) : IsIso (HomologicalComplex.homologyMap c1 (n : ℤ)) := by
  obtain ⟨A, B, φ, eA, eB, hA, hB, hφ, hout⟩ :=
    picardExternalCupCochain_right_exact_ladder k X Y f g F S hS c1 hc1 c2 hc2 c3 hc3 n
  obtain ⟨h0, h1, h3, h4⟩ := hout h2 h3
  have := h0
  have := h4
  have hmid : IsIso (ComposableArrows.app' φ 2) :=
    Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono hA hB φ inferInstance h1 h3 inferInstance
  rw [hφ] at hmid
  have : IsIso (eA.hom ≫ HomologicalComplex.homologyMap c1 (n : ℤ)) :=
    (isIso_comp_right_iff _ eB.inv).mp hmid
  exact (isIso_comp_left_iff eA.hom _).mp this

end AlgebraicGeometry.Scheme.Modules
