/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B5
-/
module

public import Sheaf.Paper.FiniteCoefficientPoint

/-! # Completed perfect realization at a geometric point

Source: the integral argument, steps 2–3 and 6–7, of
`lem-weil-point-fibre-equivalence`.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- Completed constant realization embeds bounded finitely generated complete complexes
as integral constructible complexes, and is left adjoint to the specified sections functor.
Source: Stacks, Modules on Sites, Tags 03EI and 093M; Bhatt–Scholze, Propositions
6.6.11 and 6.8.11(3); the point-fibre proof, steps 2–3 and 6–7.
(blueprint: lem-weil-point-integral-perfect-realization).

Proof: write A = O_E and B for its completed constant algebra sheaf. Realize an
A-module M by B tensor over the constant A sheaf with the constant M sheaf.
The balanced formula b tensor m ↦ b times t(m) extends by sheafification and gives
an adjunction with sections restricted along the actual constant-to-completion map.
The ring B is flat over constant A, so realization and sections are exact and the
adjunction descends termwise to derived categories. Its unit on finite free modules
is the constant-section map A ≅ Gamma(B). Exactness and finite presentations make
its unit invertible on every finitely generated A-module, hence on every complex
with finitely generated cohomology. Over the coefficient DVR, finite modules have
length-one finite projective resolutions; bounded cohomology assembly therefore
makes every source complex perfect. Its completed realization is derived complete
and has uniformly bounded constructible finite reductions, by the completed
constant reduction theorem and the stratified-perfect characterization. Thus the
adjunction restricts to the two stated full subcategories with the same unit.
This asserts only the fully faithful realization; it does not assert the counit
is invertible on arbitrary integral constructible complexes. -/
theorem pointIntegralPerfectRealization
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ∃ L : (DerivedCategory.pointFgComplete
        (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
        (Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer l E)})).FullSubcategory ⥤
        sfIntegralConstructibleCategory l E (Spec (.of D.k)),
      ∃ a : L ⊣ pointIntegralFibre D l hl E, ∀ M, IsIso (a.unit.app M) := by
  sorry

end WeilConjectures
