/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.AlgebraicGeometry.ConstructibleHigherDirectImages
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

import WeilConjectures.SixFunctors.Finite.Stalk
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence
import Sheaf.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Sheaf.CategoryTheory.CartanEilenbergExists
import Sheaf.CategoryTheory.HypercohomologyFirstPage
import Sheaf.CategoryTheory.ExactCoupleConvergence
import Sheaf.AlgebraicGeometry.FiniteConstructibleDirectImage
import WeilConjectures.CategoryTheory.ExactCoupleConvergence
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.LeraySpectralSequence

/-!
# Constructibility descends through a finite surjection

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/
`lem-finrepair-finite-surjection-cancellation.md`, order 1598
(blueprint: lem-finrepair-finite-surjection-cancellation).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Constructibility of higher direct images descends through a finite surjection.
Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/`,
`lem-finrepair-finite-surjection-cancellation.md`, statement and proof
(blueprint: lem-finrepair-finite-surjection-cancellation).

Proof plan:
1. For any module sheaf `Q`, the unit `Q → π_*π^*Q` is monic. On geometric stalks,
   `lemma-weil-pbc-finite-stalk-formula` and `lem-weil-pbc-inverse-image-stalk-germ`
   identify it with the diagonal into a nonempty finite product. Surjectivity supplies
   a lift of each geometric point. Exactness and conservativity of geometric stalks
   (`prop-weil-pbc-geometric-stalks-exact`, `lemma-weil-pbc-geometric-stalk-conservative`)
   detect the zero kernel, also in modules because kernels are computed sectionwise.
2. The finite map makes `Y` finite type over `k`. Starting with a constructible `F`,
   set `Q₀ = F`, `Gᵃ = π_*π^*Qₐ` and `Qₐ₊₁ = coker(Qₐ → Gᵃ)`. Constructible pullback,
   `lem-fin-finite-morphism`, and `thm-constructible-serre` keep all terms constructible.
   Quotient followed by the next unit defines an exact augmented resolution of `F`.
3. The composition spectral sequence (`lem-weil-pbc-grothendieck-spectral-sequence`)
   collapses because `lem-fin-finite-morphism` kills the positive higher direct images
   of the constructible sheaves `π^*Qₐ`. Hence `Rᵇf_*Gᵃ ≅ Rᵇ(fπ)_*π^*Qₐ`.
4. The Grothendieck abelian and enough-injectives nodes for module sheaves permit
   `lem-sp-cartan-eilenberg-exists` and `thm-sp-if-e1` to give the first-quadrant
   spectral sequence `E₁ᵃᵇ = Rᵇf_*Gᵃ` abutting to `Rᵃ⁺ᵇf_*F`.
5. The hypothesis `C(fπ)` makes every first-page term constructible.
6. By `thm-constructible-serre`, kernels, images and cokernels keep every later page
   constructible. At `(a,b)`, all differentials vanish for `r > max(a,b+1)`.
   Convergence (`def-sp-convergence`) gives, in each total degree, a finite filtration
   with constructible stable terms. Extension closure proves constructibility of
   the abutment. There is no uniform vanishing assertion. -/
theorem hasConstructibleHigherDirectImages_of_finite_surjective
    (k : Type u) [Field k] (N : ℕ) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X S Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [S.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (hX : IsSmoothBaseChangeCoefficients N Λ X)
    (hS : IsSmoothBaseChangeCoefficients N Λ S)
    (hY : IsSmoothBaseChangeCoefficients N Λ Y)
    (f : X ⟶ S) (π : Y ⟶ X) [IsFinite π] [Surjective π]
    (h : HasConstructibleHigherDirectImages k N Λ hY hS (π ≫ f)) :
    HasConstructibleHigherDirectImages k N Λ hX hS f := by
  sorry

end AlgebraicGeometry.Etale
