/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q59
-/
module

public import Sheaf.AlgebraicGeometry.AdequateModuliSpace
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.AlgebraicGeometry.SchemeStackDiagonalPresentation
public import Sheaf.AlgebraicGeometry.FiniteStackSchemeTests
public import Sheaf.AlgebraicGeometry.ModuliInertia
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Scheme

/-! # Finite diagonal from an affine adequate moduli space

Source: Alper, arXiv:1005.2398v3, Theorem 8.3.2, implication (3) to (1),
printed pp. 39--40, and Lemma 8.3.1
(blueprint: lem-sfb-adequate-quasifinite-diagonal-finite).

The quasi-finite separated diagonal is tested on its actual scheme presentations.
Finite type of the stack uses a smooth surjective atlas of finite type over the field,
without requiring the stack to be smooth or Deligne--Mumford.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- An affine adequate moduli space and a quasi-finite separated diagonal imply
finite diagonal and finite inertia. The scheme diagonal tests include finite type,
finite geometric fibres, and a closed relative diagonal; they allow nonreduced fibres.
Source: Alper, arXiv:1005.2398v3, Theorem 8.3.2 (3) implies (1), pp. 39--40,
and Lemma 8.3.1 (blueprint: lem-sfb-adequate-quasifinite-diagonal-finite).
Proof:
1. Set V = X ×_k X and B = Γ(V,O). By lem-sfb-adequate-product-affinization,
   the canonical map ψ : V → Spec B is an adequate moduli space.
2. Put A = Γ(Y,O). Adequacy identifies A with Γ(X,O). The diagonal pullback
   gives r : B → A with section s = pr₁* φ*, since pr₁ Δ = id. Thus r is surjective
   and integral: a satisfies T - s(a). By def-weil-finite-integral-morphism and
   def-weil-affine-spectrum, g = Spec r : Y → Spec B is integral and ψ Δ = g φ;
   the equality follows on smooth affine charts by equality of their ring maps.
3. By lem-sfb-stack-diagonal-closed-points, Δ sends closed points to closed points.
4. Apply lem-sfb-adequate-integral-comparison-finite to this square. Both vertical
   maps are adequate, g is integral, and Δ is representable, quasi-finite, separated
   and preserves closed points. The product stack is finite type by the product
   of finite-type smooth atlases. Thus Δ is finite.
5. The inertia projection is the base change of Δ along Δ. Every scheme test
   T → X gives I_X ×_X T ≃ T ×_(X×_k X) X over T. Finiteness is stable under
   this scheme base change, giving IsRepresentableFiniteModuliMap for the existing
   inertia projection, whose objects are vertical automorphisms. -/
theorem adequate_quasifinite_diagonal_finite
    (k : Type u) [Field k]
    (F : BasedCategory.{v, w} (Over (Spec (CommRingCat.of k))))
    (hF : IsAlgebraicModuliStack F)
    (hft : ∃ (U : Over (Spec (CommRingCat.of k)))
      (a : BasedFunctor (discreteModuli (yoneda.obj U)) F),
      IsSmoothModuliAtlas F U a ∧ LocallyOfFiniteType U.hom ∧ QuasiCompact U.hom)
    (Y : Over (Spec (CommRingCat.of k))) [IsAffine Y.left]
    (φ : BasedFunctor F (discreteModuli (yoneda.obj Y)))
    (hφ : IsAdequateModuliSpace F hF (AlgebraicSpace.schemeSpace Y) φ)
    (hΔ : HasSchemeStackDiagonalWith
      (fun _ V f ↦ LocallyOfFiniteType f ∧ QuasiCompact f ∧
        (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (CommRingCat.of Ω) ⟶ V),
          Finite ↥(pullback f y)) ∧ IsClosedImmersion (pullback.diagonal f)) F) :
    HasFiniteModuliDiagonal F ∧
      IsRepresentableFiniteModuliMap (moduliInertiaProjection F) := by
  sorry

end CategoryTheory
