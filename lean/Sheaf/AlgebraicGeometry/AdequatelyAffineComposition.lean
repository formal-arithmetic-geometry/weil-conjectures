/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Sheaf.AlgebraicGeometry.AdequatelyAffineMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Composition and affine examples of adequately affine morphisms

Source: Alper, *Adequate moduli spaces and geometrically reductive group schemes*,
Proposition 4.2.1(1),(2), printed p. 20
(blueprint: lem-sfb-adequately-affine-composition).

The affine hypothesis is expanded on every scheme test. Its scheme presentation
is an equivalence over the base whose projection agrees, up to a specified
2-isomorphism, with an affine scheme morphism. No atlas is chosen globally.

## Main statements

- `CategoryTheory.adequatelyAffine_comp`: adequately affine morphisms compose.
- `CategoryTheory.adequatelyAffine_of_affine`: affine morphisms are adequately affine.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂ v₃ w₃

open AlgebraicGeometry

namespace CategoryTheory

/-- Adequately affine morphisms of algebraic stacks over a field compose.
Source: Alper, Proposition 4.2.1(1), printed p. 20
(blueprint: lem-sfb-adequately-affine-composition).

Proof: first use `lem-sfb-stack-qcqs-composition-affine` to see that the composite
is quasi-compact and quasi-separated. Given any surjection A → B of quasi-coherent
algebras on U, `lem-sfb-stack-qcqs-algebra-direct-image` supplies the quasi-coherent
algebra direct images C = f_* A and D = f_* B. Adequate affineness of f says that
C → D is universally adequate, although it need not be surjective. Apply
`lem-sfb-adequate-algebra-pushforward` to g and this map to obtain universal adequacy
of g_* C → g_* D. The composition comparison of
`lem-sfb-stack-qcqs-algebra-direct-image`, natural in the algebra and on all smooth
tests, identifies this with (g ∘ f)_* A → (g ∘ f)_* B. This proves the power-lifting
condition for every algebra surjection and hence adequate affineness. -/
theorem adequatelyAffine_comp {k : Type u} [Field k]
    {U : BasedCategory.{v₁, w₁} (Over (Spec (.of k)))}
    {V : BasedCategory.{v₂, w₂} (Over (Spec (.of k)))}
    {W : BasedCategory.{v₃, w₃} (Over (Spec (.of k)))}
    (hU : IsAlgebraicModuliStack U) (hV : IsAlgebraicModuliStack V)
    (hW : IsAlgebraicModuliStack W) (f : BasedFunctor U V) (g : BasedFunctor V W)
    (hf : IsAdequatelyAffineMorphism f hU hV)
    (hg : IsAdequatelyAffineMorphism g hV hW) :
    IsAdequatelyAffineMorphism (f.comp g) hU hW := by
  sorry

/-- An affine morphism of algebraic stacks over a field is adequately affine.
The affine hypothesis says that every scheme 2-base change is represented by a
scheme, with affine projection to the test scheme. `IsAffineHom` means that the
inverse image of every affine open is affine.
Source: Alper, Proposition 4.2.1(2), printed p. 20
(blueprint: lem-sfb-adequately-affine-composition).

Proof: `lem-sfb-stack-qcqs-composition-affine` makes q quasi-compact and
quasi-separated. For any surjection A → B of quasi-coherent algebras,
`lem-sfb-stack-affine-algebra-direct-image` gives a surjection of quasi-coherent
algebra direct images. The smooth-test and surjection comparisons of
`lem-sfb-stack-qcqs-algebra-direct-image` identify their restrictions with q_* A
and q_* B and give local lifts after an étale cover of every smooth test.
Each lift is a positive-power lift with exponent 1. Thus every algebra surjection
has universally adequate direct image, which is the defining condition. -/
theorem adequatelyAffine_of_affine {k : Type u} [Field k]
    {U : BasedCategory.{v₁, w₁} (Over (Spec (.of k)))}
    {V : BasedCategory.{v₂, w₂} (Over (Spec (.of k)))}
    (hU : IsAlgebraicModuliStack U) (hV : IsAlgebraicModuliStack V)
    (q : BasedFunctor U V)
    (hq : ∀ (T : Over (Spec (.of k)))
      (t : BasedFunctor (discreteModuli (yoneda.obj T)) V),
      ∃ (P : Over (Spec (.of k))) (a : P ⟶ T)
        (e : BasedFunctor (discreteModuli (yoneda.obj P)) (moduliTwoFiberProduct t q)),
        e.toFunctor.IsEquivalence ∧
          Nonempty (ModuliTwoIso (e.comp (moduliTwoFiberFst t q))
            (discreteModuliMap (yoneda.map a))) ∧ IsAffineHom a.left) :
    IsAdequatelyAffineMorphism q hU hV := by
  sorry

end CategoryTheory
