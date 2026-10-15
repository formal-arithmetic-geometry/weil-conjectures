/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Hypercover.Zero
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Sheaf.CategoryTheory.Sites.SheafificationPlusTheorem
public import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.RegularEpi
import Mathlib.CategoryTheory.Limits.Shapes.KernelPair

/-!
# A coequalizer presentation using covering representables

Source: Stacks Project, Sites, Tag 00WS, lemma-sheaf-coequalizer-representable.
(blueprint: lem-weil-pbc-sheaf-covering-representable-coequalizer-presentation)
-/

@[expose] public section

universe u w

open CategoryTheory.Limits

namespace CategoryTheory

/-- Every set sheaf is a coequalizer of two coproducts of sheafified representables from
any covering set of site objects. The two `IsColimit (Cofan.mk ...)` assertions mean that
`P₀` and `P₁` are those coproducts; the final `IsColimit` is the coequalizer universal
property: for each sheaf `K`, composition with `q` bijects maps `H ⟶ K` with maps
`a : P₀ ⟶ K` satisfying `d₀ ≫ a = d₁ ≫ a`.
The `uliftYoneda` is just the representable presheaf with its Hom sets raised to the
universe of the sheaf values, with restriction by precomposition.

Source: Stacks Project, Sites, Tag 00WS, lemma-sheaf-coequalizer-representable.
(blueprint: lem-weil-pbc-sheaf-covering-representable-coequalizer-presentation)

Proof:
1. Sheafification and Yoneda identify maps from the sheafification of `h_V` to a sheaf
   `T` with elements of `T(V)`, sending the identity section to the chosen element.
   Use lem-weil-pbc-sheafification-plus-theorem, def-weil-pbc-sheafification and
   lem-galois-yoneda-hom-bijection. No subcanonicity assumption is needed.
2. For `T`, index by pairs `(V,t)` with `V ∈ E` and `t ∈ T(V)`. Sheafify the presheaf
   disjoint union of these representables. Maps out of the disjoint union are precisely
   families of maps out of its summands; the sheafification adjunction gives the same
   universal property after sheafification, proving the coproduct assertion, even for
   an empty index set. The maps of step 1 induce `q_T : P(T) ⟶ T`, taking `(V,t,f)` to
   `T(f)(t)`. Use def-weil-pbc-category-colimit and the sheafification inputs of step 1.
3. Given `s ∈ T(W)`, take a covering of `W` by objects `V_i ∈ E`. Its restriction to
   `V_i` lifts via the identity in the summand `(V_i,T(f_i)(s))`. Thus `q_T` is locally
   surjective and hence epi by lem-weil-pbc-site-sheaf-sets-epi-locally-surjective.
4. Set `P₀ = P(H)` and `q = q_H`. Form the sectionwise kernel pair `G` of `q`, with
   projections `r,s`, using lem-weil-pbc-site-sheaf-sets-limits-sectionwise. Apply the
   same construction to `G`, obtaining `P₁ = P(G)` and an epi `e : P₁ ⟶ G`. Set
   `d₀ = e ≫ r`, `d₁ = e ≫ s`; the kernel-pair equation gives `d₀ ≫ q = d₁ ≫ q`.
5. By lem-weil-pbc-site-sheaf-sets-epi-kernel-pair-coequalizer, the epi `q` is the
   coequalizer of `r,s`.
6. If `a` equalizes `d₀,d₁`, cancel the epi `e` to see that it equalizes `r,s`.
   Step 5 gives a unique factorization through `q`. Conversely, composition with `q`
   always equalizes `d₀,d₁`. This is exactly the required coequalizer property. -/
theorem exists_coveringRepresentable_coequalizer
    {C : Type u} [SmallCategory C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (E : Set C)
    (hE : ∀ U : C, ∃ R : Precoverage.ZeroHypercover.{max u w} J U,
      ∀ i : R.I₀, R.X i ∈ E)
    (H : Sheaf J.toGrothendieck (Type (max u w))) :
    ∃ (I₀ I₁ : Type (max u w)) (V₀ : I₀ → E) (V₁ : I₁ → E)
      (P₀ P₁ : Sheaf J.toGrothendieck (Type (max u w)))
      (ι₀ : ∀ j : I₀, (presheafToSheaf J.toGrothendieck (Type (max u w))).obj
        (uliftYoneda.{w}.obj (V₀ j).val) ⟶ P₀)
      (ι₁ : ∀ j : I₁, (presheafToSheaf J.toGrothendieck (Type (max u w))).obj
        (uliftYoneda.{w}.obj (V₁ j).val) ⟶ P₁),
      Nonempty (IsColimit (Cofan.mk P₀ ι₀)) ∧
      Nonempty (IsColimit (Cofan.mk P₁ ι₁)) ∧
      ∃ (d₀ d₁ : P₁ ⟶ P₀) (q : P₀ ⟶ H) (hq : d₀ ≫ q = d₁ ≫ q),
        Nonempty (IsColimit (Cofork.ofπ q hq)) := by
  sorry

end CategoryTheory
