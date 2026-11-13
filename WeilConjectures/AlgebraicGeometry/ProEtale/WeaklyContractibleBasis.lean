/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import WeilConjectures.RingTheory.ProEtale.WContractible
import WeilConjectures.AlgebraicGeometry.ProEtale.Projective
import WeilConjectures.AlgebraicGeometry.WContractibleAffineCover
public import Mathlib.CategoryTheory.Sites.Subcanonical

/-!
# Enough affine weakly contractible objects

Source: the Weil conjectures blueprint, main-20261015, sec-proetale-coefficients,
`sk-thm-pe-weakly-contractible-basis`; Stacks Project, Tag 098F
(blueprint: sk-thm-pe-weakly-contractible-basis).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.ProEt

/-- Every object of the small pro-etale site has a covering by spectra of w-contractible
rings. For every such affine object, epimorphisms onto its represented sheaf split,
and that represented sheaf is projective. The splitting clause is the representable
form of `GrothendieckTopology.IsWeaklyContractible` on this subcanonical site.

Stacks Project, Tag 098F
(blueprint: sk-thm-pe-weakly-contractible-basis).

Proof:
1. Apply `det-pe-wcb-cover` to each object of `X.ProEt`. Forget the additional
   factorization through an affine open, retaining the covering family and the
   identification of each member with the spectrum of a w-contractible ring.
2. For any w-contractible ring `D` and weakly etale `Spec D → X`, apply
   `det-pe-wcb-projective`. Its first clause splits every epimorphism onto the
   represented sheaf. Its second clause says evaluation over this affine object
   sends every epimorphism to a surjection. Yoneda identifies maps from the
   represented sheaf with sections; a preimage under that surjection is exactly
   the lift required by `Projective.factors`. Thus the represented sheaf is
   projective. Both clauses hold for every such affine, not just chosen cover members.
-/
theorem weaklyContractible_basis (X : Scheme.{u}) :
    (∀ U : X.ProEt,
      ∃ (I : Type u) (W : I → X.ProEt) (f : ∀ i : I, W i ⟶ U),
        Presieve.ofArrows W f ∈ precoverage X U ∧
        ∀ i : I, ∃ D : CommRingCat.{u},
          IsWContractibleRing D ∧ Nonempty (Spec D ≅ (W i).left)) ∧
    (∀ (D : Type u) [CommRing D] [IsWContractibleRing D]
      (f : Spec (.of D) ⟶ X) [WeaklyEtale f],
      (∀ (F : Sheaf (topology X) (Type (u + 1)))
        (φ : F ⟶ (topology X).uliftYoneda.{u + 1}.obj (ProEt.mk f)) [Epi φ],
        ∃ s : (topology X).uliftYoneda.{u + 1}.obj (ProEt.mk f) ⟶ F,
          s ≫ φ = 𝟙 _) ∧
      Projective ((topology X).uliftYoneda.{u + 1}.obj (ProEt.mk f))) := by
  constructor
  · intro U
    obtain ⟨I, W, f, hcover, hW⟩ := exists_wContractible_affine_cover X U
    refine ⟨I, W, f, hcover, ?_⟩
    intro i
    obtain ⟨D, hD, e, _⟩ := hW i
    exact ⟨D, hD, ⟨e⟩⟩
  · intro D _ _ f _
    obtain ⟨hsplit, hsurj⟩ := proetale_wContractible_projective X D f
    refine ⟨hsplit, ⟨?_⟩⟩
    intro F G g φ _
    obtain ⟨x, hx⟩ := hsurj F G φ ((topology X).uliftYonedaEquiv g)
    refine ⟨(topology X).uliftYonedaEquiv.symm x, ?_⟩
    apply (topology X).uliftYonedaEquiv.injective
    rw [GrothendieckTopology.uliftYonedaEquiv_comp, Equiv.apply_symm_apply]
    exact hx

end AlgebraicGeometry.Scheme.ProEt
