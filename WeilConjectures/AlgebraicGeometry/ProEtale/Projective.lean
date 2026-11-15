/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.RingTheory.ProEtale.WContractible
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible

/-!
# Projectivity of representables on the pro-étale site

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
`sk-thm-pe-weakly-contractible-basis/det-pe-wcb-projective.md`, node
`lemma-w-contractible-affines-projective` (blueprint: lemma-w-contractible-affines-projective).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- If `D` is w-contractible and `Spec D → X` is weakly étale, the represented sheaf
is projective and sections over it preserve epimorphisms.

Source: blueprint `lemma-w-contractible-affines-projective`, parts 1--2; Stacks Project, Tags 00WN
and 098F (blueprint: lemma-w-contractible-affines-projective).

Proof:
1. By proposition-topos-functoriality--1, the representable is a sheaf. Apply
   lemma-w-contractible-affines-projective to an epimorphism onto it
   and the identity section. Obtain a covering and local sections lifting its arrows.
2. By lemma-w-contractible-affines-projective, refine this covering by a finite disjoint clopen
   partition. Restrict each local lift to its partition piece; naturality says its
   image is the inclusion of that piece.
3. The partition is a pro-étale covering by definition-small-pro-etale-site. The empty covering
   makes every sheaf's value on the empty scheme a singleton. Thus the restricted
   lifts agree on the disjoint intersections and glue by the sheaf equalizer axiom
   of lemma-w-contractible-affines-projective. Separatedness of the representable identifies
   the image of the glued section with the identity. This includes the empty partition.
4. By lemma-w-contractible-affines-projective, the glued section defines a map from the
   representable to the source sheaf. Naturality makes its composite the identity,
   proving the first clause.
5. Given an epimorphism `α : F ⟶ G` and `y ∈ G(U)`, Yoneda gives a map `h_U ⟶ G`.
   Form its pullback with `α`: its sections over `V` are pairs `(x,t)` satisfying
   `α(x) = G(t)(y)`. The sheaf axiom glues both coordinates and separatedness of `G`
   preserves this equality. Local surjectivity of `α` makes the pullback projection
   locally surjective, hence epi by lemma-w-contractible-affines-projective.
6. The first clause splits this projection. Evaluate the splitting at the identity
   and project to `F(U)` to obtain a preimage of `y`. Yoneda identifies this
   surjectivity with projectivity, proving the second clause.
-/
theorem proetale_wContractible_projective
    (X : Scheme.{u}) (D : Type u) [CommRing D] [IsWContractibleRing D]
    (f : Spec (.of D) ⟶ X) [WeaklyEtale f] :
    (∀ (F : Sheaf (ProEt.topology X) (Type (u + 1)))
        (φ : F ⟶ ((ProEt.topology X).uliftYoneda.{u + 1}.obj (ProEt.mk f))) [Epi φ],
      ∃ s : ((ProEt.topology X).uliftYoneda.{u + 1}.obj (ProEt.mk f)) ⟶ F,
        s ≫ φ = 𝟙 _) ∧
      (∀ (F G : Sheaf (ProEt.topology X) (Type (u + 1)))
        (φ : F ⟶ G) [Epi φ],
        Function.Surjective
          (((sheafToPresheaf (ProEt.topology X) (Type (u + 1))).map φ).app
            (op (ProEt.mk f)))) := by
  have hU : (ProEt.topology X).IsWeaklyContractible.{u + 1} (ProEt.mk f) :=
    ProEt.isWeaklyContractible_of_iso (R := CommRingCat.of D) (Iso.refl _)
  have hsurj (F G : Sheaf (ProEt.topology X) (Type (u + 1)))
      (φ : F ⟶ G) [Epi φ] : Function.Surjective (φ.hom.app (op (ProEt.mk f))) :=
    hU φ ((Sheaf.isLocallySurjective_iff_epi φ).mpr inferInstance)
  refine ⟨?_, hsurj⟩
  intro F φ _
  obtain ⟨x, hx⟩ := hsurj F _ φ ⟨𝟙 (ProEt.mk f)⟩
  refine ⟨(ProEt.topology X).uliftYonedaEquiv.symm x, ?_⟩
  apply (ProEt.topology X).uliftYonedaEquiv.injective
  rw [GrothendieckTopology.uliftYonedaEquiv_comp, Equiv.apply_symm_apply]
  exact hx

end AlgebraicGeometry.Scheme
