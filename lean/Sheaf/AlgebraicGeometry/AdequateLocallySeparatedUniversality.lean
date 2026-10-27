/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.AlgebraicGeometry.AdequateModuliSpace
public import Sheaf.AlgebraicGeometry.RelativeModuliInertia
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # Adequate moduli spaces and schemes or separated spaces

Source: Alper, Adequate moduli spaces and geometrically reductive group schemes,
arXiv:1005.2398v3, §2 and Theorem 7.2.1, through Proposition 7.1.1
(blueprint: lem-sfb-adequate-locally-separated-universality).

The source's quasi-compact separated diagonal convention is explicit. The conclusion
uses unique factorization up to a 2-isomorphism, equivalently bijectivity on morphism
classes. No separation assumption is placed on the scheme targets.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

namespace CategoryTheory

/-- An adequate moduli map is universal for scheme targets and algebraic-space targets
with closed diagonal. The absolute diagonal of the source is tested by its actual
algebraic-space 2-base changes. For the space Y, its diagonal is a monomorphism and
hence separated automatically; only its quasi-compactness needs to be assumed.
Source: Alper, arXiv:1005.2398v3, §2, Proposition 7.1.1 and Theorem 7.2.1
(blueprint: lem-sfb-adequate-locally-separated-universality).
Proof:
1. By lem-sfb-adequate-geometric-fibres-submersion, the adequate map is universally
   submersive and identifies geometric objects exactly when their closures intersect.
   Its qcqs and structure-sheaf conditions are part of def-sfb-adequate-moduli-space.
   These give the hypotheses of lem-sfb-stein-submersive-reduced-descent.
2. Given h into a locally separated space, apply
   lem-sfb-locally-separated-closure-equivalent-images to the two projections from
   R = (X ×_Y X)_red. Their h-images agree at every algebraically closed point.
3. Pull back the immersive diagonal of the target along the pair of h-images.
   The resulting immersion W → R is surjective on geometric points. On reduced
   smooth scheme charts it is an isomorphism: locally its closed-immersion ideal
   lies in every prime, hence consists of nilpotents, hence vanishes. Thus W = R
   and the two projections have the same composite with h.
4. Apply lem-sfb-stein-submersive-reduced-descent to obtain the factorization
   through Y; its injectivity makes the factorization unique.
5. Every scheme has immersive diagonal by lem-weil-pbc-diagonal-immersion
   (Mathlib's IsImmersion.instDiagonalScheme, Stacks 01KJ). A closed diagonal
   is immersive by its closed/open factorization with the whole target open.
   Thus step 4 applies to each of the two stated target cases. All maps are
   over Spec k; Nonempty ModuliTwoIso expresses equality of their morphism classes. -/
theorem adequateModuliSpace_universal_schemes_separatedSpaces
    {k : Type u} [Field k]
    (F : BasedCategory.{v, w} (Over (Spec (CommRingCat.of k))))
    (hF : IsAlgebraicModuliStack F)
    (Y : AlgebraicSpace (Spec (CommRingCat.of k)))
    (φ : BasedFunctor F (discreteModuli Y.obj.obj))
    (hφ : IsAdequateModuliSpace F hF Y φ)
    (hFdiag : ∀ (T : Over (Spec (CommRingCat.of k)))
      (t : BasedFunctor (discreteModuli (yoneda.obj T))
        (moduliTwoFiberProduct (moduliBaseStructure F) (moduliBaseStructure F))),
      ∃ (Z : AlgebraicSpace (Spec (CommRingCat.of k))) (p : Z.obj.obj ⟶ yoneda.obj T),
        HasSpaceBaseChange (moduliRelativeDiagonal (moduliBaseStructure F)) T t Z p ∧
          MapIsQuasiCompact p ∧ MapToSchemeIsSeparated Z T p)
    (hYdiag : MapIsQuasiCompact (prod.lift (𝟙 Y.obj.obj) (𝟙 Y.obj.obj))) :
    (∀ (T : Over (Spec (CommRingCat.of k)))
      (h : BasedFunctor F (discreteModuli (yoneda.obj T))),
      ∃! g : Y.obj.obj ⟶ yoneda.obj T,
        Nonempty (ModuliTwoIso (φ.comp (discreteModuliMap g)) h)) ∧
    (∀ (T : AlgebraicSpace (Spec (CommRingCat.of k))),
      IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
        (prod.lift (𝟙 T.obj.obj) (𝟙 T.obj.obj)) →
      ∀ (h : BasedFunctor F (discreteModuli T.obj.obj)),
      ∃! g : Y.obj.obj ⟶ T.obj.obj,
        Nonempty (ModuliTwoIso (φ.comp (discreteModuliMap g)) h)) := by
  sorry

end CategoryTheory
