/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.AlgebraicGeometry.SpaceProperQuotFunctor
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperCoefficient
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests

/-! # The affine relative module Isom space

Source: Stacks Project, quot.tex, Tag 08K9, proposition-isom, in Situation 08JT
(blueprint: lem-sfb-space-module-isom-affine).

The representing equivalences use all scheme tests over the base algebraic space.
Their naturality uses the specified tensor pullback and its canonical source comparisons.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The Isom functor of two finitely presented relatively flat quasi-coherent modules
with proper support is represented by an affine algebraic space of finite presentation.
The support hypotheses specify a finite type quasi-coherent module on a proper closed
carrier, rather than an extra condition on the morphism f itself.

Source: Stacks Project, Tag 08K9, proposition-isom, with Situation 08JT
(blueprint: lem-sfb-space-module-isom-affine).

Proof:
1. Apply lem-sfb-space-module-hom-affine to (M,N), (N,M), (M,M), and (N,N).
   Every source is finitely presented and every target is finitely presented, relatively
   flat and properly supported. This gives affine finitely presented spaces H, H', E, E'.
2. Form P = H' ×_B H and Q = E ×_B E' using
   lem-trf-space-fibre-products-etale-covers. The projections, and hence their composites
   to B, are affine and finitely presented by lem-sfb-space-affine-locality,
   lem-sfb-space-flat-proper-fp-locality and lem-sfb-space-separated-fp-composition.
3. Send (v,u) to (v composed with u, u composed with v), and let sigma be the identity
   section of Q over B. The component order puts the first endomorphism on M and the
   second on N. Functoriality and def-sfb-space-module-tensor-composition make these
   formulas natural for all test schemes, so they define space morphisms.
4. The section sigma is a base change of the diagonal of Q over B: the pullback along
   (a, sigma q a) identifies with B ×_Q T since q sigma is identity. Thus sigma is a
   closed immersion because Q over B is separated; it is affine, quasi-compact and
   quasi-separated by lem-sfb-space-affine-locality and def-weil-closed-immersion.
   Apply lem-sfb-space-relative-lfp-permanence to sigma followed by q. Their composite
   is identity and hence locally finitely presented: compatible scheme charts are etale
   by lem-trf-space-representable-etale-scheme-tests and def-weil-etale-morphism.
   Hence sigma is locally finitely presented, and therefore finitely presented.
5. Let I = P ×_Q B. Its map to P is a base change of sigma, so I over B is affine and
   finitely presented by the same base-change and composition permanence results.
6. The pullback universal property identifies I(T) with pairs (v,u) satisfying vu = 1
   and uv = 1. Send a pair to u, and an isomorphism u to (u inverse,u). Inverses are
   unique since v = v(uw) = (vu)w = w. These are inverse bijections. Tensor pullback
   preserves composition and identity, hence inverses. Conjugation by the specified
   properQuotSourceIso gives precisely the displayed naturality identity. -/
theorem module_isom_affine {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (hf : ProperQuotFinitePresentation f) (M N : X.QCoh)
    (hMfp : M.obj.IsFinitePresentation) (hNfp : N.obj.IsFinitePresentation)
    (hMflat : ModuleIsFlatOver f M.obj) (hNflat : ModuleIsFlatOver f N.obj)
    (hMsupport : ∃ (Z : AlgebraicSpace S) (i : Z ⟶ X),
      IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom ∧
      MapIsProper (i ≫ f) ∧ ∃ E : Z.Modules,
        E.IsQuasicoherent ∧ E.IsFiniteType ∧ Nonempty ((moduleDirectImage i).obj E ≅ M.obj))
    (hNsupport : ∃ (Z : AlgebraicSpace S) (i : Z ⟶ X),
      IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom ∧
      MapIsProper (i ≫ f) ∧ ∃ E : Z.Modules,
        E.IsQuasicoherent ∧ E.IsFiniteType ∧ Nonempty ((moduleDirectImage i).obj E ≅ N.obj)) :
    ∃ (I : AlgebraicSpace S) (p : I ⟶ B),
      IsRepresentableWith (fun _ _ q ↦ IsAffineHom q.left) p.hom.hom ∧
      ProperQuotFinitePresentation p ∧
      ∃ e : ∀ T : ProperQuotTest B,
        {g : yoneda.obj T.left ⟶ I.obj.obj // g ≫ p.hom.hom = T.hom} ≃
          ((moduleTensorPullback (properQuotFst f T)).obj M.obj ≅
            (moduleTensorPullback (properQuotFst f T)).obj N.obj),
        ∀ (T' T : ProperQuotTest B) (h : T' ⟶ T)
          (g : {g : yoneda.obj T.left ⟶ I.obj.obj // g ≫ p.hom.hom = T.hom})
          (g' : {g : yoneda.obj T'.left ⟶ I.obj.obj // g ≫ p.hom.hom = T'.hom}),
          g'.val = yoneda.map h.left ≫ g.val →
          e T' g' = (properQuotSourceIso f M.obj h).symm ≪≫
            (moduleTensorPullback (properQuotFibreMap f h)).mapIso (e T g) ≪≫
            properQuotSourceIso f N.obj h := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
