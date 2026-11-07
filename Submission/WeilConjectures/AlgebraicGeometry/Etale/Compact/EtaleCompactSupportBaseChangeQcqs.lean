/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.Compactification.BaseChange
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

import Submission.WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import Submission.WeilConjectures.AlgebraicGeometry.Derived.DerivedExtensionZeroBaseChangeSupplement

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Arbitrary base change for compact support on qcqs etale sites

Source: Stacks Project, `more-etale.tex`, Tag 0F7L,
`lemma-base-change-shriek`, first proof paragraph
(blueprint: lem-weil-pbc-etale-compact-support-base-change-qcqs).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- For finite constant coefficients, compact support computed with a fixed compactification
commutes with arbitrary change of qcqs base, naturally in the bounded below complex.
Source: Stacks Project, Tag 0F7L, `lemma-base-change-shriek`, first proof paragraph
(blueprint: lem-weil-pbc-etale-compact-support-base-change-qcqs).

Proof:
1. Base change the compactification using the universal property of the fibre product
   (def-pc-fibre-product). Open immersions, properness and quasi-compactness survive base
   change (def-weil-open-immersion, lem-weil-pbc-proper-fp-permanence,
   lem-weil-pbc-qcqs-morphism-permanence). The new source is qcqs and the new structure
   morphism is separated of finite type (lem-pod-separated-finite-type-base-change).
2. Finiteness of the coefficient ring gives a positive integer annihilating every module.
   Extension by zero and inverse image are exact, so commute with cohomology and preserve
   boundedness below (lem-weil-pbc-extension-by-zero-exact,
   lem-sp-exact-functor-preserves-homology, prop-weil-pbc-inverse-image-modules-exact).
3. Apply thm-weil-pbc-bounded-below to the proper square for `c.g` and the torsion complex
   `c.i_! K`. By lem-weil-pbc-exchange-forget-coefficients, forgetting coefficients
   identifies the module exchange with the abelian exchange and detects invertibility.
   The mate construction of def-weil-pbc-derived-exchange makes this natural in `K`.
4. Apply cor-cbc-derived-extension-zero-base-change to the open immersion square to
   identify the pullback of `c.i_! K` with extension by zero of the pullback of `K`, then
   apply the derived proper pushforward to this natural isomorphism.
5. Compose the two natural isomorphisms and use the definition
   def-weil-pbc-projection-compactification, `Rf_!^c = R(c.g)_* c.i_!`.
-/
theorem etale_compactSupport_baseChange_qcqs
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Y' : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace Y'] [QuasiSeparatedSpace Y']
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (g : Y' ⟶ Y) (c : Compactification f) :
    Nonempty
      (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c ⋙
          (upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlus ≅
        (upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f g)).mapDerivedCategoryPlus ⋙
          rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ)
            (c.baseChange g)) := by
  let sq : IsPullback (pullback.fst f g) (pullback.snd f g) f g :=
    IsPullback.of_hasPullback f g
  have : IsIso (baseChange (ModuleCat.{u + 1} Λ)
      (c.isPullback_g_ofIsPullback sq).flip.toCommSq) :=
    isIso_baseChange_of_isProper_of_isAddTorsion_ring Λ isAddTorsion_of_finite
      (c.isPullback_g_ofIsPullback sq).flip
  let e := asIso (baseChange (ModuleCat.{u + 1} Λ)
    (c.isPullback_g_ofIsPullback sq).flip.toCommSq)
  exact ⟨Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ e ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (extensionZeroBaseChangeDerivedPlusIso Λ (c.isPullback_i_ofIsPullback sq)) _ ≪≫
    Functor.associator _ _ _⟩

end AlgebraicGeometry.Etale
