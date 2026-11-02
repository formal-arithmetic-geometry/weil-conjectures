/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SupportedHomAdjunctionClass
import WeilConjectures.AlgebraicGeometry.SupportedHomPairAdjunctionComparison

/-! # Cocycle normalization of the derived adjunction class

Source: latest blueprint, `lem-pur-supported-hom.proof.md`, derived closed adjunction
(blueprint: lem-pur-supported-hom-pair-adjunction-normalization).
-/

@[expose] public section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Any cocycle-normalized supported-Hom identification sends the actual derived
supported-adjunction class of f to f. The supported object is the recorded direct image
of P.constant, rather than an implicitly substituted constant model.
Source: Milne, Etale Cohomology, Theorem 9.4 and Example 9.5; the supported-Hom
identification in `lem-pur-gysin-structure.proof.md`
(blueprint: lem-pur-supported-hom-pair-adjunction-normalization).

Proof:
1. Apply supportedHom_adjunction_transpose to the ordinary supported coefficient
   adjunction. Its cocycle formula fixes the Hom comparison uniquely on injective
   complexes: every supported cohomology class lifts through the homology projection
   to a cycle, and the ordinary evaluation isomorphism gives its unique Hom cocycle.
2. Transport the coefficient object along lowerStar.mapIso(comparisonUpperStarUnitIso).
   The constant restriction of proEtaleSupportHomPair already contains the inverse
   of this comparison. Their composite cancels, so its evaluation is exactly the
   coefficient-quotient normalization of the supported adjunction.
3. The D+/unbounded right-derived compatibility is normalized by its derived-unit
   equation. Hence it takes the bounded-below cycle class to supportedHomCycleClass,
   with no extra scalar or sign. Naturality and an injective representative extend
   the equality of the two normalized Hom comparisons to every K.
4. Apply the transpose formula to supportedHomAdjunctionMorph of the source-transported
   f. The proved supportedHomAdjunctionMorph_transpose identity cancels the adjunction,
   the chosen inverse shift map, and the source comparison. Transport back along the
   coefficient isomorphism; its hom and inverse cancel, leaving f.
   This works in every integer degree, for zero maps, and for the empty support. -/
theorem supportedHomPairAdjunctionClass_normalization
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X]
    (chi : (proEtaleSupportHomPair P i).Identification)
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))) (a : ℤ)
    (f : (proEtaleSupportHomPair P i).derivedHom K a) :
    chi.chi K a (supportedHomPairAdjunctionClass P i K a f) = f := by
  obtain ⟨χ, hχ, ht⟩ := ProEtale.supportedHom_adjunction_transpose P i a
  rw [supportedHomPairAdjunctionComparison P i a χ hχ chi K]
  dsimp only [supportedHomPairAdjunctionClass]
  rw [← ModuleCat.comp_apply, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, ModuleCat.id_apply, ht,
    ProEtale.supportedHomAdjunctionMorph_transpose]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

end AlgebraicGeometry
