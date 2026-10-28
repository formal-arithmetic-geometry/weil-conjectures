/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.CoefScalarReductionExchange

/-! # Realization of a coefficient restriction square

Source: lem-coef-integral-finite-extension, quotient compatibility, and
lem-coef-finite-dualizing, normalized comparison-site realization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralFiniteExtension
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (X : Scheme.{u})

/-- The comparison-site realization preserves the square of coefficient restrictions.
This is a statement for an arbitrary finite-coefficient object, without any
exceptional functor, dualizing term, counit comparison or scalar-extension mate.

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-tower/
lem-coef-integral-finite-extension.proof.md, quotient compatibility, paragraphs 2--3;
lem-coef-finite-dualizing.proof.md, final realization sentence.
(blueprint: lem-sf-finite-realization-restriction-square)

Proof: the two coefficient maps in hq agree on residue representatives. Before
localization, restriction precomposes the scalar action and leaves sections
unchanged. The four intrinsic restriction comparisons and the two ordinary
comparison-site restriction comparisons are normalized by this identity on
sections. Pasting around either side therefore gives the same ordinary square,
with restriction composition accounting for the two factorizations of the ring
map. Apply the exact derived localization functors; their composition comparisons
are precisely derivedRestrictScalarsCompIso. Whisker the intrinsic and
comparison-site squares and use associator naturality. The resulting outer
boundary is the displayed equation. The definition of scalarRestrictionSquare
uses these same derived restriction compositors and the equalities
scalarQuotient_restrict, so it has the required normalization. This works for
arbitrary K, repeated levels and identity field maps; no coefficient map is
assumed flat and no exceptional adjunction is invoked. -/
theorem finiteRealization_restriction_square {m n : ℕ} (h : n ≤ m)
    (hq : (finiteDualizingQuotient l L h).comp
        (RingHom.ulift.{u + 1, u + 1} (integralScalarQuotientMap l E L ι m)) =
      (RingHom.ulift.{u + 1, u + 1} (integralScalarQuotientMap l E L ι n)).comp
        (finiteDualizingQuotient l E h))
    (K : Etale.DerivedCategoryModule (finiteDualizingCoeff l L n) X) :
    (finiteDualizingRealization l E X m).map
        (((Sheaf.derivedRestrictScalarsCompIso X.smallEtaleTopology hq).hom ≫
          (Sheaf.derivedRestrictScalarsCompIso X.smallEtaleTopology
            (rfl : (finiteDualizingQuotient l L h).comp
                (RingHom.ulift.{u + 1, u + 1} (integralScalarQuotientMap l E L ι m)) =
              (finiteDualizingQuotient l L h).comp
                (RingHom.ulift.{u + 1, u + 1}
                  (integralScalarQuotientMap l E L ι m)))).inv).app K) ≫
      (finiteRealizationRestriction l E L ι X m).inv.app
        ((Sheaf.derivedRestrictScalars X.smallEtaleTopology
          (finiteDualizingQuotient l L h)).obj K) ≫
      (pbcDerivedRestrict (integralScalarQuotientSheafMap l E L ι X m)).map
        ((finiteDualizingRealizationRestriction l L X h).inv.app K) =
    (finiteDualizingRealizationRestriction l E X h).inv.app
        ((Sheaf.derivedRestrictScalars X.smallEtaleTopology
          (RingHom.ulift.{u + 1, u + 1} (integralScalarQuotientMap l E L ι n))).obj K) ≫
      (normalizedDVRRes l E X h).map
        ((finiteRealizationRestriction l E L ι X n).inv.app K) ≫
      (scalarRestrictionSquare l E L ι X h).hom.app
        ((finiteDualizingRealization l L X n).obj K) := by sorry

end WeilConjectures.IntegralFiniteExtension
