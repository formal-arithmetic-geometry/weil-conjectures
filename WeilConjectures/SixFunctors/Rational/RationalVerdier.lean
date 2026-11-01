/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierModels
import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierDatumFromIntegral
import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierExtension
import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierUnit
import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierComposition

/-! # Rational Verdier duality and coherent coefficient extension

Source: blueprint thm-coef-rational-verdier. Assemble the single-field duality,
normalized comparisons and their two coherence equations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- Integral duality induces rational Verdier duality, with canonical evaluation,
biduality, dualizing object and coherent finite coefficient-field comparisons.
Source: Weil blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower,
thm-coef-rational-verdier, proof paragraphs 1--3
(blueprint: thm-coef-rational-verdier).

Proof (the seven DAG steps):
1. lem-coef-integral-residue-tor identifies the whole integral constructible category
with its finite-Tor subcategory. thm-coef-integral-verdier gives exact duality and the
actual invertible delta. prop-coef-integral-dualizing supplies omega. Internal Hom
precomposition is O_E-linear, so duality does not apply a scalar involution.
2. On unchanged objects put D_E K = D_R K and on pure tensors put
D_E(c tensor f) = c tensor D_R(f). Integral linearity preserves balancing;
contravariant composition and identities extend to sums. This also identifies the
localization of the opposite category with the opposite raw localization.
3. Every rational distinguished triangle is isomorphic to a localized integral one.
Apply integral exact duality and localize its shift comparison and inverse. This
proves exactness for the specified triangulation, without adjoining idempotents.
4. Integral full faithfulness gives inverse linear Hom maps, whose tensor extensions
remain inverse. Localized integral delta gives essential surjectivity. Its naturality
on pure tensors is integral naturality multiplied by the scalar, then extended to sums
(as in prop-weil-pbc-rational-transport for the covariant double-dual functors).
5. lem-pur-integral-operations-preserve-constructible keeps completed tensor in the
integral category. lem-fix-constructible-tensor-completion gives the normalized map chi
and its inverse. Integral evaluation on ordinary tensor, composed with chi inverse,
is completed evaluation. Localize this and the actual integral delta; naturality of
chi preserves evaluation and its transpose, with omega_E = Q omega_R.
6. lem-coef-integral-finite-extension supplies the canonical u and beta with their
inverses, evaluation and delta squares. Rationalize beta. Naturality on pure tensors
is integral naturality multiplied by the coefficient. Conjugating the ordinary tensor
comparison by chi identifies the completed comparison of the recorded tensor operation.
Localizing the two integral squares gives the evaluation and biduality clauses
of ExtensionProperties.
7. Localize the integral tensor unit and associator. Every factor in their equations
is integral, so functoriality of Q gives the displayed unit and associator equations
for these same specified canonical comparisons. Identity extensions are included. -/
theorem coef_rational_verdier
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))] :
    RationalVerdier.Conclusion D l hl X := by
  classical
  let duality (F : Type u) [Field F] [Algebra (Padic l) F]
      [FiniteDimensional (Padic l) F]
      (wF : IntegralFiniteExtension.DualizingDatum l X D hl F) :=
    (RationalVerdier.datum_of_integral_kflat D l hl X F wF
      (integral_verdier_biduality D l hl F X wF.omega wF.reduction)).choose
  -- SignedSymmetry already supplies naturality on all derived morphisms.
  have natural (F : Type u) [Field F] [Algebra (Padic l) F]
      [FiniteDimensional (Padic l) F]
      (wF : IntegralFiniteExtension.DualizingDatum l X D hl F) :=
    (duality F wF).symmetry.naturality
  let extension (F : Type u) [Field F] [Algebra (Padic l) F]
      [FiniteDimensional (Padic l) F]
      (G : Type u) [Field G] [Algebra (Padic l) G]
      [FiniteDimensional (Padic l) G] (i : F →ₐ[Padic l] G)
      (wF : IntegralFiniteExtension.DualizingDatum l X D hl F)
      (wG : IntegralFiniteExtension.DualizingDatum l X D hl G) :=
    (RationalVerdier.extension_exists D l hl X F G i wF wG
      (duality F wF) (duality G wG) (natural F wF) (natural G wG)).choose
  have properties (F : Type u) [Field F] [Algebra (Padic l) F]
      [FiniteDimensional (Padic l) F]
      (G : Type u) [Field G] [Algebra (Padic l) G]
      [FiniteDimensional (Padic l) G] (i : F →ₐ[Padic l] G)
      (wF : IntegralFiniteExtension.DualizingDatum l X D hl F)
      (wG : IntegralFiniteExtension.DualizingDatum l X D hl G) :
      RationalVerdier.ExtensionProperties D l hl X F G i wF wG
        (duality F wF) (duality G wG) (extension F G i wF wG) :=
    (RationalVerdier.extension_exists D l hl X F G i wF wG
      (duality F wF) (duality G wG) (natural F wF) (natural G wG)).choose_spec
  refine ⟨duality, extension, properties, ?_, ?_⟩
  · intro F _ _ _ wF
    exact RationalVerdier.extension_unit D l hl X F wF (duality F wF)
      (extension F F (AlgHom.id (Padic l) F) wF wF)
      (properties F F (AlgHom.id (Padic l) F) wF wF)
  · intro F _ _ _ G _ _ _ H _ _ _ i j wF wG wH
    exact RationalVerdier.extension_composition D l hl X F G H i j wF wG wH
      (duality F wF) (duality G wG) (duality H wH)
      (extension F G i wF wG) (extension G H j wG wH)
      (extension F H (j.comp i) wF wH)
      (properties F G i wF wG) (properties G H j wG wH)
      (properties F H (j.comp i) wF wH)

end WeilConjectures
