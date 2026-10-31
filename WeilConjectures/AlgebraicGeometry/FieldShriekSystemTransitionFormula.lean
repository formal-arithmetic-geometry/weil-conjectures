/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldShriekSystemModels
public import WeilConjectures.AlgebraicGeometry.FiniteSupportCoordinates
public import WeilConjectures.AlgebraicGeometry.SemilinearDerivedSections
public import WeilConjectures.AlgebraicGeometry.FieldShriekSystemTransitions
public import WeilConjectures.SecSmoothPurity.ReductionDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.FieldShriekSupportEvaluation
public import WeilConjectures.AlgebraicGeometry.FieldShriekSystemEvaluation
public import WeilConjectures.SecSmoothPurity.ScalarExtensionFunctor
public import WeilConjectures.SixFunctors.SemilinearProperOpenCore
public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerShriekLevels
import WeilConjectures.AlgebraicGeometry.ProEtaleExtensionZero
import WeilConjectures.SixFunctors.OpenTensorNormalization

/-! # Extension-form transitions of compact-support coefficient systems

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension/
sk-lem-sp-field-extension-towers.proof.md (2), extension-form transitions
(blueprint: lem-route-field-shriek-system-transition-formula).

The two equalities concern the actual reduction maps on ordinary unbounded derived
systems. They retain the section-identity support and scalar evaluation coordinates.
The scalar formula also asserts the equality of the two composite coefficient maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.FieldShriekSystem

variable (P : PurityFiniteSetting.{u})

/-- Compact support carries the actual system reduction to the finite coefficient
comparison followed by compact support of the input reduction, in any section-identity
finite support coordinates. The input is an arbitrary ordinary derived system.

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension/
sk-lem-sp-field-extension-towers.proof.md (2)
(blueprint: lem-route-field-shriek-system-transition-formula).

Proof.
1. Exact termwise open extension commutes with scalar restriction by
   lem-cbc-proetale-extension-zero. By the arbitrary-system clause of
   lem-sf-open-tensor-normalization, its scalar comparison is uniquely determined by
   the open adjunction: after restriction and the open units it is the identity on
   sections. Consequently its extension-form transition is the transported
   reductionOpenScalarIso followed by open extension of the input transition.
   The section-identity quotient restriction coordinates preserve this transpose.
2. Apply lem-coef-semilinear-derived-sections to the proper direct image of that
   open extension. The Fcomparison of det-sp-tower-shriek-levels uses exactly its
   normalized pushEvaluation, so the system transition is the proper coefficient
   mate followed by direct image of the open transition. Conjugate through
   supportEvaluation, which is that comparison followed by the right-derived
   section-identity proper coordinate. Its transpose remains scalar extension of
   the same proper counit after the balanced pullback comparison. Conjugating the
   quotient restriction coordinates likewise identifies the semilinear scalar
   adjunction with finiteScalarAdjunction. Hence this mate is precisely gamma_p
   in def-sp-reduction-direct-image-comparison. Combining its open factor gives
   reductionDirectImageComparison and the displayed equality. This argument is
   an equality of the specified derived maps, without using evaluation faithfulness,
   normalization of the input, or flatness of the quotient.
-/
theorem support_reduction_formula (D : Models P) (E : Index P)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {m n : ℕ} (v : m ≤ n)
    (qX : QuotientRestriction P E X v) (qY : QuotientRestriction P E Y v)
    (zn : FiniteCoordinates P E c n) (zm : FiniteCoordinates P E c m)
    (N : SpTowerShriek.D P.coefficients.l E.val X) :
    (scalarExtensionFunctor (SpTowerCalculus.quotient P.coefficients.l E.val v) Y).map
        ((supportEvaluation P D E c n zn).inv.app N) ≫
      systemReduction P E Y v qY
        ((SpTowerShriek.F P.coefficients.l E.val (D.base E) (D.operations E) c).obj N) ≫
      (supportEvaluation P D E c m zm).hom.app N =
    (reductionDirectImageComparison (SpTowerCalculus.quotient P.coefficients.l E.val v)
        c.i c.g).app ((SpTowerShriek.Ev P.coefficients.l E.val X n).obj N) ≫
      (reductionCompactSupport (SpTowerShriek.R P.coefficients.l E.val m) c.i c.g).map
        (systemReduction P E X v qX N) := by
  sorry

/-- System scalar extension carries a quotient reduction to the scalar extension of
that reduction, with the two canonical balanced reassociations. The coefficient-square
equality is asserted as part of the conclusion, rather than assumed.

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension/
sk-lem-sp-field-extension-towers.proof.md (2)
(blueprint: lem-route-field-shriek-system-transition-formula).

Proof.
3. The ScalarEvaluation transpose equation of def-sp-field-shriek-system-evaluation
   identifies evaluation of the actual system scalar adjunction with the finite
   scalar adjunction. Thus the transition of scalar extension evaluates to scalar
   extension of the original transition, by lem-coef-semilinear-derived-sections,
   with the canonical balanced tensor identifications. The two reassociations are
   scalarExtensionFunctor_composition from det-sp-scalar-extension-functor (4),
   first for R_n^E to R_n^F to R_m^F, then inversely for R_n^E to R_m^E to R_m^F.
   Both composite ring maps take a residue class to its image in R_m^F: quotient_mk
   and the quotient factor maps show their equality on every representative.
   Transport across this equality and apply scalar extension to the original
   systemReduction. Associativity coherence identifies this word with the actual
   transition. No inverse of a reduction map or flatness hypothesis is used.
-/
theorem scalar_reduction_formula (D : Models P) {E F : Index P} (h : E ≤ F)
    (X : Scheme.{u}) {m n : ℕ} (v : m ≤ n)
    (qE : QuotientRestriction P E X v) (qF : QuotientRestriction P F X v)
    (en : ScalarEvaluation P D h X n) (em : ScalarEvaluation P D h X m) :
    ∃ hc : (SpTowerCalculus.quotient P.coefficients.l F.val v).comp
          ((D.coefficients E F h).quotient n) =
        ((D.coefficients E F h).quotient m).comp
          (SpTowerCalculus.quotient P.coefficients.l E.val v),
      ∀ N : SpTowerShriek.D P.coefficients.l E.val X,
        (scalarExtensionFunctor (SpTowerCalculus.quotient P.coefficients.l F.val v) X).map
            (en.iso.inv.app N) ≫
          systemReduction P F X v qF ((D.scalars E F h X).T.obj N) ≫
          em.iso.hom.app N =
        (scalarExtensionFunctor_composition ((D.coefficients E F h).quotient n)
            (SpTowerCalculus.quotient P.coefficients.l F.val v) X).hom.app
          ((SpTowerShriek.Ev P.coefficients.l E.val X n).obj N) ≫
        eqToHom (congrArg (fun a ↦ (scalarExtensionFunctor a X).obj
          ((SpTowerShriek.Ev P.coefficients.l E.val X n).obj N)) hc) ≫
        (scalarExtensionFunctor_composition (SpTowerCalculus.quotient P.coefficients.l E.val v)
            ((D.coefficients E F h).quotient m) X).inv.app
          ((SpTowerShriek.Ev P.coefficients.l E.val X n).obj N) ≫
        (scalarExtensionFunctor ((D.coefficients E F h).quotient m) X).map
          (systemReduction P E X v qE N) := by
  sorry

end AlgebraicGeometry.ProEtale.FieldShriekSystem
