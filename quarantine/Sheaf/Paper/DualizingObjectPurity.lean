/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q58
-/
module

public import Sheaf.Paper.FiniteSmoothPullbackExchange
public import Sheaf.Paper.SmoothTrace
import Sheaf.Paper.PurityCompositionCoherence
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.Paper.CohomologicalSmoothnessTheorem
import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
import Sheaf.Paper.PurityDiagonalDualizingObject
import Sheaf.Paper.SmoothPurityMap
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor

/-! # Smooth purity from the diagonal dualizing object

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-thm-smooth-purity/cor-pur-dualizing-object-purity.md
(blueprint: cor-pur-dualizing-object-purity).

The map is the specified three-arrow composite on the original intrinsic
small-pro-etale object, with the recorded Kummer-normalized orientation and trace.
The base-change and composition assertions concern these same maps on the full
finite-type field domain, with only relative separatedness.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- The specified smooth purity map is an isomorphism, compatible with arbitrary
base change through the defined smooth exchange and with smooth composition.
Its source is Lf* K(d)[2d]; its target is the recorded exceptional image Rf! K.
The twist and trace normalization are those in smoothPurityMap and SmoothTrace,
which use the uniquely Kummer-normalized diagonal orientation.
Source: main-20261015 cor-pur-dualizing-object-purity, statement and proof;
DAG cor-pur-dualizing-object-purity, proof Steps 1--6
(blueprint: cor-pur-dualizing-object-purity).

Proof:
1. For M = Lf* K and T = A_X(d), the K-flat total-complex definitions identify
   (M tensor T)[2d] with M tensor T[2d]. The differential has no additional
   sign because 2d is even. This gives the specified smoothPurityReassociation,
   using def-coefficient-twists-detailed, def-weil-derived-tensor,
   def-pc-tensor-complex-sheaves and def-weil-abstract-derived-category.
2. thm-pur-diagonal-dualizing-object supplies precisely Pi_f on this full
   finite-type domain, without absolute separatedness. No second chart
   orientation is constructed.
3. thm-pur-cohomological-smoothness supplies invertibility of the canonical
   counit tensor map theta on Dctf. Tensor Pi_f.inv with 1_M and compose with
   reassociation and theta, exactly def-pur-smooth-purity-map. Each factor is
   invertible and natural in the original coefficient object K.
4. lem-pur-projection-purity-agreement identifies the separated affine-space
   models with the ordered Kummer-normalized projective-line integration maps,
   at every E and positive n, with the identity in dimension zero.
   lem-pur-vector-integration-site-comparison transports the actual normalized
   maps between the sites, independently of the annihilating exponent.
   def-pur-smooth-trace is Rf_!(gamma) followed by the exceptional counit.
   Thus the twist d, shift 2d and trace have the prescribed normalization.
5. For every Cartesian square in the same domain, pullback preserves bounded
   constructibility and finite Tor amplitude. The defined smooth exchange is
   (Lu*gamma)^-1 followed by b_square,K followed by gamma'. Cancelling the
   inverse gives the displayed commuting square, without any condition on v.
   This is def-pur-smooth-pullback-exchange and
   thm-pur-smooth-base-change-coherence, not a claim about another mate.
6. thm-pur-composition-coherence identifies the composite purity map with
   shifted pullback of gamma_g, then gamma_f at Rg! L, then c_(g,f)^-1,
   under the canonical source comparison. The twists add as d+e and the
   shifts as 2d+2e, with the specified exceptional compositor.
-/
theorem dualizingObjectPurity (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K) :
    ∃ hγ : IsIso (P.smoothPurityMap f d K hK),
    (∀ (X' Y' : Scheme.{u})
      [X'.Over (Spec (.of P.field.k))] [Y'.Over (Spec (.of P.field.k))]
      [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
      [QuasiCompact (X' ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
      [QuasiCompact (Y' ↘ Spec (.of P.field.k))]
      (u' : X' ⟶ X) (f' : X' ⟶ Y') (v : Y' ⟶ Y)
      [u'.IsOver (Spec (.of P.field.k))] [f'.IsOver (Spec (.of P.field.k))]
      [v.IsOver (Spec (.of P.field.k))]
      [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
      [SmoothOfRelativeDimension d f'] (sq : IsPullback u' f' f v),
      ∃ hK' : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y'
        ((P.finiteReductionPullback v).obj K),
      ∃ hγ' : IsIso (P.smoothPurityMap f' d ((P.finiteReductionPullback v).obj K) hK'),
        (P.finiteReductionPullback u').map (P.smoothPurityMap f d K hK) ≫
          (P.finiteReductionSmoothExchange u' f' f v sq d K hK).hom =
        (P.finiteReductionBaseChangeSource u' f' f v sq d K).hom ≫
          P.smoothPurityMap f' d ((P.finiteReductionPullback v).obj K) hK') ∧
    (∀ (Z : Scheme.{u}) [Z.Over (Spec (.of P.field.k))]
      [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
      [QuasiCompact (Z ↘ Spec (.of P.field.k))]
      (g : Y ⟶ Z) [g.IsOver (Spec (.of P.field.k))]
      [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
      (e : ℕ) [SmoothOfRelativeDimension e g]
      (L : Scheme.proEtaleDerivedCategory Z P.Ring)
      (hL : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Z L),
      P.smoothPurityMap (f ≫ g) (d + e) L hL =
        (P.compositionSourceIdentification f g d e L).hom ≫
          (P.compositionShiftedPullback f d).map (P.smoothPurityMap g e L hL) ≫
          P.smoothPurityMap f d ((P.compositionExceptional g).obj L)
            (P.compositionExceptional_ctf g e L hL) ≫
          (P.compositionExceptionalIso f g L hL).inv) := by
  sorry

end WeilConjectures.PurityFiniteSetting
