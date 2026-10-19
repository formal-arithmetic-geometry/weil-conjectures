/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.ConstructibleIntervals
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.Paper.FiniteExceptionalInverseImage
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.AmbientExceptionalRightAdjoint
import Sheaf.Paper.ExceptionalAdjointAdmissibility
import Sheaf.AlgebraicGeometry.SmoothTensorDuality
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import WeilConjectures.Compactification.NagataCompactification
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.AlgebraicGeometry.ResidueTorAmplitudeTest
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.ConstructibleSheaf.Pullback
import Sheaf.AlgebraicGeometry.PullbackConstantModule
import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes

import Sheaf.AlgebraicGeometry.DerivedCategories
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import Sheaf.AlgebraicGeometry.ConstructibleModuleUnderlyingSets
import Sheaf.AlgebraicGeometry.EtaleLocalIsomorphismConstructible
import Sheaf.Paper.ComparisonTorAmplitude
import Sheaf.Paper.FiniteTorAmplitudeSites
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.AlgebraicGeometry.ModuleLocalConstancyOfFiniteUnderlying
/-! # Smooth exceptional inverse image preserves the two finite coefficient classes

Source: blueprint sec-six-functors/sk-prop-sf-rf-shriek-preservation,
cor-pur-smooth-admissibility, order 2077 (blueprint: cor-pur-smooth-admissibility).

These are the two preservation clauses, with signed shift -2d. The unrestricted
ambient adjoint datum is not a hypothesis or a conclusion. No assertion at integral,
rational, or algebraically closed coefficients is made.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.PurityFiniteSetting

/-- The coefficient prime is invertible in every local ring of every k-scheme.
Source: the fixed setting of cor-pur-smooth-admissibility, proof step 1
(blueprint: cor-pur-smooth-admissibility).
Proof: the finite field has cardinality p^a, hence characteristic p; its algebraic
closure has characteristic p as well. Since ell differs from p, ell is nonzero
and therefore a unit in k. Its image under the structure map to each local ring
is a unit. No smoothness or finite-type assumption is needed for this observation. -/
theorem prime_isUnit_stalk (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] (t : T) :
    IsUnit (P.coefficients.l : T.presheaf.stalk t) := by
  sorry

/-- Smooth separated finite-type morphisms of finite-type k-schemes shift both
constructible cohomological intervals and finite Tor amplitude by -2d. The first
clause quantifies over all bounded constructible inputs, including those of infinite
Tor dimension. The final clause explicitly gives preservation of D^b_ctf.
Source: blueprint cor-pur-smooth-admissibility, clauses (1)--(2), order 2077
(blueprint: cor-pur-smooth-admissibility).

Proof, following the eight steps of the node:
1. Finite type over k makes X and Y Noetherian and Y qcqs. Nagata gives a
compactification of f. The coefficient ring is finite, and ell^n annihilates it,
since ell belongs to the uniformizer ideal. This exponent is invertible on Y.
Apply thm-asd-smooth-tensor with precisely these hypotheses.
2. By lem-sf-proetale-constructible-origin, choose an etale representative G of
any bounded constructible input M. Exact comparison identifies its cohomology
with that of M, and reflects zero sheaves. Thus G has the same interval as M.
The defining exceptional functor formula gives nu_X^* f^times G. The adjunction
interpretation is cor-sf-ambient-adjoint-discharge, without an ambient hypothesis.
3. Smooth tensor duality identifies f^times G with f^*G tensor omega_f for every
G, and omega_f with T[2d] for a locally constant free rank-one module sheaf T.
Choose an etale cover trivializing T; no Tate orientation is necessary.
4. Monoidal inverse image and the triangulatedness of derived tensor identify
these local restrictions with (u^* f^*G)[2d]. The final tensor unit is computed
on a K-flat representative P by P tensor A = P.
5. Exact inverse image gives H^r locally equal to u^* f^* H^(r+2d)(G).
It vanishes outside [a-2d,b-2d]. Pull back the finite constructible
stratification of each cohomology sheaf; on every stratum, refine the trivializing
cover by a cover on which the pulled-back sheaf is finite constant. This proves
constructibility with the same finite strata, even if the cover is infinite.
Comparison gives clause (1), with no assumption about Tor amplitude.
6. For K of finite Tor amplitude, lem-sf-comparison-tor-amplitude reflects
its interval to its bounded constructible etale representative G. The residue
criterion lem-exc-residue-tor-test says G tensor kappa has that interval.
7. On the same trivializing cover, the residue tensor of H = f^times G is
(u^* f^*(G tensor kappa))[2d]. Exact inverse image and the cohomology shift
put it in [a-2d,b-2d]. Coverwise vanishing is vanishing of the sheaf.
8. H is already bounded constructible by step 5. The etale residue test now
proves its shifted Tor interval; comparison preserves this interval against all
pro-etale degree-zero module sheaves. Bounded constructibility and finite Tor
amplitude give D^b_ctf preservation. These are exactly the signed constants
c_f^- = c_f^+ = -2d; coefficient transport at other stages is not asserted. -/
theorem smooth_exceptional_preservation (P : WeilConjectures.PurityFiniteSetting.{u})
    (X Y : Scheme.{u}) [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f] :
    (∀ (a b : ℤ) (hab : a ≤ b) (L : proEtaleDerivedCategory Y P.Ring),
      finiteTorsionConstructibleIn P.coefficients.l P.extension P.level P.level_pos
        Y (P.prime_isUnit_stalk Y) a b hab L →
      finiteTorsionConstructibleIn P.coefficients.l P.extension P.level P.level_pos
        X (P.prime_isUnit_stalk X) (a - 2 * (d : ℤ)) (b - 2 * (d : ℤ))
        (sub_le_sub_right hab _) ((finiteExceptionalInverseImage P.coefficients.l
          P.extension P.level P.level_pos P.field.k X Y f).obj L)) ∧
    (∀ (a b : ℤ) (K : proEtaleDerivedCategory Y P.Ring),
      finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K →
      HasProEtaleTorAmplitude Y P.Ring K a b →
      HasProEtaleTorAmplitude X P.Ring
        ((finiteExceptionalInverseImage P.coefficients.l P.extension P.level P.level_pos
          P.field.k X Y f).obj K) (a - 2 * (d : ℤ)) (b - 2 * (d : ℤ))) ∧
    (∀ K : proEtaleDerivedCategory Y P.Ring,
      finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K →
      finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos X
        ((finiteExceptionalInverseImage P.coefficients.l P.extension P.level P.level_pos
          P.field.k X Y f).obj K)) := by
  sorry

end WeilConjectures.PurityFiniteSetting
