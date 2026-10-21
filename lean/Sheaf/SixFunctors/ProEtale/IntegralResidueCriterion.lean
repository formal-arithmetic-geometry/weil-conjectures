/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W8
-/
module

public import Sheaf.Paper.ConstantModelTorAmplitude
public import Sheaf.SixFunctors.ProEtale.DerivedCompletion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.IntegralModelsStacks
import Sheaf.AlgebraicGeometry.IntegralConstantCompletion
import Sheaf.Paper.IntegralLfpConstantModelComparison
import Sheaf.Paper.FiniteCoefficientModelComparison
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr

/-! # Integral constructibility detected by the actual residue reduction

Source: Stacks Project, Tags 099L and 09C1; blueprint integral models, clause (2).
(blueprint: lem-sfb-internal-integral-residue-criterion).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- The residue criterion in the internal continuous coefficient presentation.
Source: blueprint `sk-lem-integral-models`, clauses (1)--(2); Stacks 099L, 09C1.
(blueprint: lem-sfb-internal-integral-residue-criterion).

Proof: the integral coefficient limit identifies the continuous integer sheaf with
its positive finite-quotient limit. Pass to sectionwise modules and the equivalent
coefficient-sized small site; these exact equivalences preserve homology, signed tensor
complexes, and products. The normalized quotient maps identify derived scalar extension
at each positive level, including the actual quotient actions and tensor units.
Consequently the canonical augmentation into the Roos complex is the completion unit
used in integral_constant_completion. Its restriction equivalence identifies completeness
with the constant-coefficient Stacks completeness condition. At level one, finite discrete
coefficient comparison identifies finite constant local models and their cohomology on
both presentations. The residue is a field: the chosen uniformizer generates the maximal
ideal of the DVR. Every residue module sheaf is flat, as can be checked locally on the
constant field coefficients. Thus a bounded residue complex has finite Tor amplitude;
conversely finite Tor amplitude implies boundedness by testing the tensor unit.
The theorem integral_models_stacks now gives both directions of the displayed criterion.
Finally a finite constant module over a DVR has a length-one finite free resolution.
Exact pullback gives Tor interval [-1,0] on every constant local model. Finite constructible
stratification and open--closed localization detect vanishing of tensor homology against
any degree-zero module. Induction on a bounded cohomological interval gives [a-1,b] for
an integral bounded constructible complex with cohomology in [a,b]. Hence all such complexes
have finite Tor amplitude; the opposite inclusion in the equality is definitional.
The argument includes zero objects, empty schemes and torsion scalar modules. -/
theorem internal_integral_residue_criterion
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X] :
    (∀ K : DerivedCategory (AdicCompletion.Modules l E X),
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X K ↔
        IsDerivedComplete l E X K ∧
        constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) X
          ((AdicCompletion.derivedReduction l E X 0).obj K) ∧
        DerivedCategory.finiteTorAmplitude _
          ((AdicCompletion.derivedReduction l E X 0).obj K)) ∧
    constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X =
      (constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X ⊓
        DerivedCategory.finiteTorAmplitude (AdicCompletion.Modules l E X)) := by
  sorry

end AlgebraicGeometry.ProEtale
