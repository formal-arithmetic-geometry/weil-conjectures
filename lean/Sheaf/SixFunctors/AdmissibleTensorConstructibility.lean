/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.AlgebraicGeometry.EtaleFlatConstructibleModel
import Sheaf.Paper.CondensedCoefficientIsoConstructible
import Sheaf.Paper.LocallyConstantTensor
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import WeilConjectures.ConstructibleSheaf.Refinement

/-!
# Tensor constructibility for admissible condensed coefficients

This isolates the constructibility calculation, without the generic Tor-amplitude addition,
from det-thm-sf-ctf-stability-direct-images.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Derived tensor preserves bounded constructibility for two admissible-coefficient
constructible complexes of finite Tor amplitude.

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-sf-ctf-stability,
det-thm-sf-ctf-stability-direct-images, proof steps 2--3
(blueprint: lem-sfb-admissible-tensor-constructibility).

Proof:
1. Finite type over the field makes X Noetherian and qcqs. Transport along the ring-object
isomorphism in hΛ; scalar restriction along an isomorphism is an exact monoidal equivalence,
preserves finite constant presentations, and hence preserves the two constructibility
predicates and Tor intervals.
2. For a finite ring A, use finiteTorComparisonNoetherian to descend both complexes with
unchanged Tor intervals to the etale site. The finite-value flat-constructible-model theorem
represents them by bounded flat constructible complexes in those intervals. Refine the
finitely many termwise stratifications. Tensor terms are constructible on the refinement:
locally they are tensors of finite A-modules, and these are finite. Finite direct sums,
kernels and cokernels remain constructible. The total tensor is bounded, has these
constructible cohomology sheaves, and is K-flat since it is bounded with flat terms. The
monoidal comparison pullback identifies it with the specified pro-etale derived tensor.
3. For O_E apply integralModelsOperations(2); for E and the finite-subextension-valued
algebraic closure apply tensorClosureRational(1). The base-field cases Z_l and Q_l are
O_E and E at E = Q_l. For the retained all-continuous algebraic-closure coefficient,
apply the lisse-generator argument directly: finite presented scalar modules over the
field are finite free; after refining the stratifications the tensor of the two lisse
factors is lisse finite free. The locally closed projection formula and finite-cone
induction give constructibility, as in the proof of tensorClosureRational. This keeps the
all-continuous coefficient distinct
from the finite-subextension-valued one. Transport back through the isomorphism of step 1.
The zero ring, zero complexes and empty strata are included by the same constructions.
-/
theorem constantModelBoundedConstructible_tensor_of_admissible
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    (K M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (hK : constantModelBoundedConstructible Λ X K ∧
      DerivedCategory.finiteTorAmplitude _ K)
    (hM : constantModelBoundedConstructible Λ X M ∧
      DerivedCategory.finiteTorAmplitude _ M) :
    constantModelBoundedConstructible Λ X (((-⊗ᴸ-(X)⟦Λ⟧).obj K).obj M) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
