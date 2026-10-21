/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.Paper.NormContinuousMonodromyData
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
import Sheaf.AlgebraicGeometry.NormalTopologicallyNoetherianComponents
import Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization
import Sheaf.CategoryTheory.SetSheafCoverDescent
import Sheaf.AlgebraicGeometry.FundamentalGroup.NormalSchemeGaloisInertiaPresentation
import Sheaf.Paper.FibreFunctorBasepointTransport

/-! # Normal-scheme monodromy for full norm-topology coefficients

Source: Bhatt--Scholze, Section 7.4, Lemmas 7.4.7 and 7.4.10, pp. 70--71,
with the agent norm-topology strengthening and its nine-step proof in the DAG.
Remark 7.4.8 uses a different topology and is not used for the algebraic-closure case.
(blueprint: lem-sfb-normal-continuous-algcl-monodromy).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.ProEtale

/-- Simultaneous linear equivalences for the algebraic closure and every finite intermediate
field, compatible with ordinary internal extension along the actual continuous-map inclusion.
The norm on Ω extends the p-adic norm, and intermediate fields have their induced norm.
The finite-basis representation category includes rank zero and uses all continuous entries.

Source: Bhatt--Scholze, Lemmas 7.4.7 and 7.4.10, pp. 70--71, and the norm-topology
strengthening recorded in this node (blueprint: lem-sfb-normal-continuous-algcl-monodromy).

Proof: (1) Noetherian normal components are finitely many disjoint clopen integral schemes;
connectedness and nonemptiness make X integral. Identify p_X^*C(-,K) with continuous functions,
using total disconnectedness of K. (2) The normal-generic section bijection extends every
matrix uniquely from the generic fibre; uniqueness and sheaf descent glue maps and inverses.
This proves full faithfulness of generic restriction and constancy of the free rank.
(3) Over a separable closure, evaluate the Cech descent matrix on G_k. The cocycle identity
is the representation law; maps are constant intertwining matrices. Coefficient extension
acts entrywise. (4) Complete K to F. Small congruence subgroups give GL_n(F) an open-subgroup
basis, and entrywise limits of Cauchy matrices and inverses prove two-sided completeness.
This includes n=0. (5) Extend L to F and apply complete-group torsor monodromy to its frame
torsor. Pointed generic pullback and the field clause identify its cocycle with the image of
the K-valued generic cocycle. (6) The generic Galois-to-etale-pi1 map is surjective. Injectivity
of K → F kills its kernel on the K-cocycle. A surjection of profinite groups is a quotient map,
so the factor has continuous entries; generic full faithfulness identifies all intertwiners.
(7) Conversely the compact image of a continuous representation has an open-subgroup basis;
its torsor glues free K-modules by its transition matrices. Effective sheaf descent glues
addition and action, and completion plus injectivity identifies its generic cocycle.
(8) Transport the fundamental group from the generic basepoint to the prescribed point by
one path for every coefficient field. Regular and finite-sum matrices are respectively 1
and block sums; empty matrices give rank zero. Matrix operations prove linearity.
(9) On each free chart scalar extension sends entries by E → Ω. The generic Cech comparison
is Ω ⊗_E V with g(a ⊗ v)=a ⊗ ρ(g)v. The same generic quotient and basepoint path give the
comparison here; its equality on every morphism matrix proves naturality. All continuous
Ω-valued functions are retained throughout. -/
theorem normal_continuous_algCl_monodromy (l : ℕ) [Fact l.Prime]
    (Ω : Type u) [NormedField Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (hnorm : ∀ a : ℚ_[l], ‖algebraMap ℚ_[l] Ω a‖ = ‖a‖)
    (X : Scheme.{u}) [ConnectedSpace X] [IsNoetherian X] [X.IsSeparated]
    (hinvertible : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hnormal : ∀ x : X,
      IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
    {Ωx : Type u} [Field Ωx] [IsAlgClosed Ωx] (x : Spec (.of Ωx) ⟶ X) :
    ∃ eΩ : NormContinuousMonodromy Ω X (Aut (Scheme.flcFiber x)),
      ∀ E : IntermediateField ℚ_[l] Ω, FiniteDimensional ℚ_[l] E →
        ∃ eE : NormContinuousMonodromy E X (Aut (Scheme.flcFiber x)),
          ∃ hE : Continuous (algebraMap E Ω),
            Nonempty (NormContinuousScalarComparison X (Aut (Scheme.flcFiber x)) hE eE eΩ) := by
  sorry

end AlgebraicGeometry.ProEtale
