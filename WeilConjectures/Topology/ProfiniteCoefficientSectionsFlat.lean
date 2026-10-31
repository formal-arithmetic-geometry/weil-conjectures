/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.CategoryTheory.RingObjects.GlobalSections
public import Mathlib.RingTheory.RingHom.Flat
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.RingTheory.Flat.TorsionFree
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import Mathlib.Topology.ContinuousMap.LocallyConstant

/-!
# Flatness of profinite sections of the four coefficient rings

Source: Hemo--Richarz--Scholbach, Proposition 6.8 and Lemma 6.10; Stacks, Tag 0AUW,
`lemma-dedekind-torsion-free-flat` (1); blueprint, `def-weil-finite-coefficient-point`,
Extension of scalars paragraph (blueprint: lem-sp-profinite-coefficient-sections-flat).

The quotient coefficient is discrete. The field and its integer ring have their
valuation subspace topologies. Algebraic-closure sections retain the existing
finite-subextension restriction. No nonemptiness assumption is made on the profinite set.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace Profinite

/-- The section ring of the discrete finite quotient coefficient, with its actual continuous
functions and pointwise operations. The bundled ring keeps the chosen discrete topology
explicit without adding a topology instance to the coefficient type.
Source: HRS Proposition 6.8; blueprint `def-weil-finite-coefficient-point`, coefficient list
(blueprint: lem-sp-profinite-coefficient-sections-flat). -/
noncomputable def finiteCoefficientSections (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) (S : Profinite.{u}) :
    CommRingCat.{u} :=
  letI : TopologicalSpace (Padic.coefficientExtensionRing ℓ E.1 n) := ⊥
  letI : DiscreteTopology (Padic.coefficientExtensionRing ℓ E.1 n) := ⟨rfl⟩
  CommRingCat.of C(S, Padic.coefficientExtensionRing ℓ E.1 n)

/-- The constant-section homomorphism for the discrete quotient coefficient.
Source: HRS Proposition 6.8; blueprint Extension of scalars paragraph
(blueprint: lem-sp-profinite-coefficient-sections-flat). -/
noncomputable def finiteCoefficientConstSections (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) (S : Profinite.{u}) :
    Padic.coefficientExtensionRing ℓ E.1 n →+* finiteCoefficientSections ℓ E n S :=
  letI : TopologicalSpace (Padic.coefficientExtensionRing ℓ E.1 n) := ⊥
  letI : DiscreteTopology (Padic.coefficientExtensionRing ℓ E.1 n) := ⟨rfl⟩
  ContinuousMap.C

/-- Constant sections for the integer ring, with the subspace valuation topology induced
from the intermediate field in the fixed algebraic closure.
Source: HRS Lemma 6.10; Stacks Tag 0AUW (1)
(blueprint: lem-sp-profinite-coefficient-sections-flat). -/
noncomputable def integralCoefficientConstSections (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (S : Profinite.{u}) :
    Padic.coefficientExtensionIntegers ℓ E.1 →+*
      C(S, Padic.coefficientExtensionIntegers ℓ E.1) :=
  ContinuousMap.C

/-- The existing algebraic-closure constant-section map, with its commutative section ring
visible as the actual lifted finite-subextension subring rather than through `RingCat`.
Source: blueprint `det-def-sfb-qlbar-condensed`, displayed section formula
(blueprint: lem-sp-profinite-coefficient-sections-flat). -/
noncomputable def algClosureCoefficientConstSections (ℓ : ℕ) [Fact ℓ.Prime]
    (S : Profinite.{u}) :
    PadicAlgCl ℓ →+* ULift.{u + 1} (PadicAlgCl.finiteIntermediateFieldValued ℓ S) :=
  Profinite.PadicAlgCl.constSectionRingHom ℓ (op S)

/-- The constant-section maps are flat for the discrete quotient, the integer ring,
the finite coefficient field, and the finite-subextension algebraic-closure coefficient.
Source: HRS Proposition 6.8 and Lemma 6.10; Stacks Tag 0AUW (1); blueprint
`def-weil-finite-coefficient-point`, Extension of scalars paragraph
(blueprint: lem-sp-profinite-coefficient-sections-flat).

Proof: The first three section rings are continuous-function rings with pointwise
operations, and the scalar action of a constant is pointwise scalar multiplication.
For the discrete quotient, use the directed set of finite partitions into nonempty
clopen pieces. Include the empty partition when S is empty. Two partitions have the
common refinement of their nonempty intersections. The functions constant on a partition
form a finite free module with the characteristic functions as basis. Every continuous
map to the discrete coefficient is constant on a finite clopen partition, by compactness.
These submodules have union the entire section module; compatible linear maps descend
uniquely from the union, proving that it is their filtered colimit. Finite free modules
are flat (`lem-sc-affine-standard-cover-finite-free-local-fp-flat`), and their filtered
colimit is flat (`lem-weil-pbc-filtered-colimit-flat-modules`). This works for nonreduced
quotients as well as fields.

The integer ring is a PID by clause 2 of `lem-weil-l-adic-extension-integers-dvr`.
A continuous function killed by a nonzero scalar is zero pointwise, since the integer
ring is a subring of a field. Hence its scalar module is torsion-free, and is flat by
`lem-weil-pbc-pid-torsion-free-module-flat`, without a finite-generation assumption.
The finite-field section ring is a vector space, hence flat by
`lem-weil-pbc-module-over-field-flat`.

For the algebraic closure use the actual finite-intermediate-field-valued subring:
if f and g lie in finite stages F and G and a is an algebraic scalar, f+g and af lie
in the finite compositum FG Q_l(a). Continuity and all module identities are pointwise.
Thus this restricted section ring is a vector space over the entire algebraic closure,
and the same field-flatness lemma applies. For S empty all four section modules are
zero; the unique empty function also satisfies the finite-stage condition. This proves
all four flatness assertions, using `def-weil-pbc-flat-ring-map` for the equivalence
between ring-map flatness and flatness of its scalar module. -/
theorem profinite_coefficient_constSections_flat (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) (_hn : 1 ≤ n)
    (S : Profinite.{u}) :
    (finiteCoefficientConstSections ℓ E n S).Flat ∧
      (integralCoefficientConstSections ℓ E S).Flat ∧
      (ContinuousMap.C (α := S) (R := E.1) (A := E.1)).Flat ∧
      (algClosureCoefficientConstSections ℓ S).Flat := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · let R := Padic.coefficientExtensionRing ℓ E.1 n
    let : TopologicalSpace R := ⊥
    let : DiscreteTopology R := ⟨rfl⟩
    change (ContinuousMap.C (α := S) (R := R) (A := R)).Flat
    rw [show ContinuousMap.C (α := S) (R := R) (A := R) = algebraMap R C(S, R)
      from rfl, RingHom.flat_algebraMap_iff]
    apply Module.Flat.of_linearEquiv
      (LinearEquiv.ofBijective (LocallyConstant.toContinuousMapLinearMap R) ?_).symm
    refine ⟨LocallyConstant.toContinuousMap_injective, ?_⟩
    intro f
    exact ⟨⟨f, (IsLocallyConstant.iff_continuous _).2 f.continuous⟩, rfl⟩
  · have h := (Padic.extension_integers_dvr ℓ E.1
        (Padic.coefficientExtensionAbsoluteValue ℓ E.1)
        (spectralNorm_extends (K := ℚ_[ℓ]) (L := E.1))).choose_spec.choose_spec
    let : IsPrincipalIdealRing (Padic.coefficientExtensionIntegers ℓ E.1) :=
      h.2.2.2.2.2.2.2.2.1
    rw [integralCoefficientConstSections, show
      ContinuousMap.C (α := S) (R := Padic.coefficientExtensionIntegers ℓ E.1)
        (A := Padic.coefficientExtensionIntegers ℓ E.1) =
        algebraMap _ C(S, Padic.coefficientExtensionIntegers ℓ E.1) from rfl,
      RingHom.flat_algebraMap_iff]
    let : Module.IsTorsionFree (Padic.coefficientExtensionIntegers ℓ E.1)
        C(S, Padic.coefficientExtensionIntegers ℓ E.1) := by
      constructor
      intro a ha f g hfg
      apply ContinuousMap.ext
      intro s
      exact ha.left (ContinuousMap.congr_fun hfg s)
    infer_instance
  · rw [show ContinuousMap.C (α := S) (R := E.1) (A := E.1) =
        algebraMap E.1 C(S, E.1) from rfl, RingHom.flat_algebraMap_iff]
    infer_instance
  · rw [RingHom.Flat]
    infer_instance

end Profinite
