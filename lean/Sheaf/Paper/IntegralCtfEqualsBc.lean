/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Sheaf.Paper.ProfiniteFiniteConstantLocalModel
public import Sheaf.Paper.ConstantModelTorAmplitude
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.RingTheory.GlobalDimension
public import Mathlib.Topology.Instances.ZMod
import Sheaf.Paper.LocalizingClosureCtfEqualsBc
import Sheaf.Paper.PadicConstantLocalModelTor
import Sheaf.Paper.StratifiedTorIntervalDevissage
import Sheaf.Paper.CohomologyTorInterval
import Sheaf.Paper.SquareZeroPeriodicTensor
import Sheaf.Paper.ConstantSquareZeroTorExample
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom

/-! # Integral and rational constructible complexes have finite Tor amplitude

Source: blueprint latest, sec-proetale-coefficients/sk-prop-integral-criterion,
lem-integral-ctf-equals-bc and its proof, Local models through The examples
(blueprint: lem-integral-ctf-equals-bc).

Constructibility is the finite constant scalar model convention. All derived categories
and tensors below are ordinary and uncompleted. The helper definitions construct the
specified scalar examples and the constant residue and two-term free complex in every
scheme universe.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj MonoidalCategory

namespace AlgebraicGeometry.ProEtale

/-- Constructible modules have amplitude `[-1,0]`, or `[0,0]` over a field. A bounded
constructible complex with cohomology in `[a,b]` has amplitude `[a-1,b]`, or `[a,b]`
over a field. Thus the object predicates of the two full subcategories agree.

Source: blueprint latest, integral criterion, lem-integral-ctf-equals-bc, clauses 1--2
(blueprint: lem-integral-ctf-equals-bc).

Proof: for each scheme, lem-sfb-padic-constant-local-model-tor resolves a finite scalar
model by finite free modules in degrees -1,0 over the DVR, and in degree 0 over the
field. This includes torsion scalar modules and finite-subextension-valued Qbar.
Apply lem-sfb-stratified-tor-interval-devissage with the same endpoints on every
scheme. Its finite open--closed refinement works for arbitrary constructible locally
closed strata; qcqs gives the finite stratification needed here. Enlarge the field
interval to [-1,0] when necessary. Each cohomology module of a bounded constructible
complex has that interval, by det-def-sfb-constructible-tor-amplitude. Apply
lem-sfb-cohomology-tor-interval with module interval [-1,0], respectively [0,0],
to obtain [a-1,b], respectively [a,b]. The Tor predicate tests every degree-zero
module, without a constructibility restriction on the test. Boundedness supplies
some finite cohomology interval, giving finite Tor amplitude. Conversely Dctf is
the intersection of Dbc with finite Tor amplitude, so extensionality gives equality
of their object predicates, with the same ambient morphisms. -/
theorem integral_ctf_equals_bc
    (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ :
      Nonempty (Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      Nonempty (Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E)) ∨
        Nonempty (Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ))) :
    (∀ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X),
      IsConstantModelConstructible Λ.X X M →
      DerivedCategory.torAmplitudeIn _ (-1) 0
        ((DerivedCategory.singleFunctor _ 0).obj M)) ∧
    (∀ (K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)))
        (a b : ℤ), a ≤ b → constantModelBoundedConstructible Λ.X X K →
      DerivedCategory.homologyConcentratedIn a b K →
      DerivedCategory.torAmplitudeIn _ (a - 1) b K) ∧
    ((Nonempty (Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
        (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
          Nonempty (Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
        Nonempty (Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ))) →
      (∀ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X),
        IsConstantModelConstructible Λ.X X M →
        DerivedCategory.torAmplitudeIn _ 0 0
          ((DerivedCategory.singleFunctor _ 0).obj M)) ∧
      (∀ (K : DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)))
          (a b : ℤ), a ≤ b → constantModelBoundedConstructible Λ.X X K →
        DerivedCategory.homologyConcentratedIn a b K →
        DerivedCategory.torAmplitudeIn _ a b K)) ∧
    (constantModelBoundedConstructible Λ.X X ⊓ DerivedCategory.finiteTorAmplitude _) =
      constantModelBoundedConstructible Λ.X X := by
  sorry

/-- The scalar residue `(Z/ell²)/(ell)` of the specific square-zero example.
Source: blueprint latest, integral criterion, lem-integral-ctf-equals-bc, The examples
(blueprint: lem-integral-ctf-equals-bc). -/
abbrev integralCriterionScalarResidue (ℓ : ℕ) : Type :=
  ZMod (ℓ ^ 2) ⧸ Ideal.span ({(ℓ : ZMod (ℓ ^ 2))} : Set (ZMod (ℓ ^ 2)))

/-- The specified scalar complex `[A --ell--> A]` in degrees -1,0, represented by
its mapping cone. Its multiplication map is the actual scalar linear map.
Source: blueprint latest, integral criterion, lem-integral-ctf-equals-bc, The examples
(blueprint: lem-integral-ctf-equals-bc). -/
def integralCriterionScalarTwoTerm (ℓ : ℕ) :
    DerivedCategory (ModuleCat.{0} (ZMod (ℓ ^ 2))) :=
  let A := ZMod (ℓ ^ 2)
  let F := CochainComplex.singleFunctor (ModuleCat.{0} A) 0
  let f : F.obj (ModuleCat.of A A) ⟶ F.obj (ModuleCat.of A A) :=
    F.map (ModuleCat.ofHom (LinearMap.mulLeft A (ℓ : A)))
  DerivedCategory.Q.obj (CochainComplex.mappingCone f)

/-- The finiteness, infinite projective dimension, and perfectness assertions for the
specified scalar square-zero example. Perfectness uses the recorded bounded finite
projective complex predicate, with no new perfectness convention.
Source: blueprint latest, integral criterion, lem-integral-ctf-equals-bc, The examples
(blueprint: lem-integral-ctf-equals-bc). -/
def integralCriterionScalarExample (ℓ : ℕ) : Prop :=
  Module.Finite (ZMod (ℓ ^ 2)) (integralCriterionScalarResidue ℓ) ∧
  ¬ ModuleCat.HasFiniteProjectiveDimension
    (ModuleCat.of (ZMod (ℓ ^ 2)) (integralCriterionScalarResidue ℓ)) ∧
  DerivedCategory.IsPerfectRingComplex (integralCriterionScalarTwoTerm ℓ) ∧
  ¬ DerivedCategory.IsPerfectRingComplex
    ((DerivedCategory.singleFunctor (ModuleCat.{0} (ZMod (ℓ ^ 2))) 0).obj
      (ModuleCat.of (ZMod (ℓ ^ 2)) (integralCriterionScalarResidue ℓ)))

/-- The scalar residue has infinite projective dimension and is not perfect, whereas
`[A --ℓ--> A]` is perfect and its only nonzero cohomology modules are the residue field.

Source: blueprint latest, integral criterion, lem-integral-ctf-equals-bc, The examples
(blueprint: lem-integral-ctf-equals-bc).

Proof: for A = Z/ell², multiplication by ell has kernel ell A and cokernel A/ell A.
The quotient is F_ell and multiplication by ell identifies A/ell A with ell A.
The periodic resolution of lem-sfb-square-zero-periodic-tensor therefore computes
self-Tor equal to the nonzero residue in every nonnegative homological degree.
There is no finite projective dimension. A bounded finite projective complex has
finite Tor amplitude, so the residue is not perfect. The concrete two-term cone
has finite free terms and is perfect, as also asserted by
det-def-localizing-closure-ctf-equals-bc. Its kernel and cokernel computation gives
the displayed cohomology; its other degrees vanish. -/
theorem integral_ctf_scalar_counterexample (ℓ : ℕ) [Fact ℓ.Prime] :
    integralCriterionScalarExample ℓ ∧
    Nonempty (integralCriterionScalarResidue ℓ ≃+* ZMod ℓ) ∧
    DerivedCategory.homologyConcentratedIn (-1) 0 (integralCriterionScalarTwoTerm ℓ) ∧
    (∀ q : ℤ, q ∈ Set.Icc (-1) 0 →
      Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{0} (ZMod (ℓ ^ 2))) q).obj
        (integralCriterionScalarTwoTerm ℓ) ≅
        ModuleCat.of (ZMod (ℓ ^ 2)) (integralCriterionScalarResidue ℓ))) := by
  sorry

/-- Over every finite discrete commutative coefficient ring, Dctf is triangulated and
closed under direct summands.

Source: blueprint latest, integral criterion, lem-integral-ctf-equals-bc, final sentence
(blueprint: lem-integral-ctf-equals-bc).

Proof: det-def-localizing-closure-ctf-equals-bc gives finite-ring thickness.
Equivalently, the finite-discrete encoding identifies finite scalar local models
with finite locally constant modules. Their constructible class is Serre, so bounded
constructible cohomology is triangulated and stable under retracts. By
det-def-sfb-constructible-tor-amplitude the finite-Tor objects are thick; intersect
the two properties. This argument includes the zero ring and the empty scheme. -/
theorem integral_ctf_finite_ring_thick
    (A : Type u) [CommRing A] [Finite A] [TopologicalSpace A]
    [DiscreteTopology A] [IsTopologicalRing A]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
    (constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj A) X ⊓
      DerivedCategory.finiteTorAmplitude _).IsTriangulated ∧
    (constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj A) X ⊓
      DerivedCategory.finiteTorAmplitude _).IsStableUnderRetracts := by
  sorry

/-- The constant residue `(Z/ell²)_X / ell`, constructed as the cokernel on the small
pro-etale site. This is the pullback of the condensed residue cokernel, because the
inverse image is exact and strong monoidal. It extends the existing universe-zero
`constantResidueModuleOnSpec` construction to an arbitrary scheme universe.
Source: blueprint latest, integral criterion, lem-integral-ctf-equals-bc, The examples
(blueprint: lem-integral-ctf-equals-bc). -/
def integralCriterionResidue (ℓ : ℕ) (X : Scheme.{u}) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} (ZMod (ℓ ^ 2))) X) :=
  cokernel ((ℓ : ℕ) • (𝟙 (𝟙_ (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (Profinite.continuousMapRingObj.{u} (ZMod (ℓ ^ 2))) X)))))

/-- The specific constant two-term free complex `[A_X --ell--> A_X]` in degrees -1,0.
It is the image of the mapping cone of multiplication on the degree-zero tensor unit.
Source: blueprint latest, integral criterion, lem-integral-ctf-equals-bc, The examples
(blueprint: lem-integral-ctf-equals-bc). -/
def integralCriterionTwoTerm (ℓ : ℕ) (X : Scheme.{u}) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} (ZMod (ℓ ^ 2))) X)) :=
  DerivedCategory.Q.obj (CochainComplex.mappingCone
    ((CochainComplex.singleFunctor _ 0).map ((ℓ : ℕ) • (𝟙 (𝟙_
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj.{u} (ZMod (ℓ ^ 2))) X)))))))

/-- On any separably closed point the constant residue is constructible with no finite
Tor amplitude. The specified constant two-term free complex is bounded constructible
and has amplitude [-1,0], with residue cohomology in both degrees; its upper truncation
at zero has no finite Tor amplitude. Thus Dctf need not be stable under truncations.

Source: blueprint latest, integral criterion, lem-integral-ctf-equals-bc, The examples
(blueprint: lem-integral-ctf-equals-bc).

Proof: use the periodic scalar resolution in lem-sfb-square-zero-periodic-tensor.
Exact monoidal pullback preserves its terms, differential and kernel/cokernel
identifications. The residue is nonzero on Spec k, so its self-Tor is nonzero in
arbitrarily negative cohomological degrees. The single scalar presentation makes it
constructible. This is the construction of lem-sfb-constant-square-zero-tor-example,
with the same proof in every site universe. The two-term cone has residue kernel
and cokernel and no other cohomology. Its terms are free rank one, hence flat;
lem-sfb-bounded-above-flat-kflat makes it K-flat, and
sk-def-sfb-derived-tensor-hom computes its tensor with any module N as [N --ell--> N].
It has amplitude [-1,0]. Its cohomology is constructible and bounded. Its standard
upper truncation at zero is the degree-zero residue, whose infinite Tor amplitude
was just computed. -/
theorem integral_ctf_constant_counterexample
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [IsSepClosed k] :
    IsConstantModelConstructible (Profinite.continuousMapRingObj.{u} (ZMod (ℓ ^ 2)))
      (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))
      (integralCriterionResidue ℓ (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))) ∧
    ¬ DerivedCategory.finiteTorAmplitude _ ((DerivedCategory.singleFunctor _ 0).obj
      (integralCriterionResidue ℓ (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))) ∧
    constantModelBoundedConstructible
      (Profinite.continuousMapRingObj.{u} (ZMod (ℓ ^ 2)))
      (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))
      (integralCriterionTwoTerm ℓ (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))) ∧
    DerivedCategory.torAmplitudeIn _ (-1) 0
      (integralCriterionTwoTerm ℓ (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))) ∧
    DerivedCategory.homologyConcentratedIn (-1) 0
      (integralCriterionTwoTerm ℓ (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))) ∧
    (∀ q : ℤ, q ∈ Set.Icc (-1) 0 →
      Nonempty ((DerivedCategory.homologyFunctor _ q).obj
        (integralCriterionTwoTerm ℓ (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))) ≅
        integralCriterionResidue ℓ (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))) ∧
    ¬ DerivedCategory.finiteTorAmplitude _ ((DerivedCategory.TStructure.t.truncGE 0).obj
      (integralCriterionTwoTerm ℓ (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))) := by
  sorry

end AlgebraicGeometry.ProEtale
