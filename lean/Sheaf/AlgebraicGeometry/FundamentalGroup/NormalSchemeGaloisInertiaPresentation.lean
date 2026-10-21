/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q46
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.Topology.Algebra.Group.Basic
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.GaloisAction
public import Sheaf.AlgebraicGeometry.FundamentalGroup.FLCFiber
import Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence
import WeilConjectures.AlgebraicGeometry.EtaleFieldGsets
import WeilConjectures.AlgebraicGeometry.Morphisms.NormalIntegralGenericHomFull
import Sheaf.RingTheory.HenselianFiniteEtaleEquivalence
import WeilConjectures.FieldTheory.OpenSubgroupFixedField
import WeilConjectures.FieldTheory.EtaleFieldGaloisClassification
import Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Etale.Field
import Mathlib.Topology.Algebra.ClopenNhdofOne

/-! # Absolute Galois presentation of the fundamental group of a normal integral scheme

Source: Stacks Project, Tag 0BTD, lemma-normal-pione-quotient-inertia, (1) = (3),
and its preceding setup; surjectivity in Tag 0BQM
(blueprint: lem-dl-a1-normal-scheme-galois-inertia-presentation).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale

/-- The function-field Galois group maps continuously and surjectively onto the fundamental
 group of a normal integral scheme, with kernel the closed normal closure of all strict
 henselian inertia groups. The strict henselizations are domains and their fraction fields
 admit the required compatible embeddings into the separable closure.

Source: Stacks Project, Tags 0BTD and 0BQM
(blueprint: lem-dl-a1-normal-scheme-galois-inertia-presentation).

`G` is any small fundamental-group model of the existing finite-etale fibre functor.
`exists_fiber_flc_equivalence` identifies this, with its topology and action, with the
natural automorphisms of `flcFiber`, as specified by def-galois-fibre-functor.
No arbitrary homomorphism is assumed: the displayed equation with
`galoisToFundamentalGroup` specifies the map on every Galois element by its action on
geometric generic fibres. The preceding unique-extension clause supplies its lift to
`Ωbar`, including in positive characteristic.

The geometric points `sx x` are arbitrary points above `x`, so all residue-closure choices
are allowed. The diagram over `X` in the embedding clauses says that the fraction-field
embedding extends the canonical local-ring inclusion into the function field; since
`X.functionField` is the fraction field of each stalk, this is exactly K-compatibility.
It avoids imposing an unrelated algebra structure on the strict henselization.
`fixingSubgroup` fixes every element of the image of its fraction field.

Proof, following the node's ten steps:
1. Each stalk is a normal local domain. Lying over and the integral-prime-over-maximal
lemma give a prime in its integral closure in Ω. The local henselian/global inertia
comparison gives the domain assertion and compatible fraction-field embeddings.
2. Automorphisms of Ω extend uniquely to Ωbar across the purely inseparable extension.
On finite-etale fibres precompose a lift with Spec of that automorphism. Naturality and
Spec's contravariance give the displayed homomorphism; evaluation on finite discrete
fibres gives continuity and identifies it with generic-point functoriality.
3. Its image is compact by the Krull finite-limit theorem and closed in the profinite
fundamental group. A proper open overgroup would give a finite coset cover with a
Galois-fixed generic point. Generic full faithfulness extends this point to a section,
forcing that coset to be fixed by the whole fundamental group, a contradiction.
4. A finite-etale cover splits over every strict henselization by its strict henselian
local structure and the henselian finite-etale equivalence. Consequently each fixing
subgroup acts trivially on every fibre. Their closed normal closure lies in the kernel.
5. For an open normal overgroup U of that closure, its fixed field L is finite separable.
Normality of U and extension of field embeddings show that L/K is Galois.
6. Any two compatible embeddings of a strict henselian fraction field into Ω are
conjugate, by extension of embeddings and bijectivity of algebraic endomorphisms.
Localization of integral closure and the local inertia comparison therefore put all
geometric inertia groups into the same closed normal closure.
7. On an affine open Spec A, normal stalks imply that A is integrally closed in K.
For its integral closures B in L and C in Ω, lying over and inertia restriction
surjectivity show that every inertia subgroup of Gal(L/K) at a prime of B is trivial.
8. The finite Galois fixed-field theorem identifies B^Gal(L/K) with A. The inertia
invariants theorem implies that Spec B is etale over Spec A. It is integral and locally
of finite type, hence finite. Relative normalization glues these affine covers to a
finite-etale cover of X, without any Noetherian hypothesis.
9. Its generic fibre is Spec L by localization of integral closure. The stabilizer of
the inclusion L into Ω is U, so the kernel of the fundamental-group map lies in U.
10. A closed normal subgroup of a profinite group is the intersection of its open normal
overgroups (take cores of open overgroups). Steps 4 and 9 give the asserted equality.
The conjugacy in step 6 proves it for every family of compatible embeddings. -/
theorem normalScheme_galois_inertia_presentation
    {X : Scheme.{u}} [IsIntegral X]
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    {Ω Ωbar : Type u} [Field Ω] [Field Ωbar]
    [Algebra X.functionField Ω] [IsSepClosure X.functionField Ω]
    [Algebra Ω Ωbar] [IsAlgClosure Ω Ωbar] [IsAlgClosed Ωbar]
    [Algebra X.functionField Ωbar] [IsScalarTower X.functionField Ω Ωbar]
    (Ωx : X → Type u) [∀ x, Field (Ωx x)] [∀ x, IsAlgClosed (Ωx x)]
    (sx : ∀ x, Spec (.of (Ωx x)) ⟶ X)
    (hsx : ∀ x, (X.SpecToEquivOfField (Ωx x) (sx x)).1 = x)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((fiber (pointOfAlgebra (K := X.functionField) Ωbar
      (X.fromSpecStalk (genericPoint X)))).obj P)]
    [IsFundamentalGroup (fiber (pointOfAlgebra (K := X.functionField) Ωbar
      (X.fromSpecStalk (genericPoint X)))) G] :
    (∀ x, IsDomain (strictHenselizationRing (sx x))) ∧
    (∀ x, ∃ j : FractionRing (strictHenselizationRing (sx x)) →+* Ω,
      Function.Injective j ∧
      Spec.map (CommRingCat.ofHom (j.comp (algebraMap (strictHenselizationRing (sx x))
        (FractionRing (strictHenselizationRing (sx x)))))) ≫
          strictHenselizationStructuralMap (sx x) =
        Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
          X.fromSpecStalk (genericPoint X)) ∧
    (∀ σ : Gal(Ω / X.functionField), ∃! σbar : Gal(Ωbar / X.functionField),
      ∀ a : Ω, σbar (algebraMap Ω Ωbar a) = algebraMap Ω Ωbar (σ a)) ∧
    ∃ q : Gal(Ω / X.functionField) →* G,
      (∀ (σ : Gal(Ω / X.functionField)) (σbar : Gal(Ωbar / X.functionField)),
        (∀ a : Ω, σbar (algebraMap Ω Ωbar a) = algebraMap Ω Ωbar (σ a)) →
        q σ = galoisToFundamentalGroup (K := X.functionField) (X.fromSpecStalk (genericPoint X))
          (Iso.refl _) G σbar) ∧
      Continuous q ∧ Function.Surjective q ∧
      ∀ j : (x : X) → FractionRing (strictHenselizationRing (sx x)) →+* Ω,
        (∀ x, Function.Injective (j x)) →
        (∀ x, Spec.map (CommRingCat.ofHom ((j x).comp (algebraMap (strictHenselizationRing (sx x))
            (FractionRing (strictHenselizationRing (sx x)))))) ≫
            strictHenselizationStructuralMap (sx x) =
          Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
            X.fromSpecStalk (genericPoint X)) →
        q.ker = (Subgroup.normalClosure (⋃ x,
          (fixingSubgroup Gal(Ω / X.functionField)
            (Set.range (j x)) : Set Gal(Ω / X.functionField)))).topologicalClosure := by
  sorry

end AlgebraicGeometry.Scheme.FiniteEtale
