/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CurveGenus
public import Sheaf.AlgebraicGeometry.Curve.VectorBundlePrincipalParts
public import Sheaf.RingTheory.TateResidue.DVRResidueCalculus
public import WeilConjectures.AlgebraicGeometry.Curve.ResidueTrace
public import WeilConjectures.AlgebraicGeometry.ScalarGlobalSectionsComparison
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.Modules.Ext
import Sheaf.AlgebraicGeometry.CurveBaseChangeRelativeDimensionOne
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import Sheaf.AlgebraicGeometry.ProperDimZeroFiniteOverField
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.RingTheory.TraceFormEtaleField
import WeilConjectures.AlgebraicGeometry.ScalarCupZeroGlobalSections
import WeilConjectures.AlgebraicGeometry.DensePoints
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum
import Sheaf.Paper.SupportDimensionCohomologyVanishing
import WeilConjectures.AlgebraicGeometry.ZariskiModuleAbelianCohomologyNatural
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import Sheaf.AlgebraicGeometry.GlobalSectionsLeftExact
import Sheaf.AlgebraicGeometry.LocallyFreeExtCohomology
public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
import WeilConjectures.AlgebraicGeometry.ScalarExtCupDegreeZero
import WeilConjectures.AlgebraicGeometry.ScalarCupCoefficientNaturality
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Kaehler.TensorProduct

/-! # Serre duality with the normalized trace in dimensions zero and one

Source: blueprint main-20261015, sec-picard-framework/sk-thm-picard-duality;
Tate, Residues of differentials on curves, §3–4 (blueprint: sk-thm-picard-duality).

The two dimension cases together cover pure dimension n ∈ {0,1}. Cohomology is
module-derived cohomology with its recorded scalar restriction, extended by zero
in negative degrees. In dimension one the trace is normalized on every finite
clopen decomposition into integral components, including the empty decomposition.
-/

@[expose] public section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- Extend the recorded module cohomology to integer degrees by zero below zero.
Source: blueprint sk-thm-picard-duality, negative-degree convention
(blueprint: sk-thm-picard-duality). -/
noncomputable def picardCohomologyZ (f : X ⟶ Spec (.of k)) (F : X.Modules) (q : ℤ) :
    ModuleCat.{u} k :=
  if 0 ≤ q then scalarCohomology f F q.toNat else ModuleCat.of k PUnit

/-- Extend the recorded coefficient map by the zero map in negative degrees.
Source: blueprint sk-thm-picard-duality, naturality and negative-degree convention
(blueprint: sk-thm-picard-duality). -/
noncomputable def picardCohomologyZMap (f : X ⟶ Spec (.of k))
    {F G : X.Modules} (φ : F ⟶ G) (q : ℤ) :
    picardCohomologyZ f F q → picardCohomologyZ f G q := by
  classical
  unfold picardCohomologyZ
  split
  · exact scalarCohomologyMap f φ q.toNat
  · exact fun _ ↦ 0

/-- Cup product, evaluation, and the given trace, with the zero pairing whenever
one of the two degrees is negative. The casts only identify equal integer degrees.
Source: blueprint sk-thm-picard-duality, displayed trace pairing
(blueprint: sk-thm-picard-duality). -/
noncomputable def picardTracePairing (f : X ⟶ Spec (.of k)) (ω : X.Modules) (n : ℕ)
    (t : Module.Dual k (scalarCohomology f ω n)) (F : X.Modules) (q : ℤ)
    (a : picardCohomologyZ f F q)
    (b : picardCohomologyZ f (dual F ⊗ ω) ((n : ℤ) - q)) : k := by
  classical
  letI : MonoidalCategory (SheafOfModules.{u} X.ringCatSheaf) :=
    SheafOfModules.monoidalCategory X.sheaf
  by_cases h : 0 ≤ q ∧ 0 ≤ (n : ℤ) - q
  · have a' : scalarCohomology f F q.toNat := by
      simpa only [picardCohomologyZ, if_pos h.1] using a
    have b' : scalarCohomology f (dual F ⊗ ω) ((n : ℤ) - q).toNat := by
      simpa only [picardCohomologyZ, if_pos h.2] using b
    exact t (cast (congrArg (fun j ↦ ↥(scalarCohomology f ω j))
      (by omega : q.toNat + ((n : ℤ) - q).toNat = n))
      (scalarCohomologyMap f (evalTensor F ω) _
        (scalarCohomologyCup f F (dual F ⊗ ω) _ _ a' b')))
  · exact 0

/-- Perfection in every integer degree and the naturality equation for this exact
cup/evaluation/trace pairing. The equivalence sends b to the functional a ↦ ⟨a,b⟩.
Source: blueprint sk-thm-picard-duality, perfection and naturality clauses
(blueprint: sk-thm-picard-duality). -/
def IsPicardTraceDuality (f : X ⟶ Spec (.of k)) (ω : X.Modules) (n : ℕ)
    (t : Module.Dual k (scalarCohomology f ω n)) : Prop :=
  (∀ (F : X.Modules) [F.IsFiniteLocallyFree] (q : ℤ),
    ∃ e : picardCohomologyZ f (dual F ⊗ ω) ((n : ℤ) - q) ≃ₗ[k]
        Module.Dual k (picardCohomologyZ f F q),
      ∀ b a, e b a = picardTracePairing f ω n t F q a b) ∧
  ∀ (F G : X.Modules) [F.IsFiniteLocallyFree] [G.IsFiniteLocallyFree]
    (φ : F ⟶ G) (q : ℤ) (a : picardCohomologyZ f F q)
    (b : picardCohomologyZ f (dual G ⊗ ω) ((n : ℤ) - q)),
    picardTracePairing f ω n t G q (picardCohomologyZMap f φ q a) b =
      picardTracePairing f ω n t F q a
        (picardCohomologyZMap f (dualMap φ ▷ ω) ((n : ℤ) - q) b)

/-- The canonical differential coefficient map for tensor pullback. It is the
adjoint of the universal derivation map, followed by the stated equality over k.
Source: blueprint sk-thm-picard-duality, restriction to components; Stacks Tag 01UM
(blueprint: sk-thm-picard-duality). -/
noncomputable def picardDifferentialPullback {Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (j : Y ⟶ X) (h : j ≫ f = g) :
    (tensorPullback j).obj f.relativeDifferentials ⟶ g.relativeDifferentials :=
  ((Classical.choose (exists_tensorPullbackAdjunction j)).homEquiv _ _).symm
    ((f.relativeDifferentialsHomEquiv _).symm (f.pushforwardDerivation j)) ≫
      (Hom.relativeDifferentialsCongr (j ≫ f) h).hom

/-- Restrict a differential cohomology class to a component, using canonical
cohomology pullback and the universal differential coefficient map.
Source: blueprint sk-thm-picard-duality, componentwise residue trace
(blueprint: sk-thm-picard-duality). -/
noncomputable def picardDifferentialCohomologyPullback {Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (j : Y ⟶ X) (h : j ≫ f = g)
    (z : scalarCohomology f f.relativeDifferentials 1) :
    scalarCohomology g g.relativeDifferentials 1 :=
  scalarCohomologyMap g (picardDifferentialPullback f g j h) 1
    (scalarCohomologyPullback f g j h f.relativeDifferentials 1 z)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

open Modules

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- Serre duality in pure dimension zero, with the finite étale algebra trace.
Source: blueprint sk-thm-picard-duality, n = 0
(blueprint: sk-thm-picard-duality).

Proof (node steps 1–3,9): properness and finite type make X Noetherian; smoothness
in relative dimension zero makes it finite étale and affine. Global sections of
F are finite projective over A = Γ(X,O_X). The étale trace form is perfect.
Split a finite free module onto this projective module; the perfect free trace
pairing restricts to its orthogonal summand. Degree-zero cup is tensoring global
sections, so evaluation gives precisely this pairing. Higher cohomology vanishes
by the dimension bound, and negative cohomology is zero. Evaluation commutes with
φ and its dual, giving naturality. The empty finite algebra gives the zero trace.
-/
theorem picard_duality_zero
    [SmoothOfRelativeDimension 0 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))] :
    ∃ t : Module.Dual k (scalarCohomology (X ↘ Spec (.of k))
        (SheafOfModules.unit X.ringCatSheaf) 0),
      (∀ z, t z = @Algebra.trace k Γ(X, ⊤) _ _
        (globalSectionsRingHom k (X := X)).toAlgebra
        (scalarGlobalSectionsEquiv (X ↘ Spec (.of k))
          (SheafOfModules.unit X.ringCatSheaf) z)) ∧
      IsPicardTraceDuality (X ↘ Spec (.of k))
        (SheafOfModules.unit X.ringCatSheaf) 0 t := by
  sorry

/-- Serre duality in pure dimension one with the sum of Tate residue traces.
The normalization is required for every finite disjoint integral-component
presentation. IsColimit of the cofan is the disjoint-union identification;
the empty index set gives the empty scheme and the zero trace.
Source: blueprint sk-thm-picard-duality, n = 1; Tate §3–4
(blueprint: sk-thm-picard-duality).

Proof (node steps 1–2,4–9): smooth proper curves are Noetherian and regular.
Their finitely many connected components are open, closed and integral. Module
sheaves, resolutions, cohomology, duals and cups decompose componentwise.
On an integral component the canonical module is invertible and coherent
cohomology is finite dimensional and vanishes above one. Principal parts give
the flasque residue resolution. The local Tate residue kills regular forms;
adelic reciprocity kills the diagonal rational forms, so summing residues descends
to H¹. The separable-point uniformizer formula gives a nonzero trace, without
assuming k perfect or omitting inseparable closed points. Extend scalars to an
algebraic closure, apply the existing projective-line curve-duality route there,
and use flat coherent base change to descend the dimension equality. A nonzero
map F → ω is generically surjective; its cokernel has zero-dimensional support.
The two kernel/image exact sequences and cohomological dimension imply that its
map on H¹ is surjective. Thus b ↦ t H¹(b) is injective, and the dimension equality
makes it bijective. The degree-zero cup formulas identify it with cup/evaluation.
Apply the same argument to Fᵛ ⊗ ω and biduality for degree zero. Other integer
degrees vanish. Sum the component pairings. Coefficient naturality of cup and
λ(φ(s)) = (λ ∘ φ)(s) give the displayed naturality equation.
-/
theorem picard_duality_one
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))] :
    ∃ t : Module.Dual k (scalarCohomology (X ↘ Spec (.of k))
        (X ↘ Spec (.of k)).relativeDifferentials 1),
      (∀ (I : Type u) [Fintype I] (Y : I → Scheme.{u})
        [∀ i, IsIntegral (Y i)] [∀ i, (Y i).Over (Spec (.of k))]
        [∀ i, Algebra k (Y i).functionField] [∀ i, IsFunctionFieldAlgebra k (Y i)]
        [∀ i, SmoothOfRelativeDimension 1 (Y i ↘ Spec (.of k))]
        [∀ i, IsProper (Y i ↘ Spec (.of k))]
        (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)]
        (h : ∀ i, j i ≫ (X ↘ Spec (.of k)) = (Y i ↘ Spec (.of k)))
        (_hc : IsColimit (Cofan.mk X j))
        (z : scalarCohomology (X ↘ Spec (.of k))
          (X ↘ Spec (.of k)).relativeDifferentials 1),
        t z = ∑ i, residueTrace k (Y i)
          (moduleCohomologyExtResolutionEquiv (Y i)
            (Y i ↘ Spec (.of k)).relativeDifferentials 1
            (picardDifferentialCohomologyPullback (X ↘ Spec (.of k))
              (Y i ↘ Spec (.of k)) (j i) (h i) z))) ∧
      IsPicardTraceDuality (X ↘ Spec (.of k))
        (X ↘ Spec (.of k)).relativeDifferentials 1 t := by
  sorry

/-- The structure-sheaf specialization, including disconnected and empty curves.
Source: blueprint sk-thm-picard-duality, final displayed isomorphism
(blueprint: sk-thm-picard-duality).

Proof (node step 9): put F = O_X and q = n = 1 in the perfect pairing.
Use the canonical identification O_Xᵛ ⊗ ω_X ≅ ω_X and invert the resulting
linear equivalence. The construction works componentwise, including the empty sum.
-/
theorem picard_duality_structureSheaf
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))] :
    Nonempty (Module.Dual k (scalarCohomology (X ↘ Spec (.of k))
        (SheafOfModules.unit X.ringCatSheaf) 1) ≃ₗ[k]
      scalarCohomology (X ↘ Spec (.of k))
        (X ↘ Spec (.of k)).relativeDifferentials 0) := by
  sorry

/-- Equality of geometric and cohomological genus.
Source: blueprint sk-thm-picard-duality, final sentence
(blueprint: sk-thm-picard-duality).

Proof (node step 9): put F = O_X and q = n = 1 in the perfect pairing. The
canonical identification O_Xᵛ ⊗ ω_X = ω_X gives the displayed equivalence.
For an algebraically closed base, take dimensions and use the genus definition
of sk-def-curve and the degree-zero global-section identification.
-/
theorem picard_duality_genus [IsConnectedCurve (X ↘ Spec (.of k))]
    [Smooth (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))] :
    IsAlgClosed k → (X ↘ Spec (.of k)).genus =
      Module.finrank k (scalarCohomology (X ↘ Spec (.of k))
        (SheafOfModules.unit X.ringCatSheaf) 1) := by
  sorry

end AlgebraicGeometry.Scheme
