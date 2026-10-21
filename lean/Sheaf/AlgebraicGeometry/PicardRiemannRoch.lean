/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import Sheaf.AlgebraicGeometry.RegularCurveDivisorCalculus
public import Sheaf.AlgebraicGeometry.RelativeDifferentialsPullbackMap
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import WeilConjectures.AlgebraicGeometry.Curve.ResidueTrace
public import WeilConjectures.AlgebraicGeometry.Cohomology.CupProduct
public import WeilConjectures.AlgebraicGeometry.Curve.AdelicStructureSheaf
public import WeilConjectures.AlgebraicGeometry.Curve.Divisor
public import WeilConjectures.ZetaSeries
public import WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Modules.GenericRank
public import WeilConjectures.AlgebraicGeometry.Modules.Torsion
public import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Sheaf.AlgebraicGeometry.Curve.ProperProjective
import Sheaf.AlgebraicGeometry.EulerCharZeroDimSupport
import Sheaf.AlgebraicGeometry.GlobalSectionsGeomConnected
import Sheaf.AlgebraicGeometry.Modules.DeterminantShortExact
import Sheaf.AlgebraicGeometry.RegularCurveTorsionfreeFree
import Sheaf.AlgebraicGeometry.TorsionSubsheafQuotient
import Sheaf.AlgebraicGeometry.VectorBundleLineSubbundle
import Sheaf.AlgebraicGeometry.VeryAmpleSeparationCriterion
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerCharProper
import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact
import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor
import WeilConjectures.AlgebraicGeometry.ModuleSupportProperOverBase
import WeilConjectures.AlgebraicGeometry.Modules.Ample
import WeilConjectures.AlgebraicGeometry.Picard.Group
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-! # Riemann–Roch and coherent Serre duality

Source: blueprint, sec-picard-framework/sk-thm-picard-rr/_section.md, including
sk-thm-picard-rr-duality.md, clause (4) (blueprint: sk-thm-picard-rr).

The field-extension clause uses the existing canonical cohomology comparison.
Its differential isomorphism is specified on universal differentials, and the
residue trace commutes with this comparison. Together with functoriality of cup
product and evaluation this says that the displayed duality isomorphism extends
by scalars, rather than merely that its two sides have the same dimension.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

/-- The canonical residue trace with the scalar structure induced by the given
structure morphism, rather than an additional algebra hypothesis.
Source: blueprint sk-thm-picard-rr-duality.md, clause (1)
(blueprint: sk-thm-picard-rr). This is exactly `residueTrace`, specialized to the
canonical `functionFieldAlgebra`; no trace data is chosen. -/
noncomputable def picardRRResidueTrace (k : Type u) [Field k] (X : Scheme.{u})
    [IsIntegral X] [X.Over (Spec (.of k))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))] :
    Module.Dual k ((X ↘ Spec (.of k)).relativeDifferentials.H 1) :=
  letI := functionFieldAlgebra k X
  letI := isFunctionFieldAlgebra_functionFieldAlgebra k X
  residueTrace k X

/-- The canonical comparison between tensor pullback and the existing pullback
used by the cohomology base-change API. It uses the uniquely section-normalized
`tensorPullbackSectionAdjunction` owned by `def-pc-module-pullback`, and compares
left adjoints compatibly with their units.
Source: Stacks Project, Tags 0095 and 02KH (blueprint: sk-thm-picard-rr). -/
noncomputable def picardRRPullbackIso {X Y : Scheme.{u}} (p : X ⟶ Y) :
    Modules.tensorPullback p ≅ Modules.pullback p :=
  (Modules.tensorPullbackSectionAdjunction p).leftAdjointUniq
    (Modules.pullbackPushforwardAdjunction p)

/-- Canonical scalar extension on cohomology, transported to tensor pullback.
Source: Stacks Project, Tag 02KH (blueprint: sk-thm-picard-rr).
The two pullbacks are compared by their adjunction units, so this is exactly
`H.baseChange`, with its output expressed using the tensor construction. -/
noncomputable def picardRRBaseChange (k : Type u) [Field k] (C : Scheme.{u})
    [C.Over (Spec (.of k))] (K : Type u) [Field K] [Algebra k K]
    (M : C.Modules) (q : ℕ) :
    TensorProduct k K (M.H q) →ₗ[K]
      Modules.HOver (Modules.baseChangeSnd (S := K) (C ↘ Spec (.of k)))
        ((Modules.tensorPullback (Modules.baseChangeFst (S := K)
          (C ↘ Spec (.of k)))).obj M) q :=
  letI : (Modules.baseChangedScheme (S := K) (C ↘ Spec (.of k))).Over
      (Spec (.of K)) := ⟨Modules.baseChangeSnd (S := K) (C ↘ Spec (.of k))⟩
  Modules.H.mapLinearMap K
    ((picardRRPullbackIso (Modules.baseChangeFst (S := K)
      (C ↘ Spec (.of k)))).inv.app M) q ∘ₗ
    Modules.H.baseChange (S := K) (C ↘ Spec (.of k)) M q

/-- The field-extension clause of Riemann–Roch and Serre duality.
Source: blueprint sk-thm-picard-rr-duality.md, clause (4)
(blueprint: sk-thm-picard-rr).

`picardRRBaseChange` transports the existing `H.baseChange` to tensor pullback
using the adjunction comparison pinned to its sectionwise unit. The differential
isomorphism sends the pullback of da to d(a). The last equation preserves the residue trace on every
cohomology class, so the induced trace-duality maps commute with extension of
scalars. Smoothness and geometric connectedness give geometric integrality by
the existing theorem; the instance below only supplies that derived fact. -/
def picardRRFieldExtension (k : Type u) [Field k] (C : Scheme.{u})
    [C.Over (Spec (.of k))] [IsSmoothProjectiveCurve (C ↘ Spec (.of k))]
    [GeometricallyConnected (C ↘ Spec (.of k))]
    (K : Type u) [Field K] [Algebra k K] : Prop :=
  letI : GeometricallyIntegral (C ↘ Spec (.of k)) :=
    GeometricallyIntegral.of_smooth_of_geometricallyConnected (C ↘ Spec (.of k))
  letI : (Modules.baseChangedScheme (S := K) (C ↘ Spec (.of k))).Over
      (Spec (.of K)) := ⟨Modules.baseChangeSnd (S := K) (C ↘ Spec (.of k))⟩
  IsSmoothProjectiveCurve (C.baseChangeField k K ↘ Spec (.of K)) ∧
  GeometricallyConnected (C.baseChangeField k K ↘ Spec (.of K)) ∧
  arithmeticGenus K (C.baseChangeField k K) = arithmeticGenus k C ∧
  (∀ (L : C.Modules) [L.IsInvertible],
    ((Modules.tensorPullback (Modules.baseChangeFst (S := K)
      (C ↘ Spec (.of k)))).obj L).degree K = L.degree k ∧
    ((Modules.tensorPullback (Modules.baseChangeFst (S := K)
      (C ↘ Spec (.of k)))).obj L).eulerChar K = L.eulerChar k ∧
    ∀ q : ℕ, Function.Bijective (picardRRBaseChange k C K L q)) ∧
  ∃ e : (Modules.tensorPullback (Modules.baseChangeFst (S := K)
      (C ↘ Spec (.of k)))).obj (C ↘ Spec (.of k)).relativeDifferentials ≅
        (C.baseChangeField k K ↘ Spec (.of K)).relativeDifferentials,
    (∀ (W : C.Opens) (a : Γ(C, W)),
      e.hom.val.app (op (Modules.baseChangeFst (S := K) (C ↘ Spec (.of k)) ⁻¹ᵁ W))
        (Hom.relativeDifferentialsPullbackGenerator (C ↘ Spec (.of k))
          (Modules.baseChangeFst (S := K) (C ↘ Spec (.of k))) W a) =
      (C.baseChangeField k K ↘ Spec (.of K)).relativeDifferentialsDerivation.d
        (X := op (Modules.baseChangeFst (S := K) (C ↘ Spec (.of k)) ⁻¹ᵁ W))
        ((Modules.baseChangeFst (S := K) (C ↘ Spec (.of k))).app W a)) ∧
    (∀ z : (C ↘ Spec (.of k)).relativeDifferentials.H 1,
      picardRRResidueTrace K (C.baseChangeField k K)
        (Modules.H.map e.hom 1
          (picardRRBaseChange k C K (C ↘ Spec (.of k)).relativeDifferentials 1
            (1 ⊗ₜ[k] z))) =
        algebraMap k K (picardRRResidueTrace k C z))

/-- The clauses of Riemann–Roch and coherent Serre duality.
Source: blueprint sk-thm-picard-rr/_section.md (blueprint: sk-thm-picard-rr).
Noetherianity and regularity are derived from smooth projectivity inside this
predicate; they are not additional hypotheses. All its clauses are displayed
explicitly, including arbitrary-dimensional proper schemes in complement (H). -/
def picardRRConclusions (k : Type u) [Field k] (C : Scheme.{u})
    [C.Over (Spec (.of k))] [IsSmoothProjectiveCurve (C ↘ Spec (.of k))]
    [GeometricallyConnected (C ↘ Spec (.of k))] : Prop :=
  letI : IsNoetherian C := isNoetherian_of_locallyOfFiniteType (C ↘ Spec (.of k))
  letI : IsRegular C := IsRegular.of_smooth (C ↘ Spec (.of k))
  (∀ (L : C.Modules) [L.IsInvertible],
    L.eulerChar k = L.degree k + 1 - (arithmeticGenus k C : ℤ) ∧
    L.eulerChar k = (L.finrankH k 0 : ℤ) - (L.finrankH k 1 : ℤ) ∧
    Function.Bijective (Modules.cupPairing (picardRRResidueTrace k C) L) ∧
    (2 * (arithmeticGenus k C : ℤ) - 2 < L.degree k →
      Subsingleton (L.H 1) ∧
      (L.finrankH k 0 : ℤ) = L.degree k + 1 - (arithmeticGenus k C : ℤ)) ∧
    (0 < L.degree k → IsAmple (C ↘ Spec (.of k)) L) ∧
    ∀ D : C.Divisor, Nonempty (D.associatedModule C ≅ L) →
      L.degree k = D.sum (fun x n ↦ n * (C ↘ Spec (.of k)).degreeOver x.val)) ∧
  (∀ f : C.functionFieldˣ,
    (C.div (Additive.ofMul f)).sum
      (fun x n ↦ n * (C ↘ Spec (.of k)).degreeOver x.val) = 0) ∧
  (C ↘ Spec (.of k)).relativeDifferentials.degree k =
    2 * (arithmeticGenus k C : ℤ) - 2 ∧
  (∀ (F : C.Modules), F.IsQuasiCoherentFiniteType →
    F.eulerChar k = (Modules.torsion F).finrankH k 0 +
      (Modules.exteriorSheaf (Modules.torsionQuotient F) F.rank).degree k +
      (F.rank : ℤ) * (1 - (arithmeticGenus k C : ℤ))) ∧
  (∀ (K : Type u) [Field K] [Algebra k K], picardRRFieldExtension k C K) ∧
  (∀ (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    (J : X.IdealSheafData), J.IsInvertible →
    IsAmple (X ↘ Spec (.of k)) J.toModulesᵛ → IsAffine (Scheme.Opens.toScheme J.support.compl))

/-- Riemann–Roch, coherent Serre duality, field extension and the ample complements.
Source: blueprint sk-thm-picard-rr/_section.md and its duality detail
(blueprint: sk-thm-picard-rr).

Proof, following the ten steps of the node:
1. Smooth projectivity gives a regular integral proper curve. Coherent cohomology
   is finite and vanishes above degree one. Geometric connectedness and smoothness
   give H0(O)=k, hence chi(O)=1-g; proper smooth curves are projective by Tag 0A26.
2. regular_curve_divisor_calculus gives the modification sequence at each closed
   point x. Euler additivity and zero-dimensional support give the increment
   [kappa(x):k]. Induction on the sum of absolute coefficients gives divisor RR.
3. Every line bundle is O(D). Principal divisors represent O, hence have degree
   zero. Tensor multiplication identifies divisor degree with Modules.degree.
4. Take the torsion subsheaf T of a coherent F. Its support is zero-dimensional,
   so chi(T)=h0(T); the torsion-free quotient E is a vector bundle of generic rank.
5. Induct on the rank of E using a saturated line subbundle, vector-bundle quotient,
   determinant multiplicativity and Euler additivity. Rank zero has determinant O.
   This proves the stated coherent formula with exactly the torsion determinant degree.
6. Smooth differentials have rank one. Serre duality with the residue trace gives
   the perfect cup pairing. Apply duality to O in both degrees to obtain
   h0(omega)=g, h1(omega)=1, and RR gives deg(omega)=2g-2.
7. If deg(L)>2g-2, omega tensor L-dual has negative degree. A nonzero section
   would give an effective zero divisor of nonnegative degree. Duality therefore
   kills H1(L), and RR gives the formula for h0(L).
8. Flat cohomology base change preserves the finite dimensions, Euler characteristic,
   genus and degree. The universal differential comparison identifies omega after
   base change, and residue trace compatibility gives scalar extension of duality.
9. For positive degree, extend to an algebraic closure and choose m with
   m deg(L)>=2g+1. The vanishing formula for twists by P and P+Q (also P=Q)
   gives point and tangent separation. Very ampleness descends, hence L is ample.
10. For any proper k-scheme and effective Cartier ideal J, apply
    isAffine_compl_of_isAmple_dual_toModules to the open complement of J.support.
    This includes the empty divisor whenever its dual ideal module is ample. -/
theorem picard_riemannRoch (k : Type u) [Field k] (C : Scheme.{u})
    [C.Over (Spec (.of k))] [IsSmoothProjectiveCurve (C ↘ Spec (.of k))]
    [GeometricallyConnected (C ↘ Spec (.of k))] : picardRRConclusions k C := by
  sorry

end AlgebraicGeometry.Scheme
