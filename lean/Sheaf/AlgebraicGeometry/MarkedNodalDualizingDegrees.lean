/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.AlgebraicGeometry.NodalDualizingDatum
public import Sheaf.AlgebraicGeometry.MultipointedCurveModification
public import Sheaf.AlgebraicGeometry.RelativeDifferentialsPullbackMap
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import Mathlib.Topology.KrullDimension

import WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.RingTheory.CompleteIntersectionOverField
import WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersectionPresentation
import WeilConjectures.AlgebraicGeometry.Modules.Dual
import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
import WeilConjectures.AlgebraicGeometry.Curve.ClosedPoint
import Sheaf.TraceFormula.GenusZeroSmoothProperLine
import Sheaf.AlgebraicGeometry.NodalCurveLCICriterion
import Sheaf.AlgebraicGeometry.SemistableMarkedBaseChange
import Sheaf.AlgebraicGeometry.UnramifiedOverFieldLocalCriterion
import WeilConjectures.RingTheory.GlobalCompleteIntersectionPrincipalLocalization
import WeilConjectures.RingTheory.RelativeGlobalCompleteIntersectionLocalRegularSequence
import WeilConjectures.RingTheory.SyntomicAtPrimeRelativeGlobalCompleteIntersection
import WeilConjectures.AlgebraicGeometry.UnramifiedQuasiFinite
import Sheaf.AlgebraicGeometry.FlatLCICanonicalAdjunction
import Sheaf.AlgebraicGeometry.NodalNormalizationAdjunction
import Sheaf.TraceFormula.NoIsolatedContractedFibreComponent

/-!
# Marked nodal dualizing degrees

Source: Temkin, Stable modification of relative curves, §1.2(a),(b), pp. 2--3, and
Theorem 1.1, contracted-subcurve calculation
(blueprint: lem-trf-marked-nodal-dualizing-degrees).

The dualizing datum includes the Jacobian-normalized fundamental class and the actual
local Ext modules. Components below are integral closed subschemes with irreducible-component
image, and all numerical invariants are taken on their canonical normalizations.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-- The marked line is the tensor product with the dual of the actual marking ideal.
Source: Temkin §1.2(b) (blueprint: lem-trf-marked-nodal-dualizing-degrees). -/
def markedNodalLine {T : Scheme.{u}} (P : MultipointedCurve T) (omega : P.X.Modules) :
    P.X.Modules :=
  omega ⊗ₘ P.i.ker.toModulesᵛ

/-- Degree of the pullback to the canonical normalization of an integral component, with
its induced field structure map. Source: Temkin §1.2(b) and Theorem 1.1
(blueprint: lem-trf-marked-nodal-dualizing-degrees). -/
def markedNodalComponentDegree (Ω : Type u) [Field Ω] {Y : Scheme.{u}}
    (Z : Scheme.{u}) [IsIntegral Z] (j : Z ⟶ Y) (s : Z ⟶ Spec (.of Ω))
    (L : Y.Modules) : ℤ :=
  @Scheme.Modules.degree Ω _ Z.normalization ⟨Z.fromNormalization ≫ s⟩
    ((Scheme.Modules.tensorPullback (Z.fromNormalization ≫ j)).obj L)

/-- The genus is `dim H¹(O)` on the canonical normalization with its induced field
structure. Source: Temkin §1.2(b) (blueprint: lem-trf-marked-nodal-dualizing-degrees). -/
def markedNodalComponentGenus (Ω : Type u) [Field Ω] (Z : Scheme.{u}) [IsIntegral Z]
    (s : Z ⟶ Spec (.of Ω)) : ℕ :=
  @Scheme.arithmeticGenus Ω _ Z.normalization ⟨Z.fromNormalization ≫ s⟩

/-- Marked and ambient nodal preimages on the canonical normalization. A self-node has
two distinct preimages; a node joining another component contributes its one branch here.
Source: Temkin §1.2(b) and Theorem 1.1
(blueprint: lem-trf-marked-nodal-dualizing-degrees). -/
def markedNodalBranches {T : Scheme.{u}} (P : MultipointedCurve T)
    (Ω : Type u) [Field Ω] (t : Spec (.of Ω) ⟶ T)
    (Z : Scheme.{u}) [IsIntegral Z] (j : Z ⟶ pullback P.x t) :
    Set Z.normalization :=
  (Z.fromNormalization ≫ j) ⁻¹'
    (Set.range (P.markingBaseChange t) ∪
      {y | y ∉ (pullback.snd P.x t).smoothLocus})

/-- All conclusions of the marked nodal degree lemma, using the source of a morphism of
multipointed curves. No properness or separatedness over the structural base is assumed.
Source: Temkin §1.2(a),(b), pp. 2--3, and Theorem 1.1
(blueprint: lem-trf-marked-nodal-dualizing-degrees). -/
structure MarkedNodalDualizingDegreesData {T : Scheme.{u}}
    (P : MultipointedCurve T) where
  omega : P.X.Modules
  dualizing : NodalDualizingDatum P.x omega
  cartier : IsEffectiveCartierCenter P.i
  marked_invertible : (markedNodalLine P omega).IsInvertible
  canonical : ∀ (F : P.X.Modules) (D : NodalDualizingDatum P.x F),
    ∃! e : omega ≅ F, dualizing.fundamental ≫ e.hom = D.fundamental
  base_change : ∀ (T' : Scheme.{u}) (q : T' ⟶ T),
    ∃ D : NodalDualizingDatum (pullback.snd P.x q)
        ((Scheme.Modules.tensorPullback (pullback.fst P.x q)).obj omega),
      (∀ (W : P.X.Opens) (a : Γ(P.X, W)),
        ((Scheme.Modules.tensorPullback (pullback.fst P.x q)).map
          dualizing.fundamental).val.app (op (pullback.fst P.x q ⁻¹ᵁ W))
          (P.x.relativeDifferentialsPullbackGenerator (pullback.fst P.x q) W a) =
        D.fundamental.app (pullback.fst P.x q ⁻¹ᵁ W)
          ((pullback.snd P.x q).relativeDifferentialsDerivation.d
            (X := op (pullback.fst P.x q ⁻¹ᵁ W)) ((pullback.fst P.x q).app W a))) ∧
      IsEffectiveCartierCenter (P.markingBaseChange q) ∧
      Nonempty ((Scheme.Modules.tensorPullback (pullback.fst P.x q)).obj
        (markedNodalLine P omega) ≅
          ((Scheme.Modules.tensorPullback (pullback.fst P.x q)).obj omega) ⊗ₘ
            (P.markingBaseChange q).ker.toModulesᵛ)
  normalization_degree :
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T)
      (Z : Scheme.{u}) [IsIntegral Z] (j : Z ⟶ pullback P.x t),
      IsClosedImmersion j → Set.range j ∈ irreducibleComponents (pullback (C := Scheme) P.x t) →
      IsProper (j ≫ pullback.snd P.x t) →
      (markedNodalBranches P Ω t Z j).Finite ∧
      markedNodalComponentDegree Ω Z (j ≫ pullback.fst P.x t)
          (j ≫ pullback.snd P.x t) (markedNodalLine P omega) =
        (2 * markedNodalComponentGenus Ω Z (j ≫ pullback.snd P.x t) : ℤ) - 2 +
          ((markedNodalBranches P Ω t Z j).ncard : ℤ)

/-- Marked dualizing line, arbitrary base change, normalized-component degree and positivity.

Source: Temkin §1.2(a),(b), pp. 2--3, and Theorem 1.1
(blueprint: lem-trf-marked-nodal-dualizing-degrees).

Proof, following the node's eight steps:
1. `lem-trf-semistable-marked-base-change` gives nodal fibres and etale smooth markings
   after any base change. `lem-trf-unramified-over-field-local-criterion` makes each
   geometric marking point reduced, of multiplicity one.
2. `lem-trf-nodal-curve-lci-criterion` and the syntomic-at-prime relative complete-intersection
   criterion give local polynomial presentations. Principal localization preserves complete
   intersections. Pure relative dimension one makes the number of equations `n-1`; the
   local-regular-sequence lemma supplies regularity.
3. `lem-trf-flat-lci-canonical-adjunction` constructs the determinant line and its normalized
   fundamental class, identifies its pushforward with Ext, and gives cocycle-compatible
   gluing on arbitrary overlaps and arbitrary base change, without separatedness.
4. `lem-trf-smooth-marking-cartier` gives the actual Cartier ideal and its dual twist; these
   and their tensor product commute with base change.
5. `lem-trf-nodal-normalization-adjunction` identifies the normalized restriction with
   differentials twisted by ambient nodal branches and marked preimages. Self-nodes count
   twice; boundary nodes count once on this component. `lem-sc-point-cartier` applies.
6. `lem-sc-riemann-roch`, `lem-sc-canonical-degree` and `lem-pc-degree-base-change` identify
   the Euler degree with classical degree and give `2g-2+n`, including empty divisors.
7. A dimension-one integral component of the fibre over the target curve is a proper
   contracted component of the structural geometric fibre, by proper base change.
   `lem-trf-no-isolated-contracted-fibre-component` supplies at least one boundary branch.
8. For genus at least two the degree is positive; for genus one the boundary gives `n>0`.
   In genus zero `lem-trf-genus-zero-smooth-proper-line` identifies the normalization with
   the projective line. A self-node supplies two more branches; otherwise the component
   itself is a projective line, and stability supplies more than two special points.
   Thus in either rational case `n>=3`, giving strict positivity. -/
theorem marked_nodal_dualizing_degrees
    (T : Scheme.{u}) [IsIntegral T] [IsNoetherian T]
    (C P : MultipointedCurve T) (η : T) (hη : IsGenericPoint η Set.univ)
    (hgenericCurve : Smooth (C.x.fiberToSpecResidueField η))
    (hgenericMarking : Etale (C.d.fiberToSpecResidueField η))
    (f : P.Hom C) (hstable : f.IsStable (T.fromSpecResidueField η)) :
    ∃ D : MarkedNodalDualizingDegreesData P,
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (z : Spec (.of Ω) ⟶ C.X)
        (Z : Scheme.{u}) [IsIntegral Z] (j : Z ⟶ pullback f.curve z),
        IsClosedImmersion j →
        Set.range j ∈ irreducibleComponents (pullback (C := Scheme) f.curve z) →
        topologicalKrullDim Z = 1 →
        0 < markedNodalComponentDegree Ω Z (j ≫ pullback.fst f.curve z)
          (j ≫ pullback.snd f.curve z) (markedNodalLine P D.omega) := by
  sorry

end AlgebraicGeometry
