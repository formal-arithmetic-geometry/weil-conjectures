module

public import Sheaf.CategoryTheory.CondensedNormalInvariantData
public import Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus
import Sheaf.CategoryTheory.CondensedSplitCosetInduction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-! # Open normal quotient actions and K-injective models

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3),
agent-formulated input extracted from the normal-subgroup comparison, steps 1–4
(blueprint: lem-sfb-open-normal-action-injective-models).

The structural Grothendieck action categories and normalized full-invariant family
are the hypotheses already specified by the node. Quotient actions, K-injective
preservation, resolutions, and the normalized derived comparison are conclusions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CondensedBar (Ring)
namespace Profinite.CondensedAction

variable [C : NormalComparisonCategories.{u}] [V : NormalInvariantFamily.{u}]

/-- The open normal quotient is finite discrete and has a continuous set section.
Source: direct-images paragraph (3), agent-formulated quotient input
(blueprint: lem-sfb-open-normal-action-injective-models).
Proof: the open cosets cover the compact group, so finitely many suffice. The quotient
is discrete since each coset is open. Choose representatives; every map out of this
finite discrete quotient is continuous. -/
theorem openNormalQuotientSection (G : ProfiniteGrp.{u}) (K : OpenNormalSubgroup G) :
    Finite (G ⧸ K.toSubgroup) ∧ DiscreteTopology (G ⧸ K.toSubgroup) ∧
      ∃ s : C(G ⧸ K.toSubgroup, G),
        Function.RightInverse s (QuotientGroup.mk : G → G ⧸ K.toSubgroup) := by
  sorry

/-- Kernel restriction preserves K-injective complexes, also for infinite L.
Source: direct-images paragraph (3), agent-formulated quotient input
(blueprint: lem-sfb-open-normal-action-injective-models).
Proof: identify (G×L)/(K×1) with (G/K)×L using the continuous quotient section.
Apply lem-sfb-condensed-split-coset-induction to obtain an exact additive left adjoint
to the actual restriction k ↦ (k,1). Apply
lem-weil-pbc-right-adjoint-preserves-kinjective. -/
@[instance] theorem openNormalKernelPreserves : NormalKernelPreserves.{u} := by
  sorry

/-- Full invariants preserve K-injectives for every profinite group.
Source: direct-images paragraph (3), agent-formulated quotient input
(blueprint: lem-sfb-open-normal-action-injective-models).
Proof: trivial inflation is exact and additive by the structural restriction calculus;
its normalized right adjoint is full invariants. Apply
lem-weil-pbc-right-adjoint-preserves-kinjective. -/
theorem openNormalFullInvariantsPreserves (A : Ring.{u}) (P : ProfiniteGrp.{u}) :
    (V.invariants A P).functor.PreservesKInjectiveComplexes := by
  sorry

/-- The kernel-fixed internal submodules carry the residual quotient action, its
normalized inflation adjunction, and K-injective preservation.
Source: direct-images paragraph (3), agent-formulated quotient input
(blueprint: lem-sfb-open-normal-action-injective-models).
Proof: fixed sections are linear and stable under restriction and glue by separatedness.
Act through any continuous quotient section. Normality preserves fixedness, and two
lifts differ by a kernel element, so the action is independent of the lift and satisfies
the group law. Restrict equivariant maps. Transpose by restricting the codomain to fixed
sections; inverse transpose composes with their inclusion. Exact quotient inflation and
lem-weil-pbc-right-adjoint-preserves-kinjective give K-injective preservation. -/
theorem openNormalQuotientExists (A : Ring.{u}) (G L : ProfiniteGrp.{u})
    (K : OpenNormalSubgroup G) : Nonempty (NormalQuotient A G L K) := by
  sorry

/-- The ordinary identities UT = Γ_K r and Γ_(G×L) = Γ_(Q×L) T are identified by their
invariant inclusions, on objects and maps, with the normalized left inflation identity.
Source: direct-images paragraph (3), agent-formulated quotient input
(blueprint: lem-sfb-open-normal-action-injective-models).
Proof: both sides of the first identity have precisely the same kernel-fixed sections.
A fully fixed section is kernel-fixed and fixed by all quotient lifts; conversely these
two conditions imply full fixedness. The inclusions coincide, so the identifications
are natural on equivariant maps. Trivial inflation followed by quotient inflation is
the identical trivial action. -/
theorem openNormalComparisonExists (A : Ring.{u}) (G L : ProfiniteGrp.{u})
    (K : OpenNormalSubgroup G) [T : NormalQuotient A G L K] :
    Nonempty (NormalDerivedComparison A G L K) := by
  sorry

/-- Every unbounded action complex admits a K-injective resolution.
Source: direct-images paragraph (3), agent-formulated quotient input
(blueprint: lem-sfb-open-normal-action-injective-models).
Proof: apply lem-sfb-grothendieck-k-injective to the structural Grothendieck abelian
category of actions. Its resolution is even monomorphic; only the quasi-isomorphism
is needed here. -/
theorem openNormalActionResolution (A : Ring.{u}) (P : ProfiniteGrp.{u})
    (N : CochainComplex (ActionModule A.toMon P) ℤ) :
    ∃ (I : CochainComplex (ActionModule A.toMon P) ℤ) (i : N ⟶ I),
      I.IsKInjective ∧ QuasiIso i := by
  sorry

/-- The canonical natural derived isomorphism beta is the identity on the common
kernel-invariant complex, under the inclusion-normalized ordinary identification.
The equation holds for every quasi-isomorphic K-injective resolution, without bounds.
Source: direct-images paragraph (3), agent-formulated quotient input, steps 6–8
(blueprint: lem-sfb-open-normal-action-injective-models).
Proof: exact kernel restriction takes i to a K-injective resolution. Compute RT on I
and RΓ_K on rI (sk-def-sfb-derived-categories); exact forgetting computes D(U).
The comparison kernel identifies UT(I) with Γ_K(rI), including differentials. Both
functors act on a chain map by this same identification. The Hom bijection of
lem-weil-pbc-kinjective-hom-derived makes the comparison natural on all derived maps.
For another resolution j:N→J, represent Qj (Qi)⁻¹ by a homotopy class h:I→J. The Hom
bijection gives hi homotopic to j and makes h a homotopy equivalence. Both invariant
functors preserve these homotopies and act identically on h, so the displayed equation
is independent of i. This proves the normalization on every unbounded derived object. -/
theorem openNormalActionInjectiveModels (A : Ring.{u}) (G L : ProfiniteGrp.{u})
    (K : OpenNormalSubgroup G) [T : NormalQuotient A G L K]
    (d : NormalDerivedComparison A G L K)
    (N I : CochainComplex (ActionModule A.toMon (G × L)) ℤ) [I.IsKInjective]
    (i : N ⟶ I) [QuasiIso i] :
    (normalBeta A G L K d).hom.app (DerivedCategory.Q.obj N) ≫
      (V.invariants A (normalKernel G K)).functor.rightDerivedFunctor.map
        ((inflate (R := A.toMon) (normalKernelInclusion G K L)).mapDerivedCategory.map
            (DerivedCategory.Q.map i) ≫
          (inflate (R := A.toMon) (normalKernelInclusion G K L)).mapDerivedCategoryFactors.hom.app
            I) ≫
      ((V.invariants A (normalKernel G K)).functor.rightDerivedFunctorObjQIso
        (((inflate (R := A.toMon) (normalKernelInclusion G K L)).mapHomologicalComplex
          (.up ℤ)).obj I)).hom =
    (forgetAction (R := A.toMon) (P := (G ⧸ K.toSubgroup) × L)).mapDerivedCategory.map
        (T.functor.rightDerivedFunctor.map (DerivedCategory.Q.map i) ≫
          (T.functor.rightDerivedFunctorObjQIso I).hom) ≫
      (forgetAction (R := A.toMon) (P := (G ⧸ K.toSubgroup) × L)).mapDerivedCategoryFactors.hom.app
        ((T.functor.mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
        (F := T.functor) (G := forgetAction (R := A.toMon) (P := (G ⧸ K.toSubgroup) × L))
        (Iso.refl _) (.up ℤ)).hom.app I) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex d.kernel.hom (.up ℤ)).app I) ≫
      DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
        (F := inflate (R := A.toMon) (normalKernelInclusion G K L))
        (G := (V.invariants A (normalKernel G K)).functor)
        (Iso.refl _) (.up ℤ)).inv.app I) := by
  sorry

end Profinite.CondensedAction
