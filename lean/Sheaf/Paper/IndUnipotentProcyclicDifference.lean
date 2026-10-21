/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.Paper.IndUnipotentSystem
public import Sheaf.CategoryTheory.CondensedDerivedInflationArrows
public import Mathlib.Algebra.Homology.Double
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Sheaf.Topology.ContinuousMapCondensedRing
import Sheaf.CategoryTheory.CondensedProductActionInflation
import Sheaf.CategoryTheory.NormedScalarProfiniteHomAcyclic
import WeilConjectures.Algebra.Homology.FirstQuadrantTotalComparison
import Sheaf.CategoryTheory.CondensedDerivedInvariantBar
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor

/-! # The rank-one derived difference model for countable ind-unipotent modules

Source: main-20261015 direct-image stability proof, paragraph (3), agent-formulated
rank-one analytic obligation; exact reference WANTED
(blueprint: lem-sfb-ind-unipotent-procyclic-difference).

All derived functors are formed in the full ordinary condensed action category.
A presentation specifies the finite-stage sections, and an actual colimit cocone specifies
M. The canonical difference is characterized on all sections, not chosen arbitrarily.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProEtale
namespace Profinite.CondensedAction.IndUnipotent

variable (ℓ : ℕ) [Fact ℓ.Prime] (F : Type u) [NormedField F]
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]



/-- Retain the original G-action by restriction along g mapping to (g,0).
Source: paragraph (3), residual action
(blueprint: lem-sfb-ind-unipotent-procyclic-difference). -/
def retained (M : ActionModule (normContinuousRing F) (G × IntegerGroup.{u} ℓ)) :
    ActionModule (normContinuousRing F) G :=
  (inflate (ContinuousMonoidHom.inl G (IntegerGroup.{u} ℓ))).obj M

/-- The existing two-term complex, in degrees zero and one, of an actual difference map.
Source: paragraph (3), displayed difference complex
(blueprint: lem-sfb-ind-unipotent-procyclic-difference). -/
def differenceComplex {M : ActionModule (normContinuousRing F) (G × IntegerGroup.{u} ℓ)}
    (d : retained ℓ F G M ⟶ retained ℓ F G M) :
    CochainComplex (ActionModule (normContinuousRing F) G) ℤ :=
  HomologicalComplex.double d (by decide : (ComplexShape.up ℤ).Rel 0 1)

variable (v : ProductInvariants (normContinuousRing F) G (IntegerGroup.{u} ℓ))

/-- Ordinary fixed sections enter ordinary derived invariants through its derivation unit.
Source: paragraph (3), degree-zero normalization
(blueprint: lem-sfb-ind-unipotent-procyclic-difference). -/
def invariantUnit (M : ActionModule (normContinuousRing F) (G × IntegerGroup.{u} ℓ)) :
    (DerivedCategory.singleFunctor _ 0).obj (v.functor.obj M) ⟶
      v.functor.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj M) :=
  (DerivedCategory.singleFunctorIsoCompQ _ 0).hom.app (v.functor.obj M) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex v.functor (.up ℤ) 0).inv.app M) ≫
    v.functor.rightDerivedFunctorUnitQ ((CochainComplex.singleFunctor _ 0).obj M) ≫
    v.functor.rightDerivedFunctor.map
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).inv.app M)

/-- The canonical inclusion from H^0 of a two-term complex into its degree-zero term.
The pOpcycles isomorphism uses its zero incoming differential.
Source: paragraph (3), common inclusion in M
(blueprint: lem-sfb-ind-unipotent-procyclic-difference). -/
def differenceH0Inclusion
    {M : ActionModule (normContinuousRing F) (G × IntegerGroup.{u} ℓ)}
    (d : retained ℓ F G M ⟶ retained ℓ F G M) :
    (differenceComplex ℓ F G d).homology 0 ⟶ retained ℓ F G M :=
  (differenceComplex ℓ F G d).homologyι 0 ≫
    ((differenceComplex ℓ F G d).pOpcyclesIso (-1) 0 (by simp)
      (HomologicalComplex.double_d_eq_zero₀ d
        (by decide : (ComplexShape.up ℤ).Rel 0 1) (-1) 0 (by simp))).inv ≫
    (HomologicalComplex.doubleXIso₀ d (by decide : (ComplexShape.up ℤ).Rel 0 1)).hom

/-- The difference comparison and the normalized identification of its degree-zero kernel.
The equation on sections characterizes d as tau minus identity, hence exp(D) minus identity.
The unit square says that the very displayed derived isomorphism induces the common
inclusion identification. No equivalence of cohomology groups substitutes for the iso.
Source: paragraph (3), rank-one analytic assertion
(blueprint: lem-sfb-ind-unipotent-procyclic-difference). -/
def DifferenceModel
    (M : ActionModule (normContinuousRing F) (G × IntegerGroup.{u} ℓ)) : Prop :=
  ∃ (d : retained ℓ F G M ⟶ retained ℓ F G M),
    (∀ (S : Profinite.{u}) (m : sectionModule (normContinuousRing F) M.module S),
      (d.val.hom.hom.app (op S)).hom m =
        M.act S (ContinuousMap.const S (1, generator ℓ)) m - m) ∧
    ∃ e : v.functor.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj M) ≅
        DerivedCategory.Q.obj (differenceComplex ℓ F G d),
    ∃ z : v.functor.obj M ≅ (differenceComplex ℓ F G d).homology 0,
      (z.hom ≫ differenceH0Inclusion ℓ F G d).val = v.inclusion.app M ∧
      (DerivedCategory.homologyFunctor _ 0).map (invariantUnit ℓ F G v M) ≫
        (DerivedCategory.homologyFunctor _ 0).map e.hom ≫
        (DerivedCategory.homologyFunctorFactors _ 0).hom.app (differenceComplex ℓ F G d) =
          (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).hom.app
            (v.functor.obj M) ≫ z.hom

/-- Countable ind-unipotent norm-coefficient representations have the normalized derived
rank-one difference model. F can be the finite intermediate field or the noncomplete
algebraic closure; no other coefficient cases are asserted.

Source: main-20261015 direct-image proof (3), rank-one analytic input, exact reference
WANTED (blueprint: lem-sfb-ind-unipotent-procyclic-difference).

Proof:
1. lem-sfb-relative-cyclic-restriction-model gives the actual restriction comparison
and its conservative forgetting of G; it suffices to prove the scalar version invertible.
2. For the trivial scalar representation over E, use
lem-sfb-normed-scalar-profinite-hom-acyclic, the derived invariant bar, and the
first-quadrant column comparison. For Omega use lem-sfb-norm-algcl-bar-augmentation
instead: no complete-field internal-Hom assertion is applied to Omega.
3. lem-sfb-procyclic-scalar-cochain-evaluation identifies that scalar bar with [A -> A]
by identity in degree zero and evaluation at 1 in degree one. The restriction-model
normalization identifies this with the actual comparison, proving its invertibility.
4. Additivity gives all trivial finite-dimensional stages, including zero, by finite sums.
5. The kernel of each nilpotent operator has trivial action; its quotient is unipotent.
A finite-dimensional linear complement gives a continuous nonequivariant splitting,
so continuous-section scalar extension gives a short exact sequence of action modules.
6. Induct on dimension. For a nonzero nilpotent operator the kernel is nonzero, so the
quotient dimension drops. The complex-SES triangle and triangle two-out-of-three,
with comparison naturality, establish the assertion at every finite stage.
7. lem-sfb-profinite-invariants-filtered-continuity identifies the colimit cohomology
by the actual coprojections. AB5 from the derived restriction calculus identifies
cohomology on the two-term side with its filtered colimit.
8. Naturality then proves invertibility on M in every degree; negative degrees vanish.
9. Restore G by conservative forgetting. Its differential is tau-1 = exp(D)-1.
10. At each stage exp(D)-1 = D times an invertible polynomial with constant term 1,
so its kernel is ker D, fixed by every exp(tD). Sheaf-colimit sections come locally
from stages, and vanishing can be checked after further refinement. Thus the fixed
subsheaf and difference kernel have the same inclusion; the restriction comparison's
unit normalization gives exactly the displayed H^0 square. This includes G=1, zero
stages, D=0, and unbounded dimensions and nilpotence orders.
-/
theorem ind_unipotent_procyclic_difference
    (Ω : Type u) [NormedField Ω] [Algebra ℚ_[ℓ] Ω] [IsAlgClosure ℚ_[ℓ] Ω]
    (hΩ : ∀ a : ℚ_[ℓ], ‖algebraMap ℚ_[ℓ] Ω a‖ = ‖a‖)
    (E : Type u) [NormedField E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (j : E →ₐ[ℚ_[ℓ]] Ω) (hE : ∀ a : E, ‖a‖ = ‖j a‖)
    [Algebra E Ω] (hj : algebraMap E Ω = j.toRingHom)
    [Algebra E F] (ι : F →ₐ[E] Ω) (hι : ∀ a : F, ‖ι a‖ = ‖a‖)
    (hF : Function.Surjective (algebraMap E F) ∨ Function.Surjective ι)
    (T : System ℓ E G) (P : Presentation ℓ E F G T)
    (c : Cocone P.diagram) (hc : IsColimit c) :
    DifferenceModel ℓ F G v c.pt := by
  sorry

end Profinite.CondensedAction.IndUnipotent
