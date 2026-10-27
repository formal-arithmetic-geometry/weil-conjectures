/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.Paper.AdicUnitTraceConstruction

import Sheaf.Paper.AdicUnitTraceTargetNormalization
import Sheaf.Paper.AdicUnitTraceCounitReductions
import Sheaf.Paper.AdicUnitTraceProjectionAssembly
import Sheaf.Paper.SfIntegralConstructibleTriangulated

/-! # Integral unit trace and purity transpose

Source: current blueprint, purity transport Steps 2-3 and unit-trace assembly
(blueprint: lem-pur-adic-unit-trace-transpose-reductions).

The theorem supplies a base-field unit lift and treats every permitted choice of it.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open WeilConjectures.IntegralSystemRealization
namespace WeilConjectures.PurUnitTrace
open ConstructibleExceptionalCoefficients
variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (d : ℕ) [SmoothOfRelativeDimension d f]
  (S : RingSystem C.l C.Qbar D C.different (f := f))

/-- Source: blueprint purity transport Steps 2-3, unit-trace assembly
(blueprint: lem-pur-adic-unit-trace-transpose-reductions).

Proof plan:
1. The operation-domain lemma puts the completed unit, its shifted Tate twist,
   pullback, support and exceptional image in the uniform finite-Tor categories.
   Apply adic reconstruction to the base coefficient unit to obtain g0; choose
   any such g0, without claiming uniqueness from its reductions.
2. Transpose g0 by the specified support/exceptional adjunction. Its counit
   compatibility with reduction identifies each reduction of t0 with the
   unit specialization of the normalized finite smooth purity map, hence trace.
3. Extend this actual trace by ordinary coefficient tensor, the normalized Tate
   comparison and inverse support comparison. Finite-free scalar comparison
   identifies it with the strict-tower construction. At the cofinal exponents er
   tensor associativity reduces this formula to finite scalar extension of t0.
   The finite universal trace theorem identifies it with the ramified trace.
4. For any m choose er at least m and take the further derived quotient.
   Finite purity and exceptional counit comparisons commute with that quotient,
   without assuming flatness of it. Thus every positive trace reduction is normalized.
5. Invert the actual projection formula and compose tE tensor 1 with the unit
   constraint. Its adjoint, precomposed with the normalized j, is the displayed
   component. Projection naturality and the adjunction Hom bijection prove
   naturality; the coefficient actions prove linearity.
6. Reduce this formula. Tensor, twist, source, projection and counit comparisons
   identify it with the finite projection/trace transpose, with its coefficient
   action retained.
7. Finite tensor-trace-transpose and the unit equation for projection identify
   the result with the recorded diagonal/DNC-normalized smoothPurityMap. The
   shift is 2d, so crossing it introduces the trivial sign.
8. Both endpoints are derived complete. The first reduction is invertible by
   finite smooth purity; derived Nakayama makes these particular components
   invertible. The formulas include d=0, the zero object and empty schemes. -/
theorem adic_unit_trace_transpose_reductions :
    ∃ (normal0 : FiniteRightNormalization D C (baseField D C) f S)
      (core0 : CompletedUnitPullback.Core C.l (baseField D C) f)
      (hT0 : finiteTorConstructibleIntegral C.l (baseField D C) X
        (tateUnit D C (baseField D C) d X)),
      (∃ g0 : tateUnit D C (baseField D C) d X ≅
          ((operation D C (baseField D C) f S).G.obj ⟨_, core0.admissibleY.1⟩).obj,
        HasPrescribedReductions D C (baseField D C) f d S normal0 ⟨_, core0.admissibleY.1⟩
          ((sourceUnitIso D C (baseField D C) f d core0).hom ≫ g0.hom)) ∧
      (∀ g0 : tateUnit D C (baseField D C) d X ≅
          ((operation D C (baseField D C) f S).G.obj ⟨_, core0.admissibleY.1⟩).obj,
        HasPrescribedReductions D C (baseField D C) f d S normal0 ⟨_, core0.admissibleY.1⟩
          ((sourceUnitIso D C (baseField D C) f d core0).hom ≫ g0.hom) →
        HasTraceReductions D C (baseField D C) f d core0
          (unitTrace D C (baseField D C) f d S core0 hT0 g0) ∧
        ∀ (F : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) F],
          Nonempty (Construction D C F f d S
            (unitTrace D C (baseField D C) f d S core0 hT0 g0))) := by
  obtain ⟨pull⟩ := CompletedUnitPullback.completedUnitPullbackTower
    (purAdicFiniteSetting D C (baseField D C) 0) f
  let core := pull.core
  obtain ⟨normal, hn⟩ := unit_trace_target_normalization D C (baseField D C) f d S
  let K : finiteTorConstructibleIntegralCategory C.l (baseField D C) Y :=
    ⟨_, core.admissibleY.1⟩
  obtain ⟨a, ha, hsource, _, hred, _⟩ :=
    purAdicReconstruction D C (baseField D C) f d K.obj K.property
  have : IsIso a := ha
  obtain ⟨e, he⟩ := hn K
  let g : tateUnit D C (baseField D C) d X ≅
      ((operation D C (baseField D C) f S).G.obj K).obj :=
    (sourceUnitIso D C (baseField D C) f d core).symm ≪≫ asIso a ≪≫ e
  have hT : finiteTorConstructibleIntegral C.l (baseField D C) X
      (tateUnit D C (baseField D C) d X) := by
    let q := sourceUnitIso D C (baseField D C) f d core
    refine ⟨ObjectProperty.prop_of_iso _ q hsource.1, ?_⟩
    obtain ⟨i, j, hij, ht⟩ := hsource.2
    refine ⟨i, j, hij, fun n ↦ ?_⟩
    let eq := (scalarReductionDerivedExtension C.l (baseField D C) X n).mapIso q
    refine ⟨(ht n).1, ?_⟩
    rintro M P ⟨r⟩ v hv hP N k hk
    exact (ht n).2 M P ⟨r ≪≫ eq.symm⟩ v hv hP N k hk
  refine ⟨normal, core, hT, ⟨g, ?_⟩, ?_⟩
  · intro n
    have hn := he n
    have hh := (hred n).2.2
    dsimp only [g, Iso.trans_hom, Iso.symm_hom, asIso_hom]
    rw [Iso.hom_inv_id_assoc, Functor.map_comp, Category.assoc]
    exact (heq_of_eq (congrArg (fun v ↦
      (scalarReductionDerivedExtension C.l (baseField D C) X n).map a ≫ v)
      (eq_of_heq hn))).trans (heq_of_eq hh)
  · intro g0 hg0
    have ht := unit_trace_counit_reductions D C (baseField D C) f d S
      normal core hT g0 hg0
    refine ⟨ht, ?_⟩
    intro F _
    exact unit_trace_projection_assembly D C F f d S core
      (unitTrace D C (baseField D C) f d S core hT g0) ht


end WeilConjectures.PurUnitTrace
