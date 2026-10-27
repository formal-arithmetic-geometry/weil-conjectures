/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q65, SHEAF group W4
-/
module

public import Sheaf.TraceFormula.EtaleGradedModuleAlgebra
public import Sheaf.TraceFormula.EtaleModuleEvaluationTensorPowers
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

/-!
# Normalization of canonical products on étale tensor powers

Source: Stacks Project, sites-modules.tex, Tags 03EL and 039Z;
spaces-descent.tex, Tag 0D3C
(blueprint: def-trf-etale-power-product-normalization).

These are the unchanged chart, first-power and product normalizations formerly
located in GradedPushforwardEtaleRestriction. Keeping the data separate lets the
canonical-product construction and its restriction comparison be stated independently.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Identify the existing tensor powers on the original site with their values on the
small affine model, using the counit of the actual restriction equivalence.
Source: Stacks, Tags 039Z and 03EL
(blueprint: def-trf-etale-power-product-normalization). -/
def gradedPowerChartIso (X : AlgebraicSpace S) (L : X.Modules) (n : ℕ) :
    X.smallModuleRestriction.obj (evaluationLinePower X L n) ≅ evaluationSmallPower X L n :=
  X.smallModuleEquivalence.counitIso.app (evaluationSmallPower X L n)

/-- The canonical identification of the first tensor power with the module itself.
Source: Stacks, Tag 03EL (blueprint: def-trf-etale-power-product-normalization). -/
def gradedPowerOneIso (X : AlgebraicSpace S) (L : X.Modules) :
    evaluationLinePower X L 1 ≅ L :=
  X.smallModuleEquivalence.inverse.mapIso (ρ_ (X.smallModuleRestriction.obj L)) ≪≫
    X.smallModuleEquivalence.unitIso.symm.app L

/-- Canonical tensor-power products, checked on an affine basis through the restriction
equivalence. The zero power is the structure module and its unit map is invertible.
The multiplication is concatenation of actual tensor factors, with ordinary symmetry.
Source: Stacks, Tags 03EL, 039Z and 0D3C
(blueprint: def-trf-etale-power-product-normalization). -/
def HasCanonicalEtalePowerProducts (X : AlgebraicSpace S) (L : X.Modules)
    (A : EtaleGradedModuleAlgebra (evaluationLinePower X L)) : Prop :=
  IsIso A.unit ∧
  (∀ (m n : ℕ) (V : X.SmallEtaleModel)
    (s : (evaluationLinePower X L m).val.obj (op (X.smallEtaleInclusion.obj V)))
    (t : (evaluationLinePower X L n).val.obj (op (X.smallEtaleInclusion.obj V))),
    (gradedPowerChartIso X L (m + n)).hom.val.app (op V)
        (A.mul m n (X.smallEtaleInclusion.obj V) s t) =
      (evaluationPowerAddIso (X.smallModuleRestriction.obj L) m n).inv.val.app (op V)
        (evaluationSmallTmul X (evaluationSmallPower X L m) (evaluationSmallPower X L n) V
          ((gradedPowerChartIso X L m).hom.val.app (op V) s)
          ((gradedPowerChartIso X L n).hom.val.app (op V) t))) ∧
  (∀ (V : X.SmallEtaleModel)
    (a : X.structureSheaf.obj.obj (op (X.smallEtaleInclusion.obj V))),
    (gradedPowerChartIso X L 0).hom.val.app (op V)
        (A.unit.val.app (op (X.smallEtaleInclusion.obj V)) a) =
      @id ((evaluationSmallPower X L 0).val.obj (op V)) a)

end AlgebraicGeometry.AlgebraicSpace
