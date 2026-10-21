/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q66
-/
module
public import Sheaf.SixFunctors.PointEvaluationTensorData

/-! Source: Stacks 0991, 03EL, 07A4
(blueprint: def-sf-point-evaluation-scalar-data). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] SheafOfModules.monoidalCategory
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.CochainPullback
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry.ProEtale.PointEvaluation
variable {k : Type u} [Field k]
  (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1})
/-- Evaluation of the given coefficient morphism, with its actual ring map.
Source: Stacks 03EL (blueprint: def-sf-point-evaluation-scalar-data). -/
abbrev scalarMap {B' : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1}}
    (a : B ⟶ B') : sectionRing k B →+* sectionRing k B' :=
  (a.hom.app (op (finalObject k))).hom

/-- Ordinary termwise scalar extension, with scalars first in Mathlib's convention.
Source: Stacks 03EL, 07A4 (blueprint: def-sf-point-evaluation-scalar-data). -/
abbrev moduleExtend
    {B' : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1}} (a : B ⟶ B') :=
  letI := (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
    (scalarMap B a)).left_adjoint_additive
  (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (scalarMap B a)).mapHomologicalComplex (.up ℤ)

variable {B}

/-- The coefficient square and its balanced inverse on flat-term representatives.
The tensor square is an equality of the specified chain maps; coefficient maps need not be flat.
Source: Stacks 03EL, 07A4 (blueprint: def-sf-point-evaluation-scalar-data). -/
structure ScalarModel
    {B' : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1}}
    (a : B ⟶ B') (T : TensorModel B) (T' : TensorModel B') where
  /-- The canonical scalar comparison on complexes. -/
  κ : extend.{u + 1, u + 1, u} a ⋙ complexSections k B' ≅ complexSections k B ⋙ moduleExtend B a
  /-- On each degree the map is precisely the balanced section comparison. -/
  κ_pure : ∀ (P : Complexes B) (i : ℤ) (b : sectionRing k B')
    (x : (pointModuleSections k B).obj (P.X i)),
    ((κ.hom.app P).f i) (extensionTmul.{u + 1, u + 1, u} a (P.X i) (op (finalObject k)) b x) =
      b ⊗ₜ[sectionRing k B, scalarMap B a] x
  /-- The ordinary coefficient tensor comparison, also specified on all summands. -/
  ε : ∀ P Q : CochainComplex (ModuleCat.{u + 1} (sectionRing k B)) ℤ,
    (moduleExtend B a).obj (P ⊗ Q) ≅ (moduleExtend B a).obj P ⊗ (moduleExtend B a).obj Q
  /-- Its inverse is (a tensor x) tensor (b tensor y) mapped to ab tensor (x tensor y).
This is the displayed balanced rule with Mathlib's coefficient-first tensor convention. -/
  ε_inverse : ∀ (P Q : CochainComplex (ModuleCat.{u + 1} (sectionRing k B)) ℤ)
    (i j n : ℤ) (h : i + j = n) (c d : sectionRing k B') (x : P.X i) (y : Q.X j),
    ((ε P Q).inv.f n)
      (HomologicalComplex.ιTensorObj ((moduleExtend B a).obj P) ((moduleExtend B a).obj Q)
        i j n h ((c ⊗ₜ[sectionRing k B, scalarMap B a] x) ⊗ₜ[sectionRing k B']
          (d ⊗ₜ[sectionRing k B, scalarMap B a] y))) =
      (c * d) ⊗ₜ[sectionRing k B, scalarMap B a]
        (HomologicalComplex.ιTensorObj P Q i j n h (x ⊗ₜ[sectionRing k B] y))

end AlgebraicGeometry.ProEtale.PointEvaluation
