/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK, SHEAF group Q65
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.CategoryTheory.Monoidal.TensorInverse

/-!
# Module evaluation and tensor powers on the small étale site

Source: Stacks Project, Modules on Sites, Tags 03D7, 03EK and 03EL;
Sites, Tag 039Z; Descent on Spaces, Tag 0D3C, the maps psi_d and psi
(blueprint: def-trf-etale-module-evaluation-tensor-powers).

These are the existing counit, coproduct evaluation and tensor-power constructions,
moved out of the Zariski/étale comparison theorem module without changing their data.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The actual degree counit, adjunct to the identity of the specified direct image.
Source: Stacks, Tags 03D7 and 0D3C
(blueprint: def-trf-etale-module-evaluation-tensor-powers). -/
def evaluationCounit {X Y : AlgebraicSpace S} (f : X ⟶ Y) (M : X.Modules) :
    (moduleTensorPullback f).obj ((moduleDirectImage f).obj M) ⟶ M :=
  (moduleTensorAdjunction f).counit.app M

/-- Pull back a coproduct cofan with its actual injections.
Source: Stacks, Tag 03D7 (blueprint: def-trf-etale-module-evaluation-tensor-powers). -/
def evaluationPullbackCofan {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (C : ℕ → Y.Modules) (c : Cofan C) :
    Cofan (fun d ↦ (moduleTensorPullback f).obj (C d)) :=
  Cofan.mk ((moduleTensorPullback f).obj c.pt)
    (fun d ↦ (moduleTensorPullback f).map (c.inj d))

/-- The total evaluation is the unique descent of its homogeneous counits.
Source: Stacks, Tag 0D3C, psi (blueprint: def-trf-etale-module-evaluation-tensor-powers). -/
def evaluationTotal {X Y : AlgebraicSpace S} (f : X ⟶ Y) (B : ℕ → X.Modules)
    (c : Cofan (fun d ↦ (moduleDirectImage f).obj (B d))) (b : Cofan B)
    (h : IsColimit (evaluationPullbackCofan f _ c)) :
    (moduleTensorPullback f).obj c.pt ⟶ b.pt :=
  Cofan.IsColimit.desc h (fun d ↦ evaluationCounit f (B d) ≫ b.inj d)

/-- The actual sheaf tensor on the small affine étale model, using the existing monoidal API.
Source: Stacks, Tags 03EK and 039Z
(blueprint: def-trf-etale-module-evaluation-tensor-powers). -/
instance (priority := 100) evaluationSmallModulesMonoidal (X : AlgebraicSpace S) :
    MonoidalCategory X.SmallModules :=
  SheafOfModules.monoidalCategory X.smallStructureSheaf

/-- Tensor powers on the small affine model use the existing generic natural tensor powers.
Source: Stacks, Tags 03EK and 0D3C
(blueprint: def-trf-etale-module-evaluation-tensor-powers). -/
def evaluationSmallPower (X : AlgebraicSpace S) (L : X.Modules) (n : ℕ) : X.SmallModules :=
  MonoidalCategory.tensorPowNat (X.smallModuleRestriction.obj L) n

/-- The same tensor powers as module sheaves on the original site, transported through the
actual restriction equivalence, which preserves the regular functions and sheaf tensor.
Source: Stacks, Tags 03EK and 039Z
(blueprint: def-trf-etale-module-evaluation-tensor-powers). -/
def evaluationLinePower (X : AlgebraicSpace S) (L : X.Modules) (n : ℕ) : X.Modules :=
  X.smallModuleEquivalence.inverse.obj (evaluationSmallPower X L n)

/-- Canonical concatenation of natural tensor powers, by the usual unitors and associators.
Source: Stacks, Tag 03EL (blueprint: def-trf-etale-module-evaluation-tensor-powers). -/
def evaluationPowerAddIso {C : Type v} [Category.{u} C] [MonoidalCategory C] (L : C) :
    ∀ m n : ℕ, MonoidalCategory.tensorPowNat L (m + n) ≅
      MonoidalCategory.tensorPowNat L m ⊗ MonoidalCategory.tensorPowNat L n
  | 0, n => eqToIso (congrArg (MonoidalCategory.tensorPowNat L) (Nat.zero_add n)) ≪≫
      (MonoidalCategory.leftUnitor _).symm
  | m + 1, n =>
      eqToIso (congrArg (MonoidalCategory.tensorPowNat L) (Nat.succ_add m n)) ≪≫
        (MonoidalCategory.whiskerLeftIso L (evaluationPowerAddIso L m n)) ≪≫
        (MonoidalCategory.associator _ _ _).symm

/-- Pure tensors in the sheaf tensor on the small affine model.
Source: Stacks, Tag 03EK (blueprint: def-trf-etale-module-evaluation-tensor-powers). -/
def evaluationSmallTmul (X : AlgebraicSpace S) (M N : X.SmallModules)
    (V : X.SmallEtaleModel) (s : M.val.obj (op V)) (t : N.val.obj (op V)) :
    (M ⊗ N).val.obj (op V) :=
  (SheafOfModules.tensorObjIsoSheafification M N).inv.val.app (op V)
    (((PresheafOfModules.sheafificationAdjunction (𝟙 X.smallStructureRings.obj)).unit.app
      (M.val ⊗ N.val)).app (op V) (s ⊗ₜ[X.smallStructureSheaf.obj.obj (op V)] t))

end AlgebraicGeometry.AlgebraicSpace
