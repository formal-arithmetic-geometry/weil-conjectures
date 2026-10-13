/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Sheaf.AlgebraicGeometry.ModulePullbackAffineSections
import Sheaf.AlgebraicGeometry.IntrinsicFlatModuleStalkTensorPresentation
import Mathlib.RingTheory.Flat.Localization

/-! # Tensor flatness on one pulled-back affine chart

Source: Stacks Project, Schemes Tags 01I4, 01IA, 01HV; Morphisms Tag 01U4;
Algebra Tag 00HT (6).
(blueprint: lem-pc-affine-pullback-chart-tensor-flat-stalks).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry

/-- On the inverse image of one affine open, flatness of the scalar-extended section
module is equivalent to relative flatness of the pulled-back stalks there.
There is no covering assumption and no flatness assertion outside this chart.
Source: Stacks Project, Schemes Tags 01I4, 01IA, 01HV; Morphisms Tag 01U4;
Algebra Tag 00HT (6).
(blueprint: lem-pc-affine-pullback-chart-tensor-flat-stalks).

Proof: Put B = Gamma(X,U) and N = Gamma(M,U), with A acting through f.
The inverse image W of U under the first projection is the fibre product
U times_{Spec A} Y. Use e and he to identify it over Y with
Spec(B tensor_A T), by the affine-spectrum pullback formula (01I4).
The affine pullback sections comparison (01IA, 01HV) identifies the sections
of the pulled-back module on W with N tensor_B (B tensor_A T).
Tensor associativity, interchange, and B tensor_B N = N identify these sections
with T tensor_A N as a T-module. All maps commute with the structure maps:
on pure tensors the comparison sends t tensor n to t times the pulled-back
section n. Consequently localization at the prime of a point z of W identifies
the localization of T tensor_A N as a (B tensor_A T)-module with the actual
pullback stalk, with T acting through the second projection.
Under e, the base stalk at the image of z is the localization T_p, where p is
the inverse image of the prime of z. Apply the two directions of the relative
local criterion for flatness (00HT (6)): the section module is T-flat exactly
when all these stalks are T_p-flat. Transport along the base stalk isomorphism
induced by e, whose compatibility with p is he. This is the displayed equivalence.
Quasi-coherence supplies the stalk localization comparisons. An empty U has zero
sections and an empty W; if T is the zero ring, W is empty and the tensor module
is zero. The zero module satisfies both sides. No finite presentation is used. -/
theorem affine_pullback_chart_tensor_flat_iff_stalks
    (A T : CommRingCat.{u}) {X Y : Scheme.{u}} (f : X ⟶ Spec A)
    (M : X.Modules) [M.IsQuasicoherent] (U : X.affineOpens)
    (q : A ⟶ T) (p : Y ⟶ Spec A) (e : Y ≅ Spec T)
    (he : e.hom ≫ Spec.map q = p) :
    (letI : Module (A : Type u) Γ(M, U.1) :=
      Module.compHom _ (((Scheme.ΓSpecIso A).inv ≫
        f.appLE ⊤ U.1 (by simp)).hom)
     letI : Algebra (A : Type u) (T : Type u) := q.hom.toAlgebra
     Module.Flat (T : Type u) ((T : Type u) ⊗[(A : Type u)] Γ(M, U.1))) ↔
    (∀ z : ↥(pullback f p : Scheme.{u}), (pullback.fst f p) z ∈ U.1 →
      Module.Flat (Y.presheaf.stalk ((pullback.snd f p) z))
        ((ModuleCat.restrictScalars ((pullback.snd f p).stalkMap z).hom).obj
          ((RingedSpace.moduleStalkFunctor (pullback f p).toRingedSpace z).obj
            ((Scheme.Modules.tensorPullback (pullback.fst f p)).obj M)))) := by sorry

end AlgebraicGeometry
