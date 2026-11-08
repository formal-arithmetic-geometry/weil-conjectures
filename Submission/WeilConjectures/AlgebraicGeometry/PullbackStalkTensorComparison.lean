/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel


public import Submission.WeilConjectures.AlgebraicGeometry.DerivedPullback
public import Submission.WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Projective

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Stalk tensor coordinates for a scheme pullback comparison

Source: Stacks Project, Tag 08IB, local affine tensor comparison, and Tag 0098,
stalks of module pullback (blueprint: def-pc-pullback-stalk-tensor-comparison).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.PullbackStalkTensor

variable {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)

/-- The base points of a pullback point agree. Source: Stacks, Tag 01JX.
Proof: apply the underlying point map to `pullback.condition`.
(blueprint: def-pc-pullback-stalk-tensor-comparison). -/
theorem point_eq (z : ↥(Limits.pullback f g)) :
    f ((pullback.fst f g) z) = g ((pullback.snd f g) z) := by
  exact congrArg (fun h : Limits.pullback f g ⟶ S ↦ h z) (pullback.condition (f := f) (g := g))

/-- Base stalk ring. Source: Stacks, Tag 08IB
(blueprint: def-pc-pullback-stalk-tensor-comparison). -/
abbrev R (z : ↥(Limits.pullback f g)) := S.presheaf.stalk (f ((pullback.fst f g) z))

/-- Left stalk ring. Source: Stacks, Tag 08IB
(blueprint: def-pc-pullback-stalk-tensor-comparison). -/
abbrev A (z : ↥(Limits.pullback f g)) := X.presheaf.stalk ((pullback.fst f g) z)

/-- Right stalk ring. Source: Stacks, Tag 08IB
(blueprint: def-pc-pullback-stalk-tensor-comparison). -/
abbrev B (z : ↥(Limits.pullback f g)) := T.presheaf.stalk ((pullback.snd f g) z)

/-- Pullback stalk ring. Source: Stacks, Tag 08IB
(blueprint: def-pc-pullback-stalk-tensor-comparison). -/
abbrev C (z : ↥(Limits.pullback f g)) := (Limits.pullback f g).presheaf.stalk z

/-- The left scalar structure is the actual scheme stalk map. Source: Stacks, Tag 08IB
(blueprint: def-pc-pullback-stalk-tensor-comparison). -/
noncomputable abbrev leftAlgebra (z : ↥(Limits.pullback f g)) : Algebra (R f g z) (A f g z) :=
  (f.stalkMap ((pullback.fst f g) z)).hom.toAlgebra

/-- The right scalar structure transports the base point along the square. Source:
Stacks, Tag 08IB (blueprint: def-pc-pullback-stalk-tensor-comparison). -/
noncomputable abbrev rightAlgebra (z : ↥(Limits.pullback f g)) : Algebra (R f g z) (B f g z) :=
  ((S.presheaf.stalkCongr (.of_eq (point_eq f g z))).hom ≫
    g.stalkMap ((pullback.snd f g) z)).hom.toAlgebra

attribute [local instance] leftAlgebra rightAlgebra

/-- The projection stalk maps agree on the base stalk. Source: Stacks, Tag 01JX.
Proof: expand the stalk maps of both composites in the pullback square; use
`pullback.condition` to identify these composites and transport their base point.
(blueprint: def-pc-pullback-stalk-tensor-comparison). -/
theorem stalk_square (z : ↥(Limits.pullback f g)) :
    f.stalkMap ((pullback.fst f g) z) ≫ (pullback.fst f g).stalkMap z =
      (S.presheaf.stalkCongr (.of_eq (point_eq f g z))).hom ≫
        g.stalkMap ((pullback.snd f g) z) ≫ (pullback.snd f g).stalkMap z := by
  simpa only [Scheme.Hom.stalkMap_comp, Category.assoc] using
    Scheme.Hom.stalkMap_congr_hom
      (pullback.fst f g ≫ f) (pullback.snd f g ≫ g) (pullback.condition (f := f) (g := g)) z

/-- The scalar structure on the pullback stalk is the composite left stalk map.
Source: Stacks, Tag 08IB (blueprint: def-pc-pullback-stalk-tensor-comparison). -/
noncomputable abbrev stalkAlgebra (z : ↥(Limits.pullback f g)) :
    Algebra (R f g z) (C f g z) :=
  (f.stalkMap ((pullback.fst f g) z) ≫ (pullback.fst f g).stalkMap z).hom.toAlgebra

attribute [local instance] stalkAlgebra

/-- The left projection stalk map as an algebra homomorphism. Source: Stacks,
Tag 08IB (blueprint: def-pc-pullback-stalk-tensor-comparison). -/
noncomputable def leftStalkHom (z : ↥(Limits.pullback f g)) :
    A f g z →ₐ[R f g z] C f g z :=
  { ((pullback.fst f g).stalkMap z).hom with commutes' := fun _ ↦ rfl }

/-- The right projection respects base scalars. Source: Stacks, Tags 01JX and 08IB.
Proof: evaluate the stalk square at a base-stalk element and reverse its equality.
(blueprint: def-pc-pullback-stalk-tensor-comparison). -/
theorem rightStalkHom_commutes (z : ↥(Limits.pullback f g)) (r : R f g z) :
    ((pullback.snd f g).stalkMap z).hom (algebraMap (R f g z) (B f g z) r) =
      algebraMap (R f g z) (C f g z) r := by
  exact (congrArg (fun h ↦ h.hom r) (stalk_square f g z)).symm

/-- The right projection stalk map as an algebra homomorphism. Source: Stacks,
Tag 08IB (blueprint: def-pc-pullback-stalk-tensor-comparison). -/
noncomputable def rightStalkHom (z : ↥(Limits.pullback f g)) :
    B f g z →ₐ[R f g z] C f g z :=
  { ((pullback.snd f g).stalkMap z).hom with
    commutes' := rightStalkHom_commutes f g z }

/-- The canonical tensor-to-stalk map constructed by the tensor-product lift.
On a pure tensor it multiplies the images under the two projection stalk maps.
Source: Stacks, Tag 08IB (blueprint: def-pc-pullback-stalk-tensor-comparison). -/
noncomputable def tensorToStalk (z : ↥(Limits.pullback f g)) :
    A f g z ⊗[R f g z] B f g z →+* C f g z :=
  (Algebra.TensorProduct.lift (leftStalkHom f g z) (rightStalkHom f g z)
    (fun _ _ ↦ Commute.all _ _)).toRingHom

/-- The pullback stalk is an algebra over the tensor of the two original stalks.
Source: Stacks, Tag 08IB (blueprint: def-pc-pullback-stalk-tensor-comparison). -/
noncomputable abbrev tensorAlgebra (z : ↥(Limits.pullback f g)) :
    Algebra (A f g z ⊗[R f g z] B f g z) (C f g z) :=
  (tensorToStalk f g z).toAlgebra

attribute [local instance] tensorAlgebra

end AlgebraicGeometry.PullbackStalkTensor

end
