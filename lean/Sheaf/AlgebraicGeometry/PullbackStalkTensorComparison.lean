/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Sheaf.AlgebraicGeometry.DerivedPullback
import Sheaf.Algebra.Homology.ModuleStalkFunctor
import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.Algebra.Category.ModuleCat.Projective

/-! # Stalk tensor coordinates for a scheme pullback comparison

Source: Stacks Project, Tag 08IB, local affine tensor comparison, and Tag 0098,
stalks of module pullback (blueprint: def-pc-pullback-stalk-tensor-comparison).
-/

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
  sorry

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

/-- The tensor-to-stalk ring map exists with the two prescribed restrictions.
Source: Stacks, Tag 01JX and Tag 08IB.
Proof: the two projection stalk maps agree on R by `pullback.condition` and
functoriality of stalk maps. The universal property of A tensor-over-R B gives
one ring map; its restrictions are the two input maps.
(blueprint: def-pc-pullback-stalk-tensor-comparison). -/
theorem exists_tensorToStalk (z : ↥(Limits.pullback f g)) :
    ∃ φ : A f g z ⊗[R f g z] B f g z →+* C f g z,
      φ.comp (algebraMap (A f g z) (A f g z ⊗[R f g z] B f g z)) =
        ((pullback.fst f g).stalkMap z).hom ∧
      φ.comp Algebra.TensorProduct.includeRight.toRingHom =
        ((pullback.snd f g).stalkMap z).hom := by
  sorry

/-- The canonical tensor-to-stalk map, selected from its universal property.
Source: Stacks, Tag 08IB (blueprint: def-pc-pullback-stalk-tensor-comparison). -/
noncomputable def tensorToStalk (z : ↥(Limits.pullback f g)) :
    A f g z ⊗[R f g z] B f g z →+* C f g z :=
  Classical.choose (exists_tensorToStalk f g z)

/-- The pullback stalk is an algebra over the tensor of the two original stalks.
Source: Stacks, Tag 08IB (blueprint: def-pc-pullback-stalk-tensor-comparison). -/
noncomputable abbrev tensorAlgebra (z : ↥(Limits.pullback f g)) :
    Algebra (A f g z ⊗[R f g z] B f g z) (C f g z) :=
  (tensorToStalk f g z).toAlgebra

attribute [local instance] tensorAlgebra

/-- Stalkwise Tor independence includes every pair over the same base point,
not merely a selected family of points in the pullback. The transport identifies
O_{S,f(x)} with O_{S,g(t)}. Source: Stacks, Tag 08IB
(blueprint: def-pc-pullback-stalk-tensor-comparison). -/
noncomputable def IsTorIndependent : Prop :=
  ∀ (x : X) (t : T) (h : f x = g t),
    letI := (f.stalkMap x).hom.toAlgebra
    letI := ((S.presheaf.stalkCongr (.of_eq h)).hom ≫ g.stalkMap t).hom.toAlgebra
    ∀ i : ℕ, 0 < i →
      IsZero (((CategoryTheory.Tor' (ModuleCat.{u} (S.presheaf.stalk (f x))) i).obj
        (ModuleCat.of (S.presheaf.stalk (f x)) (X.presheaf.stalk x))).obj
          (ModuleCat.of (S.presheaf.stalk (f x)) (T.presheaf.stalk t)))

/-- A representative's stalk complex. Source: Stacks, Tag 0098
(blueprint: def-pc-pullback-stalk-tensor-comparison). -/
noncomputable abbrev stalkComplex (z : ↥(Limits.pullback f g))
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :=
  ((RingedSpace.moduleStalkFunctor X.toRingedSpace
      ((pullback.fst f g) z)).mapHomologicalComplex (.up ℤ)).obj K

/-- The existing algebraic model applied to a representative's stalk.
Source: Stacks, Tags 08IB and 06Y6
(blueprint: def-pc-pullback-stalk-tensor-comparison). -/
noncomputable def cohomologyModel (z : ↥(Limits.pullback f g))
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :=
  letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g z))
  letI := HasDerivedCategory.standard (ModuleCat.{u} (B f g z))
  ModuleCat.baseDerivedTensorCohomologyModel (R f g z) (A f g z) (B f g z)
    (stalkComplex f g z K) (C f g z)

/-- Ordinary scalar extension of a representative's stalk along the canonical
A -> A tensor-over-R B -> C map. Source: Stacks, Tag 08IB
(blueprint: def-pc-pullback-stalk-tensor-comparison). -/
noncomputable def stalkTensorComplex (z : ↥(Limits.pullback f g))
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    CochainComplex (ModuleCat.{u} (C f g z)) ℤ :=
  ((ModuleCat.extendScalars ((tensorToStalk f g z).comp
    (algebraMap (A f g z) (A f g z ⊗[R f g z] B f g z)))).mapHomologicalComplex
      (.up ℤ)).obj
    (((RingedSpace.moduleStalkFunctor X.toRingedSpace
      ((pullback.fst f g) z)).mapHomologicalComplex (.up ℤ)).obj K)

/-- Invertibility of the canonical stalk comparison, in K-flat coordinates.
For every K-flat representative K of P, use its stalk Q, the existing derived
cohomology model T_i = H^i(Q tensor-derived-over-R B), and its specified comparison
c_i : C tensor-over-(A tensor-over-R B) T_i -> H^i(Q tensor-over-A C).
The target is identified with the stalk of H^i(Lg_X^*P). Requiring an identification
and invertibility after EVERY such identification is precisely invertibility of
c_i under the canonical identification: postcomposition by an isomorphism neither
creates nor destroys invertibility. This does not quantify over arbitrary maps
out of T_i; c_i is fixed by the equations of BaseDerivedTensorCohomologyModel.
K-flat representatives exist, so the universal quantification is not vacuous.
Source: Stacks, Tags 08IB, 0098 and 06YJ
(blueprint: def-pc-pullback-stalk-tensor-comparison). -/
noncomputable def IsComparisonIso
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Limits.pullback f g).toRingedSpace))]
    (P : schemeDerivedCategory X) (z : ↥(Limits.pullback f g)) : Prop :=
  letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g z))
  letI := HasDerivedCategory.standard (ModuleCat.{u} (B f g z))
  ∀ K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ,
    K.IsKFlat → Nonempty (DerivedCategory.Q.obj K ≅ P) →
    ∀ i : ℤ,
      Nonempty
        ((stalkTensorComplex f g z K).homology i ≅
          (RingedSpace.moduleStalkFunctor (Limits.pullback f g).toRingedSpace z).obj
            ((DerivedCategory.homologyFunctor _ i).obj
              ((derivedPullback (pullback.fst f g)).obj P))) ∧
      ∀ e :
        (stalkTensorComplex f g z K).homology i ≅
          (RingedSpace.moduleStalkFunctor (Limits.pullback f g).toRingedSpace z).obj
            ((DerivedCategory.homologyFunctor _ i).obj
              ((derivedPullback (pullback.fst f g)).obj P)),
        IsIso ((cohomologyModel f g z K).localizedComparison i ≫ e.hom)

end AlgebraicGeometry.PullbackStalkTensor

end
