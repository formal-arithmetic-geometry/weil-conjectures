/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel


public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModelExtension
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-! # Stalk tensor coordinates for a scheme pullback comparison

## References

* Stacks Project, Tags 08IB and 0098.
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

/-- The base points of a pullback point agree. -/
theorem point_eq (z : ↥(Limits.pullback f g)) :
    f ((pullback.fst f g) z) = g ((pullback.snd f g) z) := by
  exact congrArg (fun h : Limits.pullback f g ⟶ S ↦ h z) (pullback.condition (f := f) (g := g))

/-- Base stalk ring. -/
abbrev R (z : ↥(Limits.pullback f g)) := S.presheaf.stalk (f ((pullback.fst f g) z))

/-- Left stalk ring. -/
abbrev A (z : ↥(Limits.pullback f g)) := X.presheaf.stalk ((pullback.fst f g) z)

/-- Right stalk ring. -/
abbrev B (z : ↥(Limits.pullback f g)) := T.presheaf.stalk ((pullback.snd f g) z)

/-- Pullback stalk ring. -/
abbrev C (z : ↥(Limits.pullback f g)) := (Limits.pullback f g).presheaf.stalk z

/-- The left scalar structure is the actual scheme stalk map. -/
noncomputable abbrev leftAlgebra (z : ↥(Limits.pullback f g)) : Algebra (R f g z) (A f g z) :=
  (f.stalkMap ((pullback.fst f g) z)).hom.toAlgebra

/-- The right scalar structure transports the base point along the square. -/
noncomputable abbrev rightAlgebra (z : ↥(Limits.pullback f g)) : Algebra (R f g z) (B f g z) :=
  ((S.presheaf.stalkCongr (.of_eq (point_eq f g z))).hom ≫
    g.stalkMap ((pullback.snd f g) z)).hom.toAlgebra

attribute [local instance] leftAlgebra rightAlgebra

/-- The projection stalk maps agree on the base stalk. -/
theorem stalk_square (z : ↥(Limits.pullback f g)) :
    f.stalkMap ((pullback.fst f g) z) ≫ (pullback.fst f g).stalkMap z =
      (S.presheaf.stalkCongr (.of_eq (point_eq f g z))).hom ≫
        g.stalkMap ((pullback.snd f g) z) ≫ (pullback.snd f g).stalkMap z := by
  simpa only [Scheme.Hom.stalkMap_comp, Category.assoc] using
    Scheme.Hom.stalkMap_congr_hom
      (pullback.fst f g ≫ f) (pullback.snd f g ≫ g) (pullback.condition (f := f) (g := g)) z

/-- The scalar structure on the pullback stalk is the composite left stalk map. -/
noncomputable abbrev stalkAlgebra (z : ↥(Limits.pullback f g)) :
    Algebra (R f g z) (C f g z) :=
  (f.stalkMap ((pullback.fst f g) z) ≫ (pullback.fst f g).stalkMap z).hom.toAlgebra

attribute [local instance] stalkAlgebra

/-- The left projection stalk map as an algebra homomorphism. -/
noncomputable def leftStalkHom (z : ↥(Limits.pullback f g)) :
    A f g z →ₐ[R f g z] C f g z :=
  { ((pullback.fst f g).stalkMap z).hom with commutes' := fun _ ↦ rfl }

/-- The right projection respects base scalars. -/
theorem rightStalkHom_commutes (z : ↥(Limits.pullback f g)) (r : R f g z) :
    ((pullback.snd f g).stalkMap z).hom (algebraMap (R f g z) (B f g z) r) =
      algebraMap (R f g z) (C f g z) r := by
  exact (congrArg (fun h ↦ h.hom r) (stalk_square f g z)).symm

/-- The right projection stalk map as an algebra homomorphism. -/
noncomputable def rightStalkHom (z : ↥(Limits.pullback f g)) :
    B f g z →ₐ[R f g z] C f g z :=
  { ((pullback.snd f g).stalkMap z).hom with
    commutes' := rightStalkHom_commutes f g z }

/-- The canonical tensor-to-stalk map. On a pure tensor it multiplies the images under the
two projection stalk maps. -/
noncomputable def tensorToStalk (z : ↥(Limits.pullback f g)) :
    A f g z ⊗[R f g z] B f g z →+* C f g z :=
  (Algebra.TensorProduct.lift (leftStalkHom f g z) (rightStalkHom f g z)
    (fun _ _ ↦ Commute.all _ _)).toRingHom

/-- The pure-tensor formula for the explicit comparison. -/
theorem tensorToStalk_tmul (z : ↥(Limits.pullback f g)) (a : A f g z) (b : B f g z) :
    tensorToStalk f g z (a ⊗ₜ[R f g z] b) =
      ((pullback.fst f g).stalkMap z).hom a * ((pullback.snd f g).stalkMap z).hom b := by
  rfl

/-- The explicit comparison has the two prescribed restrictions. -/
theorem tensorToStalk_spec (z : ↥(Limits.pullback f g)) :
    (tensorToStalk f g z).comp
        (algebraMap (A f g z) (A f g z ⊗[R f g z] B f g z)) =
      ((pullback.fst f g).stalkMap z).hom ∧
    (tensorToStalk f g z).comp Algebra.TensorProduct.includeRight.toRingHom =
      ((pullback.snd f g).stalkMap z).hom := by
  constructor
  · ext a
    simp [tensorToStalk, leftStalkHom, rightStalkHom]
  · ext b
    simp [tensorToStalk, leftStalkHom, rightStalkHom]

/-- The two prescribed restrictions uniquely characterize the explicit comparison. -/
theorem tensorToStalk_unique (z : ↥(Limits.pullback f g))
    (φ : A f g z ⊗[R f g z] B f g z →+* C f g z)
    (hleft : φ.comp (algebraMap (A f g z) (A f g z ⊗[R f g z] B f g z)) =
      ((pullback.fst f g).stalkMap z).hom)
    (hright : φ.comp Algebra.TensorProduct.includeRight.toRingHom =
      ((pullback.snd f g).stalkMap z).hom) : φ = tensorToStalk f g z := by
  apply Algebra.TensorProduct.ringHom_ext
  · exact hleft.trans (tensorToStalk_spec f g z).1.symm
  · exact hright.trans (tensorToStalk_spec f g z).2.symm

/-- The tensor-to-stalk ring map exists with the two prescribed restrictions. -/
theorem exists_tensorToStalk (z : ↥(Limits.pullback f g)) :
    ∃ φ : A f g z ⊗[R f g z] B f g z →+* C f g z,
      φ.comp (algebraMap (A f g z) (A f g z ⊗[R f g z] B f g z)) =
        ((pullback.fst f g).stalkMap z).hom ∧
      φ.comp Algebra.TensorProduct.includeRight.toRingHom =
        ((pullback.snd f g).stalkMap z).hom := by
  exact ⟨tensorToStalk f g z, tensorToStalk_spec f g z⟩

/-- The pullback stalk is an algebra over the tensor product of the two original stalks. -/
noncomputable abbrev tensorAlgebra (z : ↥(Limits.pullback f g)) :
    Algebra (A f g z ⊗[R f g z] B f g z) (C f g z) :=
  (tensorToStalk f g z).toAlgebra

attribute [local instance] tensorAlgebra

/-- Stalkwise Tor independence: it concerns every pair of points over the same base point,
with `O_{S,f(x)}` identified with `O_{S,g(t)}` along the transport. -/
noncomputable def IsTorIndependent : Prop :=
  ∀ (x : X) (t : T) (h : f x = g t),
    letI := (f.stalkMap x).hom.toAlgebra
    letI := ((S.presheaf.stalkCongr (.of_eq h)).hom ≫ g.stalkMap t).hom.toAlgebra
    ∀ i : ℕ, 0 < i →
      IsZero (((CategoryTheory.Tor' (ModuleCat.{u} (S.presheaf.stalk (f x))) i).obj
        (ModuleCat.of (S.presheaf.stalk (f x)) (X.presheaf.stalk x))).obj
          (ModuleCat.of (S.presheaf.stalk (f x)) (T.presheaf.stalk t)))

/-- The stalk complex of a representative (Stacks, Tag 0098). -/
noncomputable abbrev stalkComplex (z : ↥(Limits.pullback f g))
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :=
  ((RingedSpace.moduleStalkFunctor X.toRingedSpace
      ((pullback.fst f g) z)).mapHomologicalComplex (.up ℤ)).obj K

/-- The algebraic cohomology model applied to a representative's stalk
(Stacks, Tags 08IB and 06Y6). -/
noncomputable def cohomologyModel (z : ↥(Limits.pullback f g))
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :=
  letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g z))
  letI := HasDerivedCategory.standard (ModuleCat.{u} (B f g z))
  ModuleCat.baseDerivedTensorCohomologyModel (R f g z) (A f g z) (B f g z)
    (stalkComplex f g z K) (C f g z)

/-- Scalar extension of a representative's stalk along the canonical
`A → A ⊗[R] B → C` map. -/
noncomputable def stalkTensorComplex (z : ↥(Limits.pullback f g))
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    CochainComplex (ModuleCat.{u} (C f g z)) ℤ :=
  ((ModuleCat.extendScalars ((tensorToStalk f g z).comp
    (algebraMap (A f g z) (A f g z ⊗[R f g z] B f g z)))).mapHomologicalComplex
      (.up ℤ)).obj
    (((RingedSpace.moduleStalkFunctor X.toRingedSpace
      ((pullback.fst f g) z)).mapHomologicalComplex (.up ℤ)).obj K)

/-- Invertibility of the canonical stalk comparison, expressed on `K`-flat representatives `K`
of `P`: the specified comparison `c_i : C ⊗[A ⊗[R] B] T_i → H^i(Q ⊗[A] C)` is invertible
for every degree `i` (Stacks, Tags 08IB, 0098 and 06YJ). -/
noncomputable def IsComparisonIso
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Limits.pullback f g).toRingedSpace))]
    (P : schemeDerivedCategory X) (z : ↥(Limits.pullback f g)) : Prop :=
  letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g z))
  letI := HasDerivedCategory.standard (ModuleCat.{u} (B f g z))
  ∀ K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ,
    K.IsKFlatTensor → Nonempty (DerivedCategory.Q.obj K ≅ P) →
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
