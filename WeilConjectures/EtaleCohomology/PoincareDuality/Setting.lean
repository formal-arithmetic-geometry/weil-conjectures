/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!

# The fixed setting of the Poincaré duality chapter

Poincaré duality for `ℓ`-adic cohomology is stated for a scheme `X₀` over a finite field `k₀`
which is smooth, separated of finite type and geometrically connected of pure dimension `d`,
base changed to an algebraic closure `k` of `k₀`. This file packages that geometric datum as a
single structure, so that the statements of the chapter can quantify over it.

Properness of `X₀` is deliberately *not* part of the datum: the duality statements are
formulated with compact supports and do not use it. It is imposed explicitly, as an
`[IsProper …]` instance hypothesis, exactly where `Ra_{X!} ≅ Ra_{X*}` is needed.

## Main definitions

- `AlgebraicGeometry.PoincareDualitySetting`: the geometric datum `(X₀, a_{X₀})` of the
  chapter.
- `AlgebraicGeometry.PoincareDualitySetting.geometricFibre`: the base change
  `X = X₀ ×_{k₀} k` to the algebraic closure.
- `AlgebraicGeometry.PoincareDualitySetting.structureMorphism`: the structure morphism
  `a_X : X ⟶ Spec k`.

## Implementation notes

The "exceptional-adjoint admissibility" of `a_X` demanded by the blueprint is, in this
formalisation, the existence of a compactification of `a_X`, i.e. an instance of
`AlgebraicGeometry.HasCompactification`; it is what makes `Ra_{X!}` and `Ra_X^!` available.
It is carried as an instance hypothesis by the statements that need it rather than as a field
of the datum, since it is a property of the derived operations and not of the geometry.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (k₀ : Type u) [Field k₀] [Finite k₀]

/-- Blueprint `sk-def-set`: The fixed setting.

The geometric datum of the Poincaré duality chapter over the finite field `k₀`: a scheme `X₀`
over `k₀` which is smooth of relative dimension `d`, separated of finite type and
geometrically connected. The algebraic closure `k` of `k₀`, along which `X₀` is base changed,
is an argument of `PoincareDualitySetting.geometricFibre` rather than a field of the
datum. -/
structure PoincareDualitySetting (d : ℕ) where
  /-- The model `X₀` over the finite base field `k₀`. -/
  model : Scheme.{u}
  /-- The structure morphism `a_{X₀} : X₀ ⟶ Spec k₀`. -/
  modelStructureMorphism : model ⟶ Spec (CommRingCat.of k₀)
  [isSeparated : IsSeparated modelStructureMorphism]
  [locallyOfFiniteType : LocallyOfFiniteType modelStructureMorphism]
  [quasiCompact : QuasiCompact modelStructureMorphism]
  [smoothOfRelativeDimension : SmoothOfRelativeDimension d modelStructureMorphism]
  [geometricallyConnected : GeometricallyConnected modelStructureMorphism]

attribute [instance] PoincareDualitySetting.isSeparated
  PoincareDualitySetting.locallyOfFiniteType PoincareDualitySetting.quasiCompact
  PoincareDualitySetting.smoothOfRelativeDimension
  PoincareDualitySetting.geometricallyConnected

/-- The Frobenius `Spec (x ↦ x^q)` of `Spec k` over the finite field `k₀` with `q`
elements. -/
noncomputable def specFrobenius (k₀ k : Type u) [Field k₀] [Finite k₀] [Field k] [Algebra k₀ k]
    [Algebra.IsAlgebraic k₀ k] : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k) :=
  letI := Fintype.ofFinite k₀
  Spec.map (CommRingCat.ofHom (FiniteField.frobeniusAlgEquivOfAlgebraic k₀ k).toAlgHom.toRingHom)

namespace PoincareDualitySetting

variable {k₀} {d : ℕ} (S : PoincareDualitySetting k₀ d)
  (k : Type u) [Field k] [IsAlgClosed k] [Algebra k₀ k]

/-- The geometric fibre `X = X₀ ×_{k₀} k` of the datum `S` over an algebraic closure `k`
of `k₀`. -/
noncomputable def geometricFibre : Scheme.{u} :=
  pullback S.modelStructureMorphism (Spec.map (CommRingCat.ofHom (algebraMap k₀ k)))

/-- The structure morphism `a_X : X ⟶ Spec k` of the geometric fibre. -/
noncomputable def structureMorphism : S.geometricFibre k ⟶ Spec (CommRingCat.of k) :=
  pullback.snd S.modelStructureMorphism (Spec.map (CommRingCat.ofHom (algebraMap k₀ k)))

/-- The projection `X = X₀ ×_{k₀} k ⟶ X₀` from the geometric fibre to the model. -/
noncomputable def toModel : S.geometricFibre k ⟶ S.model :=
  pullback.fst S.modelStructureMorphism (Spec.map (CommRingCat.ofHom (algebraMap k₀ k)))

/-- The automorphism of the geometric fibre `X = X₀ ×_{k₀} k` obtained by base changing along
a `k₀`-algebra automorphism `σ` of `k`, that is, `1_{X₀} × Spec σ`. -/
noncomputable def baseChangeAut (σ : k ≃ₐ[k₀] k) : S.geometricFibre k ⟶ S.geometricFibre k :=
  pullback.lift (pullback.fst S.modelStructureMorphism
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ k))))
    (pullback.snd S.modelStructureMorphism (Spec.map (CommRingCat.ofHom (algebraMap k₀ k))) ≫
      Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom)) (by
    have h : (CommRingCat.ofHom (algebraMap k₀ k) ≫
        CommRingCat.ofHom σ.toAlgHom.toRingHom) = CommRingCat.ofHom (algebraMap k₀ k) := by
      ext x
      exact σ.commutes x
    rw [Category.assoc, ← Spec.map_comp, h]
    exact pullback.condition)

omit [Finite k₀] [IsAlgClosed k] in
@[reassoc]
lemma baseChangeAut_comp_structureMorphism (σ : k ≃ₐ[k₀] k) :
    S.baseChangeAut k σ ≫ S.structureMorphism k =
      S.structureMorphism k ≫ Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) :=
  pullback.lift_snd _ _ _

/-- The geometric Frobenius `g_γ` of the geometric fibre `X = X₀ ×_{k₀} k`: the base change
`1_{X₀} × Spec (x ↦ x^q)` of the arithmetic Frobenius of `k` over the finite field `k₀` with
`q` elements. Since `Spec` is contravariant, the arithmetic Frobenius of the coefficient field
induces the *geometric* Frobenius of the scheme. -/
noncomputable def geometricFrobenius [Algebra.IsAlgebraic k₀ k] :
    S.geometricFibre k ⟶ S.geometricFibre k :=
  letI := Fintype.ofFinite k₀
  S.baseChangeAut k (FiniteField.frobeniusAlgEquivOfAlgebraic k₀ k)

omit [IsAlgClosed k] in
@[reassoc]
lemma geometricFrobenius_comp_structureMorphism [Algebra.IsAlgebraic k₀ k] :
    S.geometricFrobenius k ≫ S.structureMorphism k =
      S.structureMorphism k ≫ specFrobenius k₀ k :=
  pullback.lift_snd _ _ _

end PoincareDualitySetting

end AlgebraicGeometry
