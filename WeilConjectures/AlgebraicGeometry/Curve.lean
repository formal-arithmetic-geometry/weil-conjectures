/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree

/-!
# Curves, their genus, and the Picard group of a curve

A *curve* over a field `K` is a separated scheme of finite type over `K` whose underlying space
has Krull dimension at most one. For a smooth proper connected curve `C` over `K` the *genus* is
`g = dim_K H⁰(C, Ω¹_{C/K})`, the dimension of the space of global differential forms.

The Picard group `Pic(C)` of isomorphism classes of invertible `𝒪_C`-modules is already
available as `AlgebraicGeometry.Scheme.Pic`; on a curve it carries a *degree* map to `ℤ`, whose
kernel `Pic⁰(C)` is the subject of the Jacobian. A *Jacobian* of `C` is an abelian variety `J`
over `K` of dimension the genus of `C`, together with an isomorphism between the degree-zero
relative Picard functor `Pic⁰_{C/K}` and the functor of points of `J`.

The pinned Mathlib has neither a sheaf of relative Kähler differentials for schemes, nor
coherent cohomology of an `𝒪_X`-module, nor the relative Picard functor. Accordingly the
cotangent sheaf and the degree map are recorded here with `sorry` bodies, and the relative
Picard functor is taken as a parameter of `AlgebraicGeometry.IsJacobian` (it belongs to the
`sec-picard-framework` block of the blueprint).

## Main definitions

- `AlgebraicGeometry.IsCurve`: a separated, locally-of-finite-type morphism to `Spec K` whose
  source has topological Krull dimension at most one.
- `AlgebraicGeometry.Scheme.Hom.cotangent`: the sheaf `Ω¹_{X/S}` of relative Kähler
  differentials of a morphism of schemes (placeholder).
- `AlgebraicGeometry.genus`: the genus `dim_K Γ(C, Ω¹_{C/K})` of a curve.
- `AlgebraicGeometry.Scheme.Pic.degree`: the degree of an invertible module on a curve
  (placeholder).
- `AlgebraicGeometry.Scheme.picZero`: the degree-zero part `Pic⁰(C)` of the Picard group.
- `AlgebraicGeometry.IsJacobian`: the property of being a Jacobian of a curve.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {K : Type u} [Field K] {C : Scheme.{u}}

/-- Blueprint `sk-def-curve`: Curves and genus

Let `K` be a field (in the blueprint, algebraically closed). A *curve* over `K` is a separated
scheme of finite type over `K` of dimension at most one. Smoothness and properness of a curve
are the corresponding properties `Smooth` and `IsProper` of its structure morphism, so they are
not part of this class; the dimension condition is phrased with `topologicalKrullDim`, which is
valued in `WithBot ℕ∞` and is `⊥` exactly on the empty scheme. -/
class IsCurve {K : Type u} [Field K] {C : Scheme.{u}} (f : C ⟶ Spec (.of K)) : Prop where
  isSeparated : IsSeparated f
  locallyOfFiniteType : LocallyOfFiniteType f
  krullDim_le_one : topologicalKrullDim C ≤ 1

attribute [instance] IsCurve.isSeparated IsCurve.locallyOfFiniteType

/-- The sheaf of relative Kähler differentials `Ω¹_{X/S}` of a morphism of schemes.

Mathlib has no cotangent sheaf of a morphism of schemes yet (only the module of Kähler
differentials `Ω[S⁄R]` of a ring map), so this is a placeholder. -/
-- TODO(unify): sk-def-curve
noncomputable def Scheme.Hom.cotangent {X S : Scheme.{u}} (f : X ⟶ S) : X.Modules := sorry

/-- Blueprint `sk-def-curve`: Curves and genus

The *genus* of a smooth proper connected curve `C` over `K` is
`g = dim_K H⁰(C, Ω¹_{C/K})`, the `K`-dimension of the space of global sections of the sheaf of
relative differentials. Since `C` is proper the global sections form a finite-dimensional
`K`-vector space; the `K`-module structure on `Γ(Ω¹_{C/K}, ⊤)` comes from the `Γ(C, ⊤)`-module
structure by restriction of scalars along the `K`-algebra structure of `Γ(C, ⊤)`.

This definition makes sense for an arbitrary morphism `f : C ⟶ Spec K`, but is only the genus
in the intended sense when `f` is a smooth proper connected curve. -/
noncomputable def genus {K : Type u} [Field K] {C : Scheme.{u}} (f : C ⟶ Spec (.of K)) : ℕ :=
  letI := f.ΓAlgebra
  letI : Module K Γ(f.cotangent, ⊤) := Module.compHom _ (algebraMap K Γ(C, ⊤))
  Module.finrank K Γ(f.cotangent, ⊤)

/-- The degree of an invertible module on a curve.

On a smooth projective geometrically integral curve `C` over `K` the degree of an invertible
module is the degree of any associated Weil divisor; equivalently it is determined by the
Riemann-Roch formula `χ(L) = deg L + 1 - g`. Neither divisors on a scheme nor coherent
cohomology are available in the pinned Mathlib, so this is a placeholder. -/
-- TODO(unify): sk-def-av-pic
noncomputable def Scheme.Pic.degree {K : Type u} [Field K] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of K)) : C.Pic → ℤ := sorry

/-- Blueprint `sk-def-av-pic`: Pic, degree, Pic⁰

Let `C` be a smooth projective geometrically integral curve over a field `K`. Its Picard group
`Pic(C) = H¹(C_ét, 𝔾ₘ)` is the group of invertible `𝒪_C`-modules up to isomorphism; it is
available as `AlgebraicGeometry.Scheme.Pic`. The degree homomorphism `deg : Pic(C) → ℤ` is
`AlgebraicGeometry.Scheme.Pic.degree`, and `Pic⁰(C) := ker(deg)` is the subgroup of classes of
degree zero, recorded here as the subset `picZero f` of `C.Pic`.

The degree is not yet a bundled group homomorphism: the group structure on
`AlgebraicGeometry.Scheme.Pic` is the tensor product of invertible modules, which awaits the
monoidal structure on sheaves of modules (see
`AlgebraicGeometry.Scheme.Modules.tensorObj`). Once that lands, `picZero` should be upgraded to
the kernel of a `MonoidHom` and hence to a subgroup of `Pic(C)`. -/
def Scheme.picZero {K : Type u} [Field K] {C : Scheme.{u}} (f : C ⟶ Spec (.of K)) :
    Set C.Pic := {L | Scheme.Pic.degree f L = 0}

/-- Blueprint `sk-def-av-jacobian`: The Jacobian

Let `C` be a smooth projective geometrically integral curve over a field `K`, of genus `g`. A
*Jacobian of `C`* is a pair `(J, φ)` consisting of an abelian variety `J` over `K` of dimension
`g` together with an isomorphism of group-valued functors `φ : Pic⁰_{C/K} ≅ h_J` on `(Sch/K)`;
that is, `J` represents the degree-zero relative Picard functor.

The relative Picard functor `Pic⁰_{C/K}` belongs to the Picard-framework block of the
blueprint, so it enters here as the parameter `P : (Over (Spec (.of K)))ᵒᵖ ⥤ GrpCat`. The
functor of points of `J` as a group-valued functor is
`CategoryTheory.yonedaGrpObj J`, and the dimension of `J` is the topological Krull dimension of
its underlying space, compared with the genus of `C` inside `WithBot ℕ∞`.

Representability is stated as `Nonempty (P ≅ yonedaGrpObj J)` rather than as a chosen
isomorphism, so that `IsJacobian` is a `Prop`; the data of `φ` is recovered by choice. -/
structure IsJacobian {K : Type u} [Field K] {C : Scheme.{u}} (f : C ⟶ Spec (.of K))
    (P : (Over (Spec (.of K)))ᵒᵖ ⥤ GrpCat.{u}) (J : Over (Spec (.of K))) [GrpObj J] : Prop where
  isAbelianVariety : IsAbelianVariety J
  dim_eq : topologicalKrullDim J.left = (genus f : ℕ∞)
  represents : Nonempty (P ≅ CategoryTheory.yonedaGrpObj J)

end AlgebraicGeometry
