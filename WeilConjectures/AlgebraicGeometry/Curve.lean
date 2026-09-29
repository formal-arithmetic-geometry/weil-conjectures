/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.PicardFunctor
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree

/-!
# Curves, their genus, and the Picard group of a curve

A *curve* over a field `K` is a separated scheme of finite type over `K` whose underlying space
has Krull dimension at most one. "Of finite type" is spelled as `LocallyOfFiniteType` together
with `QuasiCompact`, Mathlib having no bundled class for the conjunction. For a smooth proper
connected curve `C` over `K` the *genus* is `g = dim_K H⁰(C, Ω¹_{C/K})`, the dimension of the
space of global differential forms.

The Picard group `Pic(C)` of isomorphism classes of invertible `𝒪_C`-modules is
`AlgebraicGeometry.Scheme.Pic`, introduced in
`WeilConjectures.AlgebraicGeometry.PicardFunctor`; on a curve it carries a *degree* map to `ℤ`,
whose kernel `Pic⁰(C)` is the subject of the Jacobian.

The sheaf `Ω¹_{C/K}` is `AlgebraicGeometry.Scheme.Hom.relativeDifferentials`, from
`WeilConjectures.AlgebraicGeometry.Modules.Differentials`. The pinned Mathlib has no coherent
cohomology of an `𝒪_X`-module, so the degree map is declared here as an `opaque` constant: it
depends genuinely on its arguments and introduces no `sorryAx`, but it satisfies no equations,
so no statement about `picDegree` can be proved before it is replaced.

## Main definitions

- `AlgebraicGeometry.IsCurve`: a separated morphism of finite type to `Spec K` whose source has
  topological Krull dimension at most one.
- `AlgebraicGeometry.Scheme.Hom.relativeDifferentials`: the sheaf `Ω¹_{X/S}` of relative
  differentials (see `WeilConjectures.AlgebraicGeometry.Modules.Differentials`).
- `AlgebraicGeometry.Scheme.Hom.genus`: the genus `dim_K Γ(C, Ω¹_{C/K})` of a curve.
- `AlgebraicGeometry.Scheme.Hom.picDegree`: the degree of an invertible module on a curve
  (placeholder).
- `AlgebraicGeometry.Scheme.Hom.picZero`: the degree-zero part `Pic⁰(C)` of the Picard group.
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
class IsCurve (f : C ⟶ Spec (.of K)) : Prop
    extends IsSeparated f, LocallyOfFiniteType f, QuasiCompact f where
  /-- The underlying space of a curve has dimension at most one. -/
  krullDim_le_one : topologicalKrullDim C ≤ 1

/-- Blueprint `sk-def-curve`: Curves and genus

The *genus* of a smooth proper connected curve `C` over `K` is
`g = dim_K H⁰(C, Ω¹_{C/K})`, the `K`-dimension of the space of global sections of the sheaf of
relative differentials. Since `C` is proper the global sections form a finite-dimensional
`K`-vector space; the `K`-module structure on `Γ(Ω¹_{C/K}, ⊤)` comes from the `Γ(C, ⊤)`-module
structure by restriction of scalars along the `K`-algebra structure of `Γ(C, ⊤)`.

This definition makes sense for an arbitrary morphism `f : C ⟶ Spec K`, but is only the genus
in the intended sense when `f` is a smooth proper connected curve. -/
noncomputable def Scheme.Hom.genus (f : C ⟶ Spec (.of K)) : ℕ :=
  letI := f.ΓAlgebra
  letI : Module K Γ(f.relativeDifferentials, ⊤) := Module.compHom _ (algebraMap K Γ(C, ⊤))
  Module.finrank K Γ(f.relativeDifferentials, ⊤)

/-- The degree of an invertible module on a curve.

On a smooth projective geometrically integral curve `C` over `K` the degree of an invertible
module is the degree of any associated Weil divisor; equivalently it is determined by the
Riemann-Roch formula `χ(L) = deg L + 1 - g`. Neither divisors on a scheme nor coherent
cohomology are available in the pinned Mathlib, so this is an `opaque` placeholder; it
satisfies no equations. -/
-- TODO(unify): sk-def-av-pic
opaque Scheme.Hom.picDegree (f : C ⟶ Spec (.of K)) : C.Pic → ℤ := fun _ ↦ 0

/-- Blueprint `sk-def-av-pic`: Pic, degree, Pic⁰

Let `C` be a smooth projective geometrically integral curve over a field `K`. Its Picard group
`Pic(C) = H¹(C_ét, 𝔾ₘ)` is the group of invertible `𝒪_C`-modules up to isomorphism; it is
`AlgebraicGeometry.Scheme.Pic`. The degree homomorphism `deg : Pic(C) → ℤ` is
`AlgebraicGeometry.Scheme.Hom.picDegree`, and `Pic⁰(C) := ker(deg)` is the subgroup of classes
of degree zero, recorded here as the subset `f.picZero` of `C.Pic`.

The degree is not yet a bundled group homomorphism: the group structure on
`AlgebraicGeometry.Scheme.Pic` is the tensor product of invertible modules, which awaits the
monoidal structure on sheaves of modules (see
`AlgebraicGeometry.Scheme.Modules.tensorObj`). Once that lands, `picZero` should be upgraded to
the kernel of a `MonoidHom` and hence to a subgroup of `Pic(C)`. -/
def Scheme.Hom.picZero (f : C ⟶ Spec (.of K)) : Set C.Pic :=
  {L | f.picDegree L = 0}

end AlgebraicGeometry
