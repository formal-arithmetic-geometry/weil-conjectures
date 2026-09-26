/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.Mathlib.RepresentationTheory.Rep.Basic
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Basic
public import WeilConjectures.NumberTheory.Padics.Extension

@[expose] public section

/-!
# Local systems: the Galois correspondence and the lisse sheaf–representation dictionary

This file states the four steps that turn sheaf-theoretic statements about lisse sheaves on
a curve over a finite field into statements about representations of its Weil group:

- the Galois correspondence between finite locally constant sheaves of `Λ`-modules on a
  connected scheme and finite `Λ`-modules with a continuous action of the étale fundamental
  group;
- the resulting equivalence between lisse Weil sheaves and lisse Weil representations,
  matching short exact sequences and hence subobjects, quotients and subquotients;
- the existence of a Frobenius-stable integral model (an `𝒪_E`-lattice) of a lisse Weil
  representation;
- the identification of the ordinary étale `H⁰` with the invariants of the geometric
  fundamental group, equivariantly for the residual Frobenius.

## Implementation notes

The étale fundamental group of a scheme does not exist in Mathlib, and neither do lisse
`ℚ̄_ℓ`-sheaves. The renderings chosen here are therefore the following.

- In `AlgebraicGeometry.Scheme.exists_equivalence_isFiniteLocallyConstantSheaf` the group
  `π₁(Y, s)` is *existentially quantified* as a bundled profinite group
  (`ProfiniteGrp`, which packages "topological group, compact, T2, totally disconnected").
  The target category is the full subcategory of `Rep Λ G` cut out by
  `Rep.IsFiniteContinuous`. Mathlib's `CategoryTheory.ContAction` is not usable here: it
  requires `HasForget₂ V TopCat`, and there is no such instance for `ModuleCat Λ`. Since
  the modules in question are finite, the only sensible topology on them is the discrete
  one, for which continuity of the action is exactly openness of all the stabilizers; this
  is what `Rep.IsFiniteContinuous` says. Compatibility with the geometric stalk is the
  requested clause; exactness and the tensor structure are automatic for an equivalence of
  abelian categories and are not restated, and neither is the base change along
  `Λ → Λ'`, which would require the (not yet available) `ℓ`-adic coefficient formalism.

- `AlgebraicGeometry.WeilGroup.isLisseRep_exact` states the *consequence* of the lisse
  sheaf–representation equivalence that the rest of the block uses, since the source
  category of that equivalence — lisse `ℚ̄_ℓ`-Weil sheaves — cannot be written down: the
  lisse Weil representations form a full subcategory of `Rep ℚ̄_ℓ W(C₀)` closed under
  kernels, cokernels and extensions, and a short complex of lisse representations is short
  exact precisely when its geometric generic stalk is. Stating the equivalence with a
  subcategory of `Sheaf C.smallEtaleTopology (ModuleCat Λ)` would only reproduce
  `sk-i-real-galois` at a finite coefficient ring `Λ`, not the `ℚ̄_ℓ`-statement, and would
  therefore be less faithful, not more.

- In `AlgebraicGeometry.WeilGroup.IsLisse.exists_lattice` the finite extension `E/ℚ_ℓ` is
  existentially quantified as a finite-dimensional `IntermediateField ℚ_[l] (PadicAlgCl l)`,
  which is what makes "after replacing `E` by a finite extension" a true statement; the
  `𝒪_E`-module structure on `V` is the restriction of scalars along
  `𝒪_E → E → ℚ̄_ℓ`, introduced by `letI` inside the statement.

- In `AlgebraicGeometry.WeilGroup.globalSections_eq_invariants` the global sections
  `H⁰(U, F|_U)` are rendered, following the proof sketch, as the `π₁(U)`-equivariant maps
  from the constant rank-one sheaf, i.e. as
  `AlgebraicGeometry.WeilGroup.globalSections`. Mathlib's `CategoryTheory.Sheaf.H` is not
  applicable, as the lisse `ℚ̄_ℓ`-sheaf `F` itself is unavailable.

Throughout, the open subscheme `U₀ ⊆ C₀`, its Weil group `W(U₀)` and the restriction
homomorphism `W(U₀) → W(C₀)` are taken as hypotheses.

## Main definitions

- `AlgebraicGeometry.WeilGroup.isLisseRep`
- `AlgebraicGeometry.WeilGroup.globalSections`

## Main statements

- `AlgebraicGeometry.Scheme.exists_equivalence_isFiniteLocallyConstantSheaf`
- `AlgebraicGeometry.WeilGroup.isLisseRep_exact`
- `AlgebraicGeometry.WeilGroup.IsLisse.exists_lattice`
- `AlgebraicGeometry.WeilGroup.globalSections_eq_invariants`
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Blueprint `sk-i-real-galois`: Galois correspondence for finite local systems.

Let `Y` be a connected scheme, `s : Spec Ω ⟶ Y` a geometric point and `Λ` a finite ring.
Then there is a profinite group `G` — the étale fundamental group `π₁(Y, s)`, which does
not exist in Lean and is therefore existentially quantified as a `ProfiniteGrp` — together
with an equivalence between the category of finite locally constant sheaves of
`Λ`-modules on `Y_ét` and the category of finite `Λ`-modules with a continuous
`G`-action, compatible with the geometric stalk at `s`: composing the equivalence with the
forgetful functor to `ModuleCat Λ` gives back the fiber functor
`(Scheme.pointSmallEtale s).sheafFiber`.

Exactness and compatibility with `⊗_Λ` are automatic consequences of the equivalence being
an equivalence of abelian (monoidal) categories; the compatibility with base change along a
map `Λ → Λ'` of finite rings is not restated here, see the module implementation notes. -/
theorem Scheme.exists_equivalence_isFiniteLocallyConstantSheaf (Y : Scheme.{u})
    [ConnectedSpace Y] {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    ∃ (G : ProfiniteGrp.{u})
      (e : ObjectProperty.FullSubcategory
            (fun F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) ↦
              Scheme.IsFiniteLocallyConstantSheaf F) ≌
          ObjectProperty.FullSubcategory (Rep.IsFiniteContinuous (Λ := Λ) (G := G))),
      Nonempty (e.functor ⋙ ObjectProperty.ι _ ⋙
          forget₂ (Rep.{u + 1} Λ G) (ModuleCat.{u + 1} Λ) ≅
        ObjectProperty.ι _ ⋙ (Scheme.pointSmallEtale s).sheafFiber) := by
  sorry

variable {K : Type u} [Field K] {C U : Scheme.{u}} {p : C ⟶ Spec (.of K)}
  {pU : U ⟶ Spec (.of K)}

namespace WeilGroup

/-- Blueprint `sk-i-real-sheaves`: The lisse sheaf–representation equivalence.

The property of an object of `Rep ℚ̄_ℓ W(C₀)` of being a *lisse Weil representation*: the
underlying `ℚ̄_ℓ`-vector space is finite dimensional and the geometric subgroup `π₁(C)`
acts continuously (`AlgebraicGeometry.WeilGroup.IsLisse`). Under the equivalence of
`sk-i-real-sheaves` these are exactly the objects corresponding to lisse Weil sheaves on
`C₀`. -/
def isLisseRep (W : WeilGroup p) (l : ℕ) [Fact l.Prime] :
    ObjectProperty (Rep.{0} (PadicAlgCl l) W.carrier) :=
  fun X ↦ ∃ _ : FiniteDimensional (PadicAlgCl l) X.V, W.IsLisse l X.ρ

/-- Blueprint `sk-i-real-sheaves`: The lisse sheaf–representation equivalence.

The geometric-generic-stalk functor is an exact equivalence between lisse Weil sheaves on
`C₀` and lisse Weil representations of `W(C₀)`. Since lisse `ℚ̄_ℓ`-sheaves are not
available in Lean, what is stated here is the consequence used by the rest of the block:
the lisse Weil representations are closed under kernels, cokernels and extensions inside
`Rep ℚ̄_ℓ W(C₀)` — so subobjects, quotients and subquotients of lisse objects are again
lisse — and a short complex of lisse Weil representations is short exact exactly when its
geometric generic stalk, i.e. its image under the forgetful functor to `ModuleCat ℚ̄_ℓ`,
is short exact. See the module implementation notes for this choice. -/
theorem isLisseRep_exact (W : WeilGroup p) (l : ℕ) [Fact l.Prime] :
    ObjectProperty.IsClosedUnderKernels (W.isLisseRep l) ∧
      ObjectProperty.IsClosedUnderCokernels (W.isLisseRep l) ∧
      ObjectProperty.IsClosedUnderExtensions (W.isLisseRep l) ∧
      ∀ S : ShortComplex (Rep.{0} (PadicAlgCl l) W.carrier), W.isLisseRep l S.X₁ →
        W.isLisseRep l S.X₂ → W.isLisseRep l S.X₃ → (S.ShortExact ↔
          (S.map (forget₂ (Rep.{0} (PadicAlgCl l) W.carrier)
            (ModuleCat.{0} (PadicAlgCl l)))).ShortExact) := by
  sorry

/-- Blueprint `sk-p-real-integral`: Integral models.

Let `ρ` be a lisse Weil representation on `V` over `ℚ̄_ℓ` and let `U₀ ⊆ C₀` be a nonempty
open subscheme, with Weil group `W(U₀)`, geometric fundamental group `π₁(U) = ker deg` and
restriction homomorphism `res : W(U₀) → W(C₀)`. Then, after replacing the coefficient field
by a finite extension `E/ℚ_ℓ` — here a finite-dimensional intermediate field of
`ℚ_ℓ ⊆ ℚ̄_ℓ` — there is an `𝒪_E`-lattice `L ⊂ V`, that is a free `𝒪_E`-submodule of rank
`dim V` whose `ℚ̄_ℓ`-span is all of `V`, which is stable under `ρ (π₁(U))` and whose
reduction modulo `𝔪_E ^ n` has finite `π₁(U)`-image for every `n`.

The finiteness of the image in `Aut (L / 𝔪_E ^ n L)` is expressed as the finiteness of the
set of maps `L → V / 𝔪_E ^ n L` induced by the elements of `π₁(U)`; since `L` is stable and
`L / 𝔪_E ^ n L → V / 𝔪_E ^ n L` is injective, this is the same condition, and it avoids
having to restrict `ρ g` to `L` before the lattice is known to be stable. -/
theorem IsLisse.exists_lattice {l : ℕ} [Fact l.Prime] {W : WeilGroup p} {V : Type}
    [AddCommGroup V] [Module (PadicAlgCl l) V] [FiniteDimensional (PadicAlgCl l) V]
    {ρ : Representation (PadicAlgCl l) W.carrier V} (hρ : W.IsLisse l ρ) (j : U ⟶ C)
    [IsOpenImmersion j] [Nonempty U] (hj : j ≫ p = pU) (WU : WeilGroup pU)
    (res : WU.carrier →* W.carrier) (hres : Continuous res)
    (hdeg : ∀ g, W.deg (res g) = WU.deg g) :
    ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧
      letI : Module (PadicAlgCl.integers l (E : Type)) V :=
        Module.compHom V ((algebraMap (E : Type) (PadicAlgCl l)).comp
          (PadicAlgCl.integers l (E : Type)).subtype)
      ∃ L : Submodule (PadicAlgCl.integers l (E : Type)) V,
        Module.Free (PadicAlgCl.integers l (E : Type)) L ∧
        Module.finrank (PadicAlgCl.integers l (E : Type)) L =
          Module.finrank (PadicAlgCl l) V ∧
        Submodule.span (PadicAlgCl l) (L : Set V) = ⊤ ∧
        (∀ g : WU.geometric, ∀ x ∈ L, ρ (res g) x ∈ L) ∧
        ∀ n : ℕ, (Set.range fun g : WU.geometric ↦ fun x : L ↦
          Submodule.Quotient.mk (p := (IsLocalRing.maximalIdeal
            (PadicAlgCl.integers l (E : Type)) ^ n) • L) (ρ (res g) x)).Finite := by
  sorry

/-- Blueprint `sk-p-real-sections`: Global sections as invariants.

The global sections `H⁰(U, F|_U)` of the lisse sheaf `F` with geometric generic stalk
`(V, ρ)`, rendered as in the proof sketch: a global section is a morphism from the constant
rank-one sheaf, i.e. a `π₁(U)`-equivariant `ℚ̄_ℓ`-linear map `ℚ̄_ℓ → V`, where `π₁(U)` acts
on `V` through `res`. -/
noncomputable def globalSections (W : WeilGroup p) (l : ℕ) [Fact l.Prime] {V : Type}
    [AddCommGroup V] [Module (PadicAlgCl l) V] (ρ : Representation (PadicAlgCl l) W.carrier V)
    (WU : WeilGroup pU) (res : WU.carrier →* W.carrier) :
    Submodule (PadicAlgCl l) (PadicAlgCl l →ₗ[PadicAlgCl l] V) :=
  (Representation.linHom (Representation.trivial (PadicAlgCl l) WU.geometric (PadicAlgCl l))
    ((ρ.comp res).comp WU.geometric.subtype)).invariants

/-- Blueprint `sk-p-real-sections`: Global sections as invariants.

For a lisse Weil representation `(V, ρ)` and a nonempty open `U₀ ⊆ C₀` with Weil group
`W(U₀)` and restriction `res : W(U₀) → W(C₀)`, the global sections
`H⁰(U, F|_U) = Hom_{π₁(U)}(𝟙, V)` are the invariants `V ^ (π₁(U))`, by evaluation at `1`.

Both sides carry a residual action of the geometric Frobenius `F = ρ (res γ)`: `π₁(U)` is
normal in `W(U₀)`, so the degree-one lift `γ` of `W(U₀)` preserves the invariants, and it
acts on global sections by post-composition. The last clause says that the identification
is equivariant for these two operators. -/
theorem globalSections_eq_invariants {l : ℕ} [Fact l.Prime] {W : WeilGroup p} {V : Type}
    [AddCommGroup V] [Module (PadicAlgCl l) V] [FiniteDimensional (PadicAlgCl l) V]
    {ρ : Representation (PadicAlgCl l) W.carrier V} (hρ : W.IsLisse l ρ) (j : U ⟶ C)
    [IsOpenImmersion j] [Nonempty U] (hj : j ≫ p = pU) (WU : WeilGroup pU)
    (res : WU.carrier →* W.carrier) (hres : Continuous res)
    (hdeg : ∀ g, W.deg (res g) = WU.deg g) :
    ∃ (hγ : ∀ f ∈ W.globalSections l ρ WU res,
        (ρ (res WU.γ)).comp f ∈ W.globalSections l ρ WU res)
      (hinv : ∀ v ∈ (Representation.invariants ((ρ.comp res).comp WU.geometric.subtype)),
        ρ (res WU.γ) v ∈ (Representation.invariants ((ρ.comp res).comp WU.geometric.subtype)))
      (e : W.globalSections l ρ WU res ≃ₗ[PadicAlgCl l]
        (Representation.invariants ((ρ.comp res).comp WU.geometric.subtype))),
      ∀ f : W.globalSections l ρ WU res,
        e ⟨(ρ (res WU.γ)).comp (f : PadicAlgCl l →ₗ[PadicAlgCl l] V), hγ f f.2⟩ =
          ⟨ρ (res WU.γ) (e f), hinv (e f) (e f).2⟩ := by
  sorry

end WeilGroup

end AlgebraicGeometry
