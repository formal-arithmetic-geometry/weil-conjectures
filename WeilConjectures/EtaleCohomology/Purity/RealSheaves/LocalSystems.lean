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
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Basic
public import WeilConjectures.Mathlib.RepresentationTheory.Continuous.Basic
public import WeilConjectures.NumberTheory.Padics.Extension

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
  `Rep.IsFiniteContinuous`. Compatibility with the geometric stalk is the requested clause;
  exactness and the tensor structure are automatic for an equivalence of abelian categories
  and are not restated. The compatibility with base change along a map `Λ → Λ'` of finite
  rings is not restated either: the group `G` is existentially quantified, so two invocations
  of the theorem, at `Λ` and at `Λ'`, produce unrelated groups and the square cannot even be
  written down. Naming `π₁` — through `CategoryTheory.PreGaloisCategory.IsFundamentalGroup`,
  once the Galois category of finite étale covers of a scheme exists — is what would make the
  base change clause statable.

- `AlgebraicGeometry.WeilGroup.isLisseRep` is a full subcategory of `Rep ℚ̄_ℓ W(C₀)`, and the
  content of the lisse sheaf–representation equivalence used by the rest of the block is
  recorded by the closure properties
  `AlgebraicGeometry.WeilGroup.isLisseRep.isClosedUnderKernels` and its companions together
  with `AlgebraicGeometry.WeilGroup.isLisseRep_shortExact_iff`, since the source category of
  that equivalence — lisse `ℚ̄_ℓ`-Weil sheaves — cannot be written down here.

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

The open subcurve `U₀ ⊆ C₀`, its Weil group `W(U₀)` and the restriction homomorphism
`W(U₀) → W(C₀)` enter through `AlgebraicGeometry.WeilGroup.Restriction`, which is also what
`AlgebraicGeometry.BoundaryDatum` extends.

## Main definitions

- `AlgebraicGeometry.WeilGroup.isLisseRep`
- `AlgebraicGeometry.WeilGroup.globalSections`

## Main statements

- `AlgebraicGeometry.Scheme.exists_equivalence_isFiniteLocallyConstantSheaf`
- `AlgebraicGeometry.WeilGroup.isLisseRep_shortExact_iff`
- `AlgebraicGeometry.WeilGroup.IsLisse.exists_lattice`
- `AlgebraicGeometry.WeilGroup.globalSections_eq_invariants`
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Blueprint `sk-i-real-galois`: Galois correspondence for finite local systems.

The steps *sheaves and covers* and *linear structure* of the proof, for a named fundamental
group: let `Y` be a connected scheme, `s : Spec Ω ⟶ Y` a geometric point, `Λ` a finite ring
and `G` a fundamental group of the fibre functor `AlgebraicGeometry.Scheme.FiniteEtale.fiber s`
on finite étale `Y`-schemes, i.e. `G = π₁(Y, s)`. Then the geometric stalk at `s` is an
equivalence between finite locally constant sheaves of `Λ`-modules on `Y_ét` and finite
`Λ`-modules with a continuous `G`-action.

Mathematically, a finite locally constant sheaf of sets is represented by a finite étale
`Y`-scheme, whose geometric fibre is the stalk at `s`; the Galois correspondence
`AlgebraicGeometry.Scheme.FiniteEtale.equivalenceContAction` identifies these with finite
continuous `G`-sets, and a `Λ`-module structure on the sheaf is transported to one on the
`G`-set. -/
theorem Scheme.exists_equivalence_isFiniteLocallyConstantSheaf_of_isFundamentalGroup
    (Y : Scheme.{u}) [ConnectedSpace Y] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ Y) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (G : ProfiniteGrp.{u})
    [∀ P, MulAction G ((Scheme.FiniteEtale.fiber s).obj P)]
    [PreGaloisCategory.IsFundamentalGroup (Scheme.FiniteEtale.fiber s) G] :
    ∃ e : ObjectProperty.FullSubcategory
            (fun F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) ↦
              Scheme.IsFiniteLocallyConstantSheaf F) ≌
          ObjectProperty.FullSubcategory (Rep.IsFiniteContinuous (Λ := Λ) (G := G)),
      Nonempty (e.functor ⋙ ObjectProperty.ι _ ⋙
          forget₂ (Rep.{u + 1} Λ G) (ModuleCat.{u + 1} Λ) ≅
        ObjectProperty.ι _ ⋙ (Scheme.pointSmallEtale s).sheafFiber) := by
  sorry

/-- Blueprint `sk-i-real-galois`: Galois correspondence for finite local systems.

Let `Y` be a connected scheme, `s : Spec Ω ⟶ Y` a geometric point and `Λ` a finite ring.
Then there is a profinite group `G` — the étale fundamental group `π₁(Y, s)`, which does
not exist in Lean and is therefore existentially quantified as a `ProfiniteGrp` — together
with an equivalence between the category of finite locally constant sheaves of
`Λ`-modules on `Y_ét` and the category of finite `Λ`-modules with a continuous
`G`-action, compatible with the geometric stalk at `s`: the triangle

```
    FLC(Y_ét)  ──e.functor──▶  Rep^{fin,cont}_Λ(G)
         │                            │
         │ sheafFiber s               │ forget₂
         ▼                            ▼
     ModuleCat Λ  ══════════════  ModuleCat Λ
```

commutes up to isomorphism.

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
  obtain ⟨G, _, _⟩ := Scheme.FiniteEtale.exists_isFundamentalGroup s
  exact ⟨G, exists_equivalence_isFiniteLocallyConstantSheaf_of_isFundamentalGroup Y s Λ G⟩

variable {K : Type u} [Field K] [Finite K] {C U : Scheme.{u}} {p : C ⟶ Spec (.of K)}
  [IsCurve p] {pU : U ⟶ Spec (.of K)} [IsCurve pU]

namespace WeilGroup

/-- Blueprint `sk-i-real-sheaves`: The lisse sheaf–representation equivalence.

The property of an object of `Rep ℚ̄_ℓ W(C₀)` of being a *lisse Weil representation*: the
underlying `ℚ̄_ℓ`-vector space is finite dimensional and the geometric subgroup `π₁(C)`
acts continuously (`AlgebraicGeometry.WeilGroup.IsLisse`). Under the equivalence of
`sk-i-real-sheaves` these are exactly the objects corresponding to lisse Weil sheaves on
`C₀`. -/
def isLisseRep (W : WeilGroup p) (l : ℕ) [Fact l.Prime] :
    ObjectProperty (Rep.{u} (PadicAlgCl l) W.carrier) :=
  fun X ↦ FiniteDimensional (PadicAlgCl l) X.V ∧ W.IsLisse l X.ρ

variable (W : WeilGroup p) (l : ℕ) [Fact l.Prime]

/-- Blueprint `sk-i-real-sheaves`: The lisse sheaf–representation equivalence.

Lisse Weil representations are closed under kernels, so a subobject of a lisse Weil
representation is again lisse. -/
instance isLisseRep.isClosedUnderKernels :
    ObjectProperty.IsClosedUnderKernels (W.isLisseRep l) := by
  sorry

/-- Blueprint `sk-i-real-sheaves`: The lisse sheaf–representation equivalence.

Lisse Weil representations are closed under cokernels, so a quotient of a lisse Weil
representation is again lisse. -/
instance isLisseRep.isClosedUnderCokernels :
    ObjectProperty.IsClosedUnderCokernels (W.isLisseRep l) := by
  sorry

/-- Blueprint `sk-i-real-sheaves`: The lisse sheaf–representation equivalence.

Lisse Weil representations are closed under extensions. -/
instance isLisseRep.isClosedUnderExtensions :
    ObjectProperty.IsClosedUnderExtensions (W.isLisseRep l) := by
  sorry

/-- Blueprint `sk-i-real-sheaves`: The lisse sheaf–representation equivalence.

A short complex of lisse Weil representations is short exact exactly when its geometric
generic stalk, i.e. its image under the forgetful functor to `ModuleCat ℚ̄_ℓ`, is short exact.
This is the form in which the exactness of the geometric-generic-stalk equivalence of
`sk-i-real-sheaves` is used, lisse `ℚ̄_ℓ`-sheaves themselves being unavailable. -/
theorem isLisseRep_shortExact_iff (S : ShortComplex (Rep.{u} (PadicAlgCl l) W.carrier))
    (h₁ : W.isLisseRep l S.X₁) (h₂ : W.isLisseRep l S.X₂) (h₃ : W.isLisseRep l S.X₃) :
    S.ShortExact ↔ (S.map (forget₂ (Rep.{u} (PadicAlgCl l) W.carrier)
      (ModuleCat.{u} (PadicAlgCl l)))).ShortExact := by
  sorry

variable {W l}

/-- Blueprint `sk-p-real-integral`: Integral models.

Let `ρ` be a lisse Weil representation on `V` over `ℚ̄_ℓ` and let `R` be a restriction of Weil
groups along a nonempty open subscheme `j : U₀ ⊆ C₀`. Then, after replacing the coefficient
field by a finite extension `E/ℚ_ℓ` — here a finite-dimensional intermediate field of
`ℚ_ℓ ⊆ ℚ̄_ℓ` — there is an `𝒪_E`-lattice `L ⊂ V`, that is a free `𝒪_E`-submodule of rank
`dim V` whose `ℚ̄_ℓ`-span is all of `V`, which is stable under `ρ (π₁(U))` and whose
reduction modulo `𝔪_E ^ n` has finite `π₁(U)`-image for every `n`.

The finiteness of the image in `Aut (L / 𝔪_E ^ n L)` is expressed as the finiteness of the
set of maps `L → V / 𝔪_E ^ n L` induced by the elements of `π₁(U)`; since `L` is stable and
`L / 𝔪_E ^ n L → V / 𝔪_E ^ n L` is injective, this is the same condition, and it avoids
having to restrict `ρ g` to `L` before the lattice is known to be stable. -/
theorem IsLisse.exists_lattice {l : ℕ} [Fact l.Prime] {W : WeilGroup p} {V : Type u}
    [AddCommGroup V] [Module (PadicAlgCl l) V] [FiniteDimensional (PadicAlgCl l) V]
    {ρ : Representation (PadicAlgCl l) W.carrier V} (hρ : W.IsLisse l ρ) {j : U ⟶ C}
    [IsOpenImmersion j] [Nonempty U] {WU : WeilGroup pU} (R : Restriction j WU W) :
    ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧
      letI : Module (PadicAlgCl.integers l (E : Type)) V :=
        Module.compHom V ((algebraMap (E : Type) (PadicAlgCl l)).comp
          (PadicAlgCl.integers l (E : Type)).subtype)
      ∃ L : Submodule (PadicAlgCl.integers l (E : Type)) V,
        Module.Free (PadicAlgCl.integers l (E : Type)) L ∧
        Module.finrank (PadicAlgCl.integers l (E : Type)) L =
          Module.finrank (PadicAlgCl l) V ∧
        Submodule.span (PadicAlgCl l) (L : Set V) = ⊤ ∧
        (∀ g : WU.geometric, ∀ x ∈ L, ρ (R.restrict g) x ∈ L) ∧
        ∀ n : ℕ, (Set.range fun g : WU.geometric ↦ fun x : L ↦
          Submodule.Quotient.mk (p := (IsLocalRing.maximalIdeal
            (PadicAlgCl.integers l (E : Type)) ^ n) • L) (ρ (R.restrict g) x)).Finite := by
  sorry

/-- Blueprint `sk-p-real-sections`: Global sections as invariants.

The global sections `H⁰(U, F|_U)` of the lisse sheaf `F` with geometric generic stalk
`(V, ρ)`, rendered as in the proof sketch: a global section is a morphism from the constant
rank-one sheaf, i.e. a `π₁(U)`-equivariant `ℚ̄_ℓ`-linear map `ℚ̄_ℓ → V`, where `π₁(U)` acts
on `V` through `res`. -/
noncomputable def globalSections (W : WeilGroup p) (l : ℕ) [Fact l.Prime] {V : Type u}
    [AddCommGroup V] [Module (PadicAlgCl l) V] (ρ : Representation (PadicAlgCl l) W.carrier V)
    (WU : WeilGroup pU) (res : WU.carrier →* W.carrier) :
    Submodule (PadicAlgCl l) (PadicAlgCl l →ₗ[PadicAlgCl l] V) :=
  (Representation.linHom (Representation.trivial (PadicAlgCl l) WU.geometric (PadicAlgCl l))
    ((ρ.comp res).comp WU.geometric.subtype)).invariants

section Sections

variable {l : ℕ} [Fact l.Prime] {W : WeilGroup p} {V : Type u} [AddCommGroup V]
  [Module (PadicAlgCl l) V] (ρ : Representation (PadicAlgCl l) W.carrier V) {j : U ⟶ C}
  [IsOpenImmersion j] [Nonempty U] {WU : WeilGroup pU} (R : Restriction j WU W)

/-- Blueprint `sk-p-real-sections`: Global sections as invariants.

The geometric Frobenius `F = ρ (res γ)` acts on global sections by post-composition: `π₁(U)`
is normal in `W(U₀)`, so post-composing an equivariant map with `F` gives an equivariant
map. -/
theorem comp_mem_globalSections (f : PadicAlgCl l →ₗ[PadicAlgCl l] V)
    (hf : f ∈ W.globalSections l ρ WU R.restrict) :
    (ρ (R.restrict WU.frobeniusLift)).comp f ∈ W.globalSections l ρ WU R.restrict := by
  sorry

/-- Blueprint `sk-p-real-sections`: Global sections as invariants.

The geometric Frobenius `F = ρ (res γ)` preserves the invariants `V ^ (π₁(U))`, because
`π₁(U)` is normal in `W(U₀)`. -/
theorem frobeniusLift_mem_invariants (v : V)
    (hv : v ∈ Representation.invariants ((ρ.comp R.restrict).comp WU.geometric.subtype)) :
    ρ (R.restrict WU.frobeniusLift) v ∈
      Representation.invariants ((ρ.comp R.restrict).comp WU.geometric.subtype) := by
  sorry

/-- Blueprint `sk-p-real-sections`: Global sections as invariants.

For a lisse Weil representation `(V, ρ)` and a restriction `R` of Weil groups along a nonempty
open `U₀ ⊆ C₀`, the global sections `H⁰(U, F|_U) = Hom_{π₁(U)}(𝟙, V)` are the invariants
`V ^ (π₁(U))`, by evaluation at `1`.

Both sides carry a residual action of the geometric Frobenius `F = ρ (res γ)`
(`AlgebraicGeometry.WeilGroup.comp_mem_globalSections` and
`AlgebraicGeometry.WeilGroup.frobeniusLift_mem_invariants`), and the identification is
equivariant for it:

```
    H⁰(U, F|_U) ──── e ────▶ V^{π₁(U)}
          │                      │
    F ∘ ─ │                      │ F
          ▼                      ▼
    H⁰(U, F|_U) ──── e ────▶ V^{π₁(U)}
```
-/
theorem globalSections_eq_invariants [FiniteDimensional (PadicAlgCl l) V]
    (hρ : W.IsLisse l ρ) :
    ∃ e : W.globalSections l ρ WU R.restrict ≃ₗ[PadicAlgCl l]
      Representation.invariants ((ρ.comp R.restrict).comp WU.geometric.subtype),
      ∀ f : W.globalSections l ρ WU R.restrict,
        e ⟨(ρ (R.restrict WU.frobeniusLift)).comp (f : PadicAlgCl l →ₗ[PadicAlgCl l] V),
            comp_mem_globalSections ρ R f f.2⟩ =
          ⟨ρ (R.restrict WU.frobeniusLift) (e f),
            frobeniusLift_mem_invariants ρ R (e f) (e f).2⟩ := by
  sorry

end Sections

end WeilGroup

end AlgebraicGeometry
