/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant
public import WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.ConstructibleSheaf.Biproduct
public import WeilConjectures.ConstructibleSheaf.OfForget
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Basic
public import WeilConjectures.Mathlib.RepresentationTheory.Continuous.Basic
public import WeilConjectures.NumberTheory.Padics.Extension
public import WeilConjectures.RepresentationTheory.IntegralModel

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

Lisse `ℚ̄_ℓ`-sheaves do not exist in Mathlib. The renderings chosen here are therefore the
following.

- The étale fundamental group `π₁(Y, s)` is named as a fundamental group
  (`CategoryTheory.PreGaloisCategory.IsFundamentalGroup`) of the fibre functor
  `AlgebraicGeometry.Scheme.FiniteEtale.fiber s` on finite étale `Y`-schemes.
  `AlgebraicGeometry.Scheme.exists_equivalence_isFiniteLocallyConstantSheaf_of_isFundamentalGroup`
  states the Galois correspondence for any such group `G`, and
  `AlgebraicGeometry.Scheme.exists_equivalence_isFiniteLocallyConstantSheaf` deduces the
  version with `G` existentially quantified as a bundled profinite group (`ProfiniteGrp`).
  The target category is the full subcategory of `Rep Λ G` cut out by
  `Rep.IsFiniteContinuous`. Compatibility with the geometric stalk is the requested clause; it
  is an isomorphism of underlying `Λ`-modules only, not tied to the action of `G` on geometric
  fibres. Exactness is `AlgebraicGeometry.Scheme.isFiniteLocallyConstantSheaf_shortExact_iff`
  (in `WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalSystemsExact`). Compatibility
  with `⊗_Λ` is *not* a formal consequence of the equivalence (an equivalence of abelian
  categories need not be monoidal); it is proved in
  `WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalSystemsTensor`, see
  `AlgebraicGeometry.Scheme.exists_equivalence_isFiniteLocallyConstantSheaf_tensor`. The
  compatibility with base change along a map `Λ → Λ'` of
  finite rings is not restated either; with `G` fixed as in the `_of_isFundamentalGroup`
  version it could now be written down, but it is not part of the statement here.

- `AlgebraicGeometry.WeilGroup.isLisseRep` is a full subcategory of `Rep ℚ̄_ℓ W(C₀)`, and the
  content of the lisse sheaf–representation equivalence used by the rest of the block is
  recorded by the closure properties
  `AlgebraicGeometry.WeilGroup.isLisseRep.isClosedUnderKernels` and its companions together
  with `AlgebraicGeometry.WeilGroup.isLisseRep_shortExact_iff`. The equivalence itself, from lisse
  Weil sheaves, is `AlgebraicGeometry.WeilGroup.exists_equivalence_isLisse`; its exactness is
  `AlgebraicGeometry.WeilGroup.isLisse_shortExact_iff`.
  Closure under extensions is *not* recorded: inside `Rep ℚ̄_ℓ W(C₀)` it fails, since a
  discontinuous additive character `c` of `π₁(C)` (for instance of a quotient `ℤ_ℓ`) gives the
  non-lisse extension `g ↦ !![1, c g; 0, 1]` of the trivial line by itself. An extension of
  lisse sheaves is lisse, but its representation is continuous for a reason — it comes from a
  sheaf — that is invisible on the representation side.

- In `AlgebraicGeometry.WeilGroup.IsLisse.exists_lattice` the finite extension `E/ℚ_ℓ` is
  existentially quantified as a finite-dimensional `IntermediateField ℚ_[l] (PadicAlgCl l)`,
  which is what makes "after replacing `E` by a finite extension" a true statement; the
  `𝒪_E`-module structure on `V` is the restriction of scalars along
  `𝒪_E → E → ℚ̄_ℓ`, introduced by `letI` inside the statement.

- `AlgebraicGeometry.WeilGroup.globalSections_eq_invariants` is the representation-theoretic
  step of the proof sketch: the `π₁(U)`-equivariant maps from the trivial line
  (`AlgebraicGeometry.WeilGroup.globalSections`) are the invariants. The statement about the
  étale global sections `H⁰(Ū, F|_U)` of a lisse Weil sheaf is
  `AlgebraicGeometry.WeilGroup.exists_globalSections_upperStar_linearEquiv_invariants`.

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

namespace CategoryTheory

open Limits

section PairAux

variable {C : Type*} [Category* C] (H : C ⥤ Type _)

variable {H} {A B : C} [HasBinaryProduct A B] [PreservesLimit (pair A B) H]

end PairAux

end CategoryTheory

namespace AlgebraicGeometry

section BiprodAux

variable {C : Type*} [Category C] [Preadditive C] [Limits.HasBinaryBiproducts C]
  {R : Type*} [Ring R] (H : C ⥤ ModuleCat R) [H.Additive] {X X' : C}

end BiprodAux

section GaloisAction

/-! ### The Galois action on stalks of finite locally constant sheaves -/

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)

variable (G : Type u) [Group G] [∀ P, MulAction G ((Scheme.FiniteEtale.fiber s).obj P)]

section Linear

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

instance : ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).Additive :=
  have : Limits.HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    Limits.hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  have : ((Scheme.pointSmallEtale s).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  have : Limits.PreservesBinaryBiproducts
      ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)) :=
    Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  Functor.additive_of_preservesBinaryBiproducts _

end Linear

end GaloisAction

section EssSurjAux

open Limits

variable {Y : Scheme.{u}}

section EssSurj

variable [ConnectedSpace Y] {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [∀ P, MulAction G ((Scheme.FiniteEtale.fiber s).obj P)]
  [PreGaloisCategory.IsFundamentalGroup (Scheme.FiniteEtale.fiber s) G]

open scoped FintypeCatDiscrete

section Construction

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

end Construction

end EssSurj

end EssSurjAux

section GaloisRepEquivalence

variable {Y : Scheme.{u}} [ConnectedSpace Y] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ Y) {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] (G : ProfiniteGrp.{u})
  [∀ P, MulAction G ((Scheme.FiniteEtale.fiber s).obj P)]
  [PreGaloisCategory.IsFundamentalGroup (Scheme.FiniteEtale.fiber s) G]

end GaloisRepEquivalence

variable {K : Type u} [Field K] [Finite K] {C U : Scheme.{u}} {p : C ⟶ Spec (.of K)}
  [IsCurve p] {pU : U ⟶ Spec (.of K)} [IsCurve pU]

namespace WeilGroup

/-- Blueprint `prop-wf-weil-sheaf-representation-equivalence`: The lisse sheaf–representation
equivalence.

The property of an object of `Rep ℚ̄_ℓ W(C₀)` of being a *lisse Weil representation*: the
underlying `ℚ̄_ℓ`-vector space is finite dimensional and the geometric subgroup `π₁(C)`
acts continuously (`AlgebraicGeometry.WeilGroup.IsLisse`). Under the equivalence of
`prop-wf-weil-sheaf-representation-equivalence` these are exactly the objects corresponding to lisse
Weil sheaves on `C₀`. -/
def isLisseRep (W : WeilGroup p) (l : ℕ) [Fact l.Prime] :
    ObjectProperty (Rep.{u} (PadicAlgCl l) W.carrier) :=
  fun X ↦ FiniteDimensional (PadicAlgCl l) X.V ∧ W.IsLisse l X.ρ

variable (W : WeilGroup p) (l : ℕ) [Fact l.Prime]

/-- Blueprint `prop-wf-weil-sheaf-representation-equivalence`: The lisse sheaf–representation
equivalence.

A subrepresentation of a lisse Weil representation is again lisse: it is finite dimensional,
and every coefficient `g ↦ φ (ρ g v)` of it is a coefficient of the ambient representation,
for a linear form extending `φ`. -/
instance isLisseRep.isClosedUnderSubobjects :
    ObjectProperty.IsClosedUnderSubobjects (W.isLisseRep l) where
  prop_of_mono {X Y} f _ hY := by
    obtain ⟨_, hρ⟩ := hY
    have hf : Function.Injective f.hom := (Rep.mono_iff_injective f).1 inferInstance
    have : FiniteDimensional (PadicAlgCl l) X.V :=
      Module.Finite.of_injective f.hom.toLinearMap hf
    refine ⟨this, IsLisse.of_continuous_apply fun φ v ↦ ?_⟩
    obtain ⟨ψ, hψ⟩ :=
      f.hom.toLinearMap.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hf)
    have hψ' (x : X.V) : ψ (f.hom x) = x := LinearMap.congr_fun hψ x
    simpa [← Rep.hom_comm_apply, hψ'] using hρ.continuous_apply (φ ∘ₗ ψ) (f.hom v)

/-- Blueprint `prop-wf-weil-sheaf-representation-equivalence`: The lisse sheaf–representation
equivalence.

A quotient of a lisse Weil representation is again lisse: it is finite dimensional, and every
coefficient `g ↦ φ (ρ g (f v))` of it is the coefficient `g ↦ (φ ∘ f) (ρ g v)` of the source. -/
instance isLisseRep.isClosedUnderQuotients :
    ObjectProperty.IsClosedUnderQuotients (W.isLisseRep l) where
  prop_of_epi {X Y} f _ hX := by
    obtain ⟨_, hρ⟩ := hX
    have hf : Function.Surjective f.hom := (Rep.epi_iff_surjective f).1 inferInstance
    have : FiniteDimensional (PadicAlgCl l) Y.V :=
      Module.Finite.of_surjective f.hom.toLinearMap hf
    refine ⟨this, IsLisse.of_continuous_apply fun φ w ↦ ?_⟩
    obtain ⟨v, rfl⟩ := hf w
    simpa [Rep.hom_comm_apply] using hρ.continuous_apply (φ ∘ₗ f.hom.toLinearMap) v

/-- Blueprint `prop-wf-weil-sheaf-representation-equivalence`: The lisse sheaf–representation
equivalence.

Lisse Weil representations are closed under kernels, so a subobject of a lisse Weil
representation is again lisse. -/
instance isLisseRep.isClosedUnderKernels :
    ObjectProperty.IsClosedUnderKernels (W.isLisseRep l) :=
  inferInstance

/-- Blueprint `prop-wf-weil-sheaf-representation-equivalence`: The lisse sheaf–representation
equivalence.

Lisse Weil representations are closed under cokernels, so a quotient of a lisse Weil
representation is again lisse. -/
instance isLisseRep.isClosedUnderCokernels :
    ObjectProperty.IsClosedUnderCokernels (W.isLisseRep l) :=
  inferInstance

variable {W l}

section Sections

variable {l : ℕ} [Fact l.Prime] {W : WeilGroup p} {V : Type u} [AddCommGroup V]
  [Module (PadicAlgCl l) V] (ρ : Representation (PadicAlgCl l) W.carrier V) {j : U ⟶ C}
  [IsOpenImmersion j] [Nonempty U] {WU : WeilGroup pU} (R : Restriction j WU W)

end Sections

end WeilGroup

end AlgebraicGeometry
