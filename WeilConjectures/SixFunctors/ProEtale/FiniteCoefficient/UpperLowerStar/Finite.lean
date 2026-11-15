/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractibleProducts
public import WeilConjectures.RingTheory.ProEtale.FiniteWContractible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtale.CohomologyFilteredColimit
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine

/-!
# The pushforward along a finite morphism on pro-étale sheaves of modules is exact

Let `f : X ⟶ Y` be a finite morphism of finite presentation. For pro-étale sheaves of modules
the pushforward `f_*` is exact (Bhatt–Scholze, *The pro-étale topology for schemes*, §5.4,
compare `AlgebraicGeometry.ProEtale.preservesFiniteColimits_lowerStar_of_isCompl` for closed
immersions).

Proof: the objects `V` of the pro-étale site of `Y` whose underlying scheme is the spectrum of
a w-contractible ring cover every object. For such `V`, the base change `V ×_Y X` is the
spectrum of a module-finite, finitely presented algebra over a w-contractible ring, hence
itself the spectrum of a w-contractible ring (`IsWContractibleRing.of_finite`), hence weakly
contractible in the pro-étale site of `X`. So an epimorphism `G ⟶ H` of sheaves on `X` is
surjective on sections over `V ×_Y X`, that is, `f_* G ⟶ f_* H` is surjective on sections
over `V`; this detects epimorphisms
(`CategoryTheory.GrothendieckTopology.epi_iff_of_forall_exists`).

## Main results

- `AlgebraicGeometry.Scheme.ProEt.exists_isWContractibleRing_cover`: every object of the small
  pro-étale site is covered by spectra of w-contractible rings.
- `AlgebraicGeometry.ProEtale.preservesFiniteColimits_lowerStar_of_isFinite`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

/-- A scheme admitting a finite morphism of finite presentation to the spectrum of a
w-contractible ring is affine, with w-contractible ring of global sections. -/
lemma isAffine_and_isWContractibleRing_of_isFinite {P : Scheme.{u}} {R : CommRingCat.{u}}
    [IsWContractibleRing R] (g : P ⟶ Spec R) [IsFinite g] [LocallyOfFinitePresentation g] :
    IsAffine P ∧ IsWContractibleRing Γ(P, ⊤) := by
  have : IsAffine P := isAffine_of_isAffineHom g
  refine ⟨this, ?_⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : R ⟶ Γ(P, ⊤), Spec.map φ = P.isoSpec.inv ≫ g :=
    ⟨Spec.preimage _, Spec.map_preimage _⟩
  have : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have : LocallyOfFinitePresentation (Spec.map φ) := by rw [hφ]; infer_instance
  have hfin : φ.hom.Finite := (IsFinite.SpecMap_iff φ).1 inferInstance
  have hfp : φ.hom.FinitePresentation :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).1 inferInstance
  algebraize [φ.hom]
  exact IsWContractibleRing.of_finite (A := R)

namespace Scheme.ProEt

variable {T : Scheme.{u}}

/-- Two-level transitivity of the pro-étale topology: if the family `u i : U i ⟶ V` generates a
covering sieve of `V` and, for each `i`, the family `w i j : W i j ⟶ U i` generates a covering
sieve of `U i`, then the composites `W i j ⟶ U i ⟶ V` generate a covering sieve of `V`. -/
private theorem ofArrows_comp_mem {V : T.ProEt} {ι : Type u} {U : ι → T.ProEt}
    {u : ∀ i, U i ⟶ V} (hU : Sieve.ofArrows U u ∈ topology T V)
    {κ : ι → Type u} {W : ∀ i, κ i → T.ProEt} {w : ∀ i j, W i j ⟶ U i}
    (hW : ∀ i, Sieve.ofArrows (W i) (w i) ∈ topology T (U i)) :
    Sieve.ofArrows (fun p : Σ i, κ i ↦ W p.1 p.2) (fun p ↦ w p.1 p.2 ≫ u p.1) ∈
      topology T V := by
  refine (topology T).transitive hU _ fun Y g hg ↦ ?_
  obtain ⟨_, c, _, ⟨i⟩, rfl⟩ := hg
  rw [Sieve.pullback_comp]
  refine (topology T).pullback_stable c ((topology T).superset_covering ?_ (hW i))
  rintro Z d ⟨_, e, _, ⟨j⟩, rfl⟩
  rw [Sieve.pullback_apply, Category.assoc]
  exact (Sieve.ofArrows _ _).downward_closed (Sieve.ofArrows_mk _ _ (⟨i, j⟩ : Σ i, κ i)) e

/-- Every object of the small pro-étale site is covered by objects whose underlying scheme is
the spectrum of a w-contractible ring: the affine pro-étale objects form a basis of the site
(`AlgebraicGeometry.Scheme.AffineProEt.isCoverDense_toProEt`), so every object is covered by
objects with affine underlying scheme, and every ring admits an ind-étale faithfully flat
w-contractible cover (`exists_isWContractibleRing`). -/
theorem exists_isWContractibleRing_cover (V : T.ProEt) :
    ∃ (ι : Type u) (W : ι → T.ProEt) (f : ∀ i, W i ⟶ V),
      (∀ i, ∃ R : CommRingCat.{u}, IsWContractibleRing R ∧ Nonempty ((W i).left ≅ Spec R)) ∧
      Sieve.ofArrows W f ∈ topology T V := by
  -- a Zariski cover of `V` by affine opens
  have 𝒜 : V.left.AffineOpenCover := V.left.affineOpenCover
  let U (x : 𝒜.I₀) := ofOpenImmersion V (𝒜.f x)
  have hU : Sieve.ofArrows U (fun x ↦ ofOpenImmersionHom V (𝒜.f x)) ∈ topology T V :=
    mem_topology_of_openImmersion _ 𝒜.f (fun y ↦ ⟨_, 𝒜.covers y⟩)
      (fun x ↦ Sieve.ofArrows_mk _ _ x)
  -- each affine open is covered by finitely many objects with affine underlying scheme lying
  -- in the covering sieve generated by the affine pro-étale objects
  have hY (x : 𝒜.I₀) : ∃ (m : ℕ) (Y : Fin m → T.ProEt) (g : ∀ a, Y a ⟶ U x),
      (∀ a, Sieve.coverByImage (AffineProEt.toProEt T) (U x) (g a)) ∧
      (∀ a, IsAffine (Y a).left) ∧ Sieve.ofArrows Y g ∈ topology T (U x) :=
    have : CompactSpace (U x).left := inferInstanceAs (CompactSpace (Spec (𝒜.X x)))
    have : QuasiSeparatedSpace (U x).left :=
      inferInstanceAs (QuasiSeparatedSpace (Spec (𝒜.X x)))
    exists_finite_affine_of_mem_topology
      (Functor.IsCoverDense.is_cover (G := AffineProEt.toProEt T) (K := topology T) (U x))
  choose n Y g _ hYaff hYcov using hY
  have (x : 𝒜.I₀) (a : Fin (n x)) : IsAffine (Y x a).left := hYaff x a
  have (x : 𝒜.I₀) (a : Fin (n x)) : WeaklyEtale (Y x a).hom := (Y x a).prop
  -- w-contractible covers of the affine objects
  choose S iS iA hind hff hw using fun (x : 𝒜.I₀) (a : Fin (n x)) ↦
    exists_isWContractibleRing Γ((Y x a).left, ⊤)
  let φ (x : 𝒜.I₀) (a : Fin (n x)) : Γ((Y x a).left, ⊤) ⟶ CommRingCat.of (S x a) :=
    CommRingCat.ofHom (algebraMap _ _)
  have (x : 𝒜.I₀) (a : Fin (n x)) : WeaklyEtale (Spec.map (φ x a)) := by
    rw [WeaklyEtale.Spec_iff]
    exact RingHom.IndEtale.weaklyEtale ((RingHom.IndEtale.algebraMap_iff _ _).2 (hind x a))
  have (x : 𝒜.I₀) (a : Fin (n x)) : Surjective (Spec.map (φ x a)) :=
    ((flat_and_surjective_SpecMap_iff (φ x a)).2
      (RingHom.faithfullyFlat_algebraMap_iff.2 (hff x a))).2
  have (x : 𝒜.I₀) (a : Fin (n x)) : WeaklyEtale (Y x a).left.isoSpec.inv :=
    MorphismProperty.of_isIso @WeaklyEtale _
  have (x : 𝒜.I₀) (a : Fin (n x)) :
      WeaklyEtale (Spec.map (φ x a) ≫ (Y x a).left.isoSpec.inv) := inferInstance
  have (x : 𝒜.I₀) (a : Fin (n x)) :
      Surjective (Spec.map (φ x a) ≫ (Y x a).left.isoSpec.inv) := inferInstance
  let W (x : 𝒜.I₀) (a : Fin (n x)) : T.ProEt :=
    ProEt.mk ((Spec.map (φ x a) ≫ (Y x a).left.isoSpec.inv) ≫ (Y x a).hom)
  let w (x : 𝒜.I₀) (a : Fin (n x)) : W x a ⟶ Y x a :=
    MorphismProperty.Over.homMk (Spec.map (φ x a) ≫ (Y x a).left.isoSpec.inv) rfl
  -- the w-contractible covers of the `Y x a` cover `U x`
  have hW (x : 𝒜.I₀) : Sieve.ofArrows (fun a : ULift.{u} (Fin (n x)) ↦ W x a.down)
      (fun a ↦ w x a.down ≫ g x a.down) ∈ topology T (U x) := by
    refine (topology T).transitive (hYcov x) _ fun Z e he ↦ ?_
    obtain ⟨_, c, _, ⟨a⟩, rfl⟩ := he
    rw [Sieve.pullback_comp]
    refine (topology T).pullback_stable c ((topology T).superset_covering ?_
      (Precoverage.generate_mem_toGrothendieck (R := .singleton (w x a)) ?_))
    · rintro _ _ ⟨_, d, _, ⟨⟩, rfl⟩
      rw [Sieve.pullback_apply, Category.assoc]
      exact (Sieve.ofArrows _ _).downward_closed
        (Sieve.ofArrows_mk _ _ (⟨a⟩ : ULift.{u} (Fin (n x)))) d
    · rw [mem_precoverage_iff, Presieve.map_singleton]
      exact Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale)
        (f := Spec.map (φ x a) ≫ (Y x a).left.isoSpec.inv) inferInstance
  have hcov := ofArrows_comp_mem hU hW
  exact ⟨Σ x : 𝒜.I₀, ULift.{u} (Fin (n x)), fun p ↦ W p.1 p.2.down,
    fun p ↦ (w p.1 p.2.down ≫ g p.1 p.2.down) ≫ ofOpenImmersionHom V (𝒜.f p.1),
    fun p ↦ ⟨CommRingCat.of (S p.1 p.2.down), hw p.1 p.2.down, ⟨Iso.refl _⟩⟩, hcov⟩

/-- The base change of an object of the small pro-étale site of `Y` whose underlying scheme is
the spectrum of a w-contractible ring along a finite morphism of finite presentation is weakly
contractible. -/
theorem isWeaklyContractible_pullback_of_isFinite {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    [LocallyOfFinitePresentation f] {W : Y.ProEt} {R : CommRingCat.{u}} [IsWContractibleRing R]
    (e : W.left ≅ Spec R) :
    (topology X).IsWeaklyContractible.{u + 1}
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj W) := by
  let g : pullback W.hom f ⟶ Spec R := pullback.fst W.hom f ≫ e.hom
  obtain ⟨_, h⟩ := isAffine_and_isWContractibleRing_of_isFinite g
  exact isWeaklyContractible_of_iso (R := Γ(pullback W.hom f, ⊤))
    (pullback W.hom f).isoSpec

end Scheme.ProEt

namespace ProEtale

variable {R : Type (u + 1)} [Ring R] {X Y : Scheme.{u}}

/-- The pushforward along a finite morphism of finite presentation preserves epimorphisms of
pro-étale sheaves of modules: an epimorphism is surjective on sections over weakly contractible
objects, and the base change of the spectrum of a w-contractible ring along `f` is weakly
contractible (`AlgebraicGeometry.Scheme.ProEt.isWeaklyContractible_pullback_of_isFinite`). -/
lemma epi_lowerStar_map_of_isFinite (f : X ⟶ Y) [IsFinite f] [LocallyOfFinitePresentation f]
    {G H : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)} (φ : G ⟶ H) [Epi φ] :
    Epi ((f)_*[ModuleCat.{u + 1} R].map φ) := by
  have hX := (GrothendieckTopology.epi_iff_of_forall_exists
    (fun W : X.ProEt ↦ (Scheme.ProEt.topology X).IsWeaklyContractible.{u + 1} W)
    (fun V ↦ by
      obtain ⟨ι, W, g, hW, hcov⟩ := Scheme.ProEt.exists_isWeaklyContractible_cover.{u + 1} V
      exact ⟨ι, W, g, fun i ↦ (hW i).2, hcov⟩)
    (fun _ h ↦ h) φ).1 inferInstance
  rw [GrothendieckTopology.epi_iff_of_forall_exists
    (fun W : Y.ProEt ↦ ∃ R : CommRingCat.{u}, IsWContractibleRing R ∧ Nonempty (W.left ≅ Spec R))
    Scheme.ProEt.exists_isWContractibleRing_cover
    (fun W ⟨R, _, ⟨e⟩⟩ ↦ Scheme.ProEt.isWeaklyContractible_of_iso e)]
  rintro W ⟨R, _, ⟨e⟩⟩
  exact hX _ (Scheme.ProEt.isWeaklyContractible_pullback_of_isFinite f e)

variable (R) in
/-- **Finite pushforward is exact** on pro-étale sheaves of modules: for a finite morphism `f`
of finite presentation, `f_*` is left exact as a right adjoint and preserves epimorphisms by
`AlgebraicGeometry.ProEtale.epi_lowerStar_map_of_isFinite`. -/
theorem preservesFiniteColimits_lowerStar_of_isFinite (f : X ⟶ Y) [IsFinite f]
    [LocallyOfFinitePresentation f] :
    PreservesFiniteColimits ((f)_*[ModuleCat.{u + 1} R]) := by
  have : ((f)_*[ModuleCat.{u + 1} R]).PreservesEpimorphisms :=
    ⟨fun φ _ ↦ epi_lowerStar_map_of_isFinite f φ⟩
  have := Functor.preservesHomology_of_preservesEpis_and_kernels ((f)_*[ModuleCat.{u + 1} R])
  exact Functor.preservesFiniteColimits_of_preservesHomology _

end ProEtale

end AlgebraicGeometry
