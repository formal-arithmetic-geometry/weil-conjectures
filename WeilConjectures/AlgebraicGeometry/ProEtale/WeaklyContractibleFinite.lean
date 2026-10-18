/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.RingTheory.ProEtale.WContractibleFinite
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Exactness of finite pushforward on pro-étale sheaves

Let `g : X ⟶ Y` be a finite morphism of finite presentation. Base change along `g` sends objects
of the small pro-étale site of `Y` whose underlying scheme is the spectrum of a w-contractible
ring to weakly contractible objects of the small pro-étale site of `X`
(`IsWContractibleRing.of_finite`). Since the former cover the site, the pushforward `g_*` of
pro-étale sheaves of modules preserves epimorphisms, hence is exact.

## Main results

- `AlgebraicGeometry.Scheme.ProEt.exists_isWContractibleRing_cover`: every object of the small
  pro-étale site is covered by spectra of w-contractible rings.
- `AlgebraicGeometry.Scheme.ProEt.isWeaklyContractible_pullback_of_isFinite`: the base change of
  the spectrum of a w-contractible ring along a finite morphism of finite presentation is affine
  and weakly contractible.
- `AlgebraicGeometry.ProEtale.preservesFiniteColimits_lowerStar_of_isFinite`: for a finite
  morphism `g` of finite presentation, `g_*` is exact on pro-étale sheaves of modules.
-/

@[expose] public section

universe w u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace Scheme.ProEt

variable {T : Scheme.{u}}

/-- **Stacks 0990.** Every object `V` of the small pro-étale site is covered by objects `W i`
whose underlying schemes are spectra of w-contractible rings: cover `V` by affine opens `Spec R`
and each `Spec R` by `Spec S` for a faithfully flat, ind-étale and w-contractible `R`-algebra
`S`. -/
@[stacks 0990]
theorem exists_isWContractibleRing_cover (V : T.ProEt) :
    ∃ (ι : Type u) (W : ι → T.ProEt) (f : ∀ i, W i ⟶ V),
      (∀ i, ∃ R : CommRingCat.{u}, IsWContractibleRing R ∧ Nonempty ((W i).left ≅ Spec R)) ∧
      Sieve.ofArrows W f ∈ topology T V := by
  have 𝒜 : V.left.AffineOpenCover := V.left.affineOpenCover
  choose S iS iA hind hff hw using fun x : 𝒜.I₀ ↦ exists_isWContractibleRing (𝒜.X x)
  let φ (x : 𝒜.I₀) : 𝒜.X x ⟶ CommRingCat.of (S x) := CommRingCat.ofHom (algebraMap _ _)
  have (x : 𝒜.I₀) : WeaklyEtale (Spec.map (φ x)) := by
    rw [WeaklyEtale.Spec_iff]
    exact RingHom.IndEtale.weaklyEtale ((RingHom.IndEtale.algebraMap_iff _ _).2 (hind x))
  have (x : 𝒜.I₀) : Surjective (Spec.map (φ x)) :=
    ((flat_and_surjective_SpecMap_iff (φ x)).2
      (RingHom.faithfullyFlat_algebraMap_iff.2 (hff x))).2
  let U (x : 𝒜.I₀) := ofOpenImmersion V (𝒜.f x)
  let W (x : 𝒜.I₀) : T.ProEt := ProEt.mk (Spec.map (φ x) ≫ (U x).hom)
  let w (x : 𝒜.I₀) : W x ⟶ U x := MorphismProperty.Over.homMk (Spec.map (φ x)) rfl
  refine ⟨𝒜.I₀, W, fun x ↦ w x ≫ ofOpenImmersionHom V (𝒜.f x),
    fun x ↦ ⟨CommRingCat.of (S x), hw x, ⟨Iso.refl _⟩⟩, ?_⟩
  have hU : Sieve.ofArrows U (fun x ↦ ofOpenImmersionHom V (𝒜.f x)) ∈ topology T V :=
    mem_topology_of_openImmersion _ 𝒜.f (fun y ↦ ⟨_, 𝒜.covers y⟩)
      (fun x ↦ Sieve.ofArrows_mk _ _ x)
  refine (topology T).transitive hU _ fun Y g hg ↦ ?_
  obtain ⟨_, c, _, ⟨x⟩, rfl⟩ := hg
  rw [Sieve.pullback_comp]
  refine (topology T).pullback_stable c ((topology T).superset_covering ?_
    (Precoverage.generate_mem_toGrothendieck (R := .singleton (w x)) ?_))
  · rintro _ _ ⟨_, d, _, ⟨⟩, rfl⟩
    rw [Sieve.pullback_apply, Category.assoc]
    exact (Sieve.ofArrows _ _).downward_closed (Sieve.ofArrows_mk _ _ x) d
  · rw [mem_precoverage_iff, Presieve.map_singleton]
    exact Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale) (f := Spec.map (φ x))
      inferInstance

/-- Let `g : X ⟶ Y` be finite and of finite presentation, and `W` an object of the small
pro-étale site of `Y` whose underlying scheme is the spectrum of a w-contractible ring `R`. The
base change of `W` along `g` is affine, the spectrum of a finite and finitely presented
`R`-algebra, which is w-contractible by `IsWContractibleRing.of_finite`; hence it is affine and
weakly contractible. -/
theorem isWeaklyContractible_pullback_of_isFinite {X Y : Scheme.{u}} (g : X ⟶ Y) [IsFinite g]
    [LocallyOfFinitePresentation g] (W : Y.ProEt) {R : CommRingCat.{u}} [IsWContractibleRing R]
    (e : W.left ≅ Spec R) :
    IsAffine ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj W).left ∧
      (topology X).IsWeaklyContractible.{w}
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj W) := by
  set P := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj W
  let h : P.left ⟶ Spec R := pullback.fst W.hom g ≫ e.hom
  have : IsFinite h := by dsimp [h]; infer_instance
  have : LocallyOfFinitePresentation h := by dsimp [h]; infer_instance
  have hP : IsAffine P.left := isAffine_of_isAffineHom h
  obtain ⟨φ, hφ⟩ : ∃ φ : R ⟶ Γ(P.left, ⊤), Spec.map φ = P.left.isoSpec.inv ≫ h :=
    ⟨Spec.preimage _, Spec.map_preimage _⟩
  have hfin : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]
    infer_instance
  have hfp : φ.hom.FinitePresentation := by
    rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation), hφ]
    infer_instance
  algebraize [φ.hom]
  have : IsWContractibleRing Γ(P.left, ⊤) := IsWContractibleRing.of_finite (A := R)
  exact ⟨hP, isWeaklyContractible_of_iso (R := Γ(P.left, ⊤)) P.left.isoSpec⟩

end Scheme.ProEt

namespace ProEtale

variable {X Y : Scheme.{u}} (g : X ⟶ Y) [IsFinite g] [LocallyOfFinitePresentation g]
  {Λ : Type (u + 1)} [Ring Λ]

/-- For a finite morphism `g` of finite presentation, the pushforward `g_*` of pro-étale sheaves
of modules preserves epimorphisms. The sections of `g_* φ` over an object `W` whose underlying
scheme is the spectrum of a w-contractible ring are those of `φ` over the base change of `W`,
which is weakly contractible (`Scheme.ProEt.isWeaklyContractible_pullback_of_isFinite`), so they
are surjective; and such objects cover the site
(`Scheme.ProEt.exists_isWContractibleRing_cover`). -/
theorem epi_lowerStar_map_of_isFinite
    {F G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)} (φ : F ⟶ G) [Epi φ] :
    Epi ((g)_*[ModuleCat.{u + 1} Λ].map φ) := by
  have hloc : Sheaf.IsLocallySurjective φ := (Sheaf.isLocallySurjective_iff_epi' _ φ).2 ‹_›
  have hsurj (W : Y.ProEt) (R : CommRingCat.{u}) (hR : IsWContractibleRing R)
      (e : W.left ≅ Spec R) :
      Function.Surjective (((g)_*[ModuleCat.{u + 1} Λ].map φ).hom.app (op W)) := by
    rw [ProEtale.lowerStar_map_hom_app]
    exact (Scheme.ProEt.isWeaklyContractible_pullback_of_isFinite.{u + 1} g W e).2
      ((sheafCompose _ (forget _)).map φ)
      ((Presheaf.isLocallySurjective_iff_whisker_forget _ _).1 hloc)
  rw [← Sheaf.isLocallySurjective_iff_epi']
  refine ⟨fun {V} s ↦ ?_⟩
  obtain ⟨ι, W, f, hW, hcov⟩ := Scheme.ProEt.exists_isWContractibleRing_cover V
  refine (Scheme.ProEt.topology Y).superset_covering ?_ hcov
  rintro _ _ ⟨_, a, _, ⟨i⟩, rfl⟩
  obtain ⟨R, hR, ⟨e⟩⟩ := hW i
  obtain ⟨t, ht⟩ := hsurj (W i) R hR e (((g)_*[ModuleCat.{u + 1} Λ].obj G).obj.map (f i).op s)
  exact (Presheaf.imageSieve _ s).downward_closed ⟨t, ht⟩ a

/-- **Finite pushforward is exact on pro-étale sheaves of modules.** For a finite morphism `g`
of finite presentation, `g_*` is left exact as a right adjoint and preserves epimorphisms by
`AlgebraicGeometry.ProEtale.epi_lowerStar_map_of_isFinite`. -/
theorem preservesFiniteColimits_lowerStar_of_isFinite :
    PreservesFiniteColimits ((g)_*[ModuleCat.{u + 1} Λ]) := by
  have : ((g)_*[ModuleCat.{u + 1} Λ]).PreservesEpimorphisms :=
    ⟨fun φ _ ↦ epi_lowerStar_map_of_isFinite g φ⟩
  have := Functor.preservesHomology_of_preservesEpis_and_kernels ((g)_*[ModuleCat.{u + 1} Λ])
  exact Functor.preservesFiniteColimits_of_preservesHomology _

end ProEtale

end AlgebraicGeometry
