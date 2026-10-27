module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
# Canonical affine charts give a quasi-compact open immersion

Source: Stacks Project, Morphisms of Schemes, Tag 01SM,
`lemma-characterize-quasi-affine`, proof (2) implies (4), final two sentences
(blueprint: lem-trf-canonical-affine-charts-qc-open-immersion).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- If an `S`-morphism into an affine `S`-scheme identifies on every affine base open
with the canonical affinization map of a quasi-affine scheme, it is a quasi-compact
open immersion. No compactness or separation assumption is made on `S`.

Source: Stacks Project, Morphisms of Schemes, Tag 01SM,
`lemma-characterize-quasi-affine`, proof (2) implies (4), final two sentences
(blueprint: lem-trf-canonical-affine-charts-qc-open-immersion).

Proof: Choose an affine open cover `Uᵢ` of `S`. Its preimages `Wᵢ` in `X` and `Vᵢ`
in `Y` cover their respective schemes. Affineness of `π` makes `Vᵢ` affine, and
`c ≫ π = f` identifies `c⁻¹(Vᵢ)` with `Wᵢ`. Each `Wᵢ` is quasi-affine, hence compact,
and its canonical map to the spectrum of global sections is an open immersion
(lem-trf-quasi-affine-canonical-affine-embedding). The chart isomorphism identifies
this map with the restriction of `c`, which is therefore an open immersion.
If `c(x) = c(x')`, their common base point lies in some `Uᵢ`, and injectivity on
`Wᵢ` gives `x = x'`. Each point has an open neighbourhood `Wᵢ` whose map to `Y`
is an open immersion. The injective local-source criterion
(lem-weil-pbc-open-immersion-injective-local-source) now makes `c` an open immersion.
Each affine `Vᵢ` is quasi-separated (lem-weil-pbc-affine-scheme-qcqs), so compactness
of `Wᵢ` makes its map to `Vᵢ` quasi-compact
(lem-weil-pbc-qcqs-morphism-permanence, clause (1)). Quasi-compactness is local on
the target (lem-pc-quasi-compact-local-on-target), giving quasi-compactness of `c`
on the cover `Vᵢ`, without taking a finite subcover of the base. -/
theorem isOpenImmersion_and_quasiCompact_of_canonical_affine_charts
    {X Y S : Scheme.{u}} (f : X ⟶ S) (π : Y ⟶ S) (c : X ⟶ Y)
    (hc : c ≫ π = f) [IsAffineHom π]
    (hqa : ∀ U : S.Opens, IsAffineOpen U → (f ⁻¹ᵁ U).toScheme.IsQuasiAffine)
    (hcharts : ∀ U : S.Opens, IsAffineOpen U →
      ∃ h : (π ⁻¹ᵁ U).toScheme ≅ Spec Γ((f ⁻¹ᵁ U).toScheme, ⊤),
        c.resLE (π ⁻¹ᵁ U) (f ⁻¹ᵁ U)
            ((congrArg (fun g : X ⟶ S ↦ g ⁻¹ᵁ U) hc).symm.le) ≫ h.hom =
          (f ⁻¹ᵁ U).toScheme.toSpecΓ) :
    IsOpenImmersion c ∧ QuasiCompact c := by
  subst f
  simp only [Scheme.Hom.comp_preimage] at hqa hcharts
  simp only [Scheme.Hom.resLE_eq_morphismRestrict] at hcharts
  have hlocal (U : S.Opens) (hU : IsAffineOpen U) :
      IsOpenImmersion (c ∣_ π ⁻¹ᵁ U) ∧ QuasiCompact (c ∣_ π ⁻¹ᵁ U) := by
    have := hqa U hU
    obtain ⟨h, hh⟩ := hcharts U hU
    have : IsOpenImmersion (c ∣_ π ⁻¹ᵁ U) := by
      have : IsOpenImmersion ((c ∣_ π ⁻¹ᵁ U) ≫ h.hom) := by
        rw [hh]
        infer_instance
      exact IsOpenImmersion.of_comp _ h.hom
    have : IsAffine (π ⁻¹ᵁ U).toScheme := hU.preimage π
    exact ⟨inferInstance, inferInstance⟩
  have hcover (y : Y) : ∃ U : Y.Opens, y ∈ U ∧
      IsOpenImmersion (c ∣_ U) ∧ QuasiCompact (c ∣_ U) := by
    obtain ⟨U, hU, hy, _⟩ := exists_isAffineOpen_mem_and_subset
      (show π y ∈ (⊤ : S.Opens) from trivial)
    exact ⟨π ⁻¹ᵁ U, hy, hlocal U hU⟩
  constructor
  · apply IsOpenImmersion.of_forall_source_exists c
    · intro x x' hxx'
      obtain ⟨V, hxV, ho, _⟩ := hcover (c x)
      have := ho
      have hx'V : c x' ∈ V := hxx' ▸ hxV
      have he : (c ∣_ V) ⟨x, hxV⟩ = (c ∣_ V) ⟨x', hx'V⟩ := by
        apply Subtype.ext
        simpa only [morphismRestrict_base_coe] using hxx'
      exact congrArg Subtype.val ((c ∣_ V).isEmbedding.injective he)
    · intro x
      obtain ⟨V, hxV, ho, _⟩ := hcover (c x)
      have := ho
      refine ⟨(c ⁻¹ᵁ V).toScheme, (c ⁻¹ᵁ V).ι, inferInstance, ?_, ?_⟩
      · rw [Scheme.Opens.opensRange_ι]
        exact hxV
      · rw [← morphismRestrict_ι]
        infer_instance
  · exact IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict fun y ↦ by
      obtain ⟨U, hy, _, hq⟩ := hcover y
      exact ⟨U, hy, hq⟩

end AlgebraicGeometry
