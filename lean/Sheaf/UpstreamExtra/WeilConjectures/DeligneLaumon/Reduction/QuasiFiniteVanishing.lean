module

public import WeilConjectures.WeilSheaf.FiniteLowerStar
public import WeilConjectures.WeilSheaf.LowerShriek
public import Sheaf.RingTheory.FiniteWContractible

/-! Declarations of ours that lived in the upstream file
`WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing` (moved out by the scheduled
sync, tools/upstream_verbatim.py, 2026-10-20: upstream files are verbatim in live). -/

/-!
# Vanishing of direct images of Weil sheaves

The derived direct image `Rf₀*G` and the direct image with compact support `Rf₀!G` of a Weil
sheaf are concentrated in degrees `≥ 0`. For a finite morphism `p` the higher direct images
`Rʳp₀*G` vanish for `r > 0`, and so, by Zariski's main theorem, do the higher direct images with
compact support `Rʳf₀!G` along a separated quasi-finite morphism `f`. These statements do not
involve weights; they are used both by the weight reductions of
`WeilConjectures.DeligneLaumon.Reduction.FormalSteps` and by the computation of the local
Frobenius of quasi-finite direct images in
`WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.isZero_homologySheaf_derivedLowerStar_of_neg` and
  `AlgebraicGeometry.WeilSheaf.isZero_homologySheaf_derivedLowerShriek_of_neg`: vanishing in
  negative degrees.
- `AlgebraicGeometry.WeilSheaf.isZero_higherLowerStar_of_isFinite`: blueprint
  `lemma-weil-pbc-finite-direct-image-exact`.
- `AlgebraicGeometry.isZero_higherLowerShriek_of_quasiFinite`: blueprint
  `sk-l-dl-general-quasifinite`, `lem-zl-quasi-finite`, part 1.
-/

@[expose] public section

-- The synchronization companion retains only private helpers.
set_option linter.privateModule false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

private def wContractibleAffine {Y : Scheme.{u}} (W : Y.ProEt) : Prop :=
  ∃ (R : CommRingCat.{u}) (_ : IsWContractibleRing R), Nonempty (W.left ≅ Spec R)

private theorem exists_wContractibleAffine_cover {B : Scheme.{u}} (V : B.ProEt) :
    ∃ (ι : Type u) (W : ι → B.ProEt) (f : ∀ i, W i ⟶ V),
      (∀ i, wContractibleAffine (W i)) ∧
      Sieve.ofArrows W f ∈ Scheme.ProEt.topology B V := by
  have 𝒜 : V.left.AffineOpenCover := V.left.affineOpenCover
  choose S iS iA hind hff hw using fun x : 𝒜.I₀ ↦ exists_isWContractibleRing (𝒜.X x)
  let φ (x : 𝒜.I₀) : 𝒜.X x ⟶ CommRingCat.of (S x) := CommRingCat.ofHom (algebraMap _ _)
  have (x : 𝒜.I₀) : WeaklyEtale (Spec.map (φ x)) := by
    rw [WeaklyEtale.Spec_iff]
    exact RingHom.IndEtale.weaklyEtale ((RingHom.IndEtale.algebraMap_iff _ _).2 (hind x))
  have (x : 𝒜.I₀) : Surjective (Spec.map (φ x)) :=
    ((flat_and_surjective_SpecMap_iff (φ x)).2
      (RingHom.faithfullyFlat_algebraMap_iff.2 (hff x))).2
  let U (x : 𝒜.I₀) := Scheme.ProEt.ofOpenImmersion V (𝒜.f x)
  let W (x : 𝒜.I₀) : B.ProEt := Scheme.ProEt.mk (Spec.map (φ x) ≫ (U x).hom)
  let w (x : 𝒜.I₀) : W x ⟶ U x := MorphismProperty.Over.homMk (Spec.map (φ x)) rfl
  refine ⟨𝒜.I₀, W, fun x ↦ w x ≫ Scheme.ProEt.ofOpenImmersionHom V (𝒜.f x),
    fun x ↦ ⟨CommRingCat.of (S x), hw x, ⟨Iso.refl _⟩⟩, ?_⟩
  · have hU : Sieve.ofArrows U (fun x ↦ Scheme.ProEt.ofOpenImmersionHom V (𝒜.f x)) ∈
        Scheme.ProEt.topology B V :=
      Scheme.ProEt.mem_topology_of_openImmersion _ 𝒜.f (fun y ↦ ⟨_, 𝒜.covers y⟩)
        (fun x ↦ Sieve.ofArrows_mk _ _ x)
    refine (Scheme.ProEt.topology B).transitive hU _ fun V₁ g hg ↦ ?_
    obtain ⟨_, c, _, ⟨x⟩, rfl⟩ := hg
    rw [Sieve.pullback_comp]
    refine (Scheme.ProEt.topology B).pullback_stable c
      ((Scheme.ProEt.topology B).superset_covering ?_
      (Precoverage.generate_mem_toGrothendieck (R := .singleton (w x)) ?_))
    · rintro _ _ ⟨_, d, _, ⟨⟩, rfl⟩
      rw [Sieve.pullback_apply, Category.assoc]
      exact (Sieve.ofArrows _ _).downward_closed (Sieve.ofArrows_mk _ _ x) d
    · rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_singleton]
      exact Scheme.Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale) (f := Spec.map (φ x))
        inferInstance

private theorem wContractibleAffine_isWeaklyContractible {Y : Scheme.{u}} (W : Y.ProEt)
    (hW : wContractibleAffine W) :
    (Scheme.ProEt.topology Y).IsWeaklyContractible.{u + 1} W := by
  obtain ⟨R, hR, ⟨e⟩⟩ := hW
  exact Scheme.ProEt.isWeaklyContractible_of_iso e

private theorem wContractibleAffine_pullback {X Y : Scheme.{u}} (p : X ⟶ Y)
    [IsFinite p] [LocallyOfFinitePresentation p] (W : Y.ProEt)
    (hW : wContractibleAffine W) :
    wContractibleAffine ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ p).obj W) := by
  obtain ⟨R, hR, ⟨e⟩⟩ := hW
  let Z := ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ p).obj W).left
  let q : Z ⟶ Spec R := pullback.fst W.hom p ≫ e.hom
  have : IsFinite q := inferInstanceAs (IsFinite (pullback.fst W.hom p ≫ e.hom))
  have : LocallyOfFinitePresentation q :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.fst W.hom p ≫ e.hom))
  have : IsAffine Z := isAffine_of_isAffineHom q
  let φ : R ⟶ Γ(Z, ⊤) := Spec.preimage (Z.isoSpec.inv ≫ q)
  have hφ : Spec.map φ = Z.isoSpec.inv ≫ q := Spec.map_preimage _
  have hfin : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have hfp : LocallyOfFinitePresentation (Spec.map φ) := by rw [hφ]; infer_instance
  let : Algebra R Γ(Z, ⊤) := φ.hom.toAlgebra
  have : Module.Finite R Γ(Z, ⊤) :=
    RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff φ).mp hfin)
  have : Algebra.FinitePresentation R Γ(Z, ⊤) :=
    RingHom.finitePresentation_algebraMap.mp
      ((HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mp hfp)
  exact ⟨Γ(Z, ⊤), isWContractibleRing_of_finite_finitePresentation R Γ(Z, ⊤),
    ⟨Z.isoSpec⟩⟩

private theorem preservesFiniteColimits_proEtaleLowerStar_of_isFinite
    {X Y : Scheme.{u}} (p : X ⟶ Y) [IsFinite p] [LocallyOfFinitePresentation p]
    (R : Type (u + 1)) [CommRing R] :
    PreservesFiniteColimits (ProEtale.lowerStar (ModuleCat.{u + 1} R) p) := by
  have h : (ProEtale.lowerStar (ModuleCat.{u + 1} R) p).PreservesHomology :=
    Functor.preservesHomology_of_map_exact _ (fun S hS ↦ by
      apply (GrothendieckTopology.exact_iff_of_forall_exists
        wContractibleAffine exists_wContractibleAffine_cover
        wContractibleAffine_isWeaklyContractible _).mpr
      intro W hW
      have hB := wContractibleAffine_pullback p W hW
      exact (GrothendieckTopology.exact_iff_of_forall_exists
        wContractibleAffine exists_wContractibleAffine_cover
        wContractibleAffine_isWeaklyContractible S).mp hS _ hB)
  exact Functor.preservesFiniteColimits_of_preservesHomology _

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section UpperStar

variable {W X : Scheme.{u}} [W.Over (Spec (CommRingCat.of k₀))]
  [X.Over (Spec (CommRingCat.of k₀))] (h : W ⟶ X) [h.IsOver (Spec (CommRingCat.of k₀))]

end UpperStar

section LowerShriek

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] {f : X ⟶ Y} [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]

end LowerShriek

section QuasiFinite

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyQuasiFinite f] [LocallyOfFiniteType f] [QuasiCompact f]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]

end QuasiFinite

end AlgebraicGeometry
