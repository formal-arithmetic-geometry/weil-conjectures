module
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.FinitePresentation
import Sheaf.AlgebraicGeometry.FilteredColimitLocalizationAtPrime
@[expose] public section
universe u p
open CategoryTheory CategoryTheory.Limits
namespace RingHom
/-- Core ring descent assertion, retaining the transition and structure maps but omitting
explicit representatives of the cocone maps. This is the finite-coefficient construction
of Stacks Project, Algebra, Tags 00QV and 00QX; its proof descends the presentation and
prime to a common stage and verifies the colimit and locality properties.
(blueprint: lem-weil-pbc-limit-module-ring-data-core)

Proof: Descend the finite coefficients of the presentation and localization prime to a
common stage, then verify the cocone, locality, and compatibility assertions elementwise. -/
theorem exists_limit_module_ring_data_core
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    [∀ i : I, IsLocalRing (F.obj i)] [IsLocalRing c.pt]
    (hF : ∀ (i j : I) (h : i ≤ j), IsLocalHom (F.map (homOfLE h)).hom)
    (hcLocal : ∀ i : I, IsLocalHom (c.ι.app i).hom)
    (T : CommRingCat.{u}) [IsLocalRing T] (τ : c.pt →+* T) [IsLocalHom τ]
    (P : Type p) [CommRing P] [Algebra c.pt P] [Algebra.FinitePresentation c.pt P]
    (W : Submonoid P) (f : P →+* T)
    (hf : f.comp (algebraMap c.pt P) = τ)
    (hT : letI := f.toAlgebra; IsLocalization W T) :
    ∃ i₀ : I,
      ∃ (B : {i : I // i₀ ≤ i} ⥤ CommRingCat.{u})
        (β : B ⟶ (Functor.const _).obj T),
        Nonempty (IsColimit (Cocone.mk T β)) ∧
        ∃ (τ₀ : ∀ i : {i : I // i₀ ≤ i}, F.obj i.1 →+* B.obj i),
          (∀ i, IsLocalHom (τ₀ i)) ∧ (∀ i, (τ₀ i).EssFiniteType) ∧
          (∀ i, (β.app i).hom.comp (τ₀ i) = τ.comp (c.ι.app i.1).hom) ∧
          (∀ (i j : {i : I // i₀ ≤ i}) (h : i ≤ j),
            (B.map (homOfLE h)).hom.comp (τ₀ i) =
              (τ₀ j).comp (F.map (homOfLE h)).hom) ∧
          (∀ i, IsLocalRing (B.obj i)) ∧
          (∀ i, IsLocalHom ((β.app i).hom)) ∧
          (∀ (i j : {i : I // i₀ ≤ i}) (h : i ≤ j),
            IsLocalHom (B.map (homOfLE h)).hom) := by
  sorry
end RingHom
