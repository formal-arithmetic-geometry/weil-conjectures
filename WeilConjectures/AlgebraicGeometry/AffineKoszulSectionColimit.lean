/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedTensorAugmentation
public import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.HomCongr
import WeilConjectures.AlgebraicGeometry.AffinePerfectOpenRepresentCohomology
import WeilConjectures.AlgebraicGeometry.SchemeIsoDerivedLocalizations
import all WeilConjectures.AlgebraicGeometry.SchemeIsoDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.SpectrumStructureRestrictionComparison
import WeilConjectures.AlgebraicGeometry.SchemeIsoDerivedQCoh
import WeilConjectures.AlgebraicGeometry.SchemeIsoPerfectTransport

/-! # The Koszul section colimit on an arbitrary affine scheme

Source: Stacks Project, Tags 08DC, 08DD and 08EH.
(blueprint: lem-sc-affine-koszul-section-colimit).
-/

@[expose] public section

set_option autoImplicit false
universe uX wD
open CategoryTheory CategoryTheory.Limits TopologicalSpace MonoidalCategory
namespace AlgebraicGeometry.Scheme
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem existsFiniteKoszulOpen (A : Type uX) [CommRing A]
    (V : (Spec (.of A)).Opens) (hV : IsCompact (V : Set (Spec (.of A)))) :
    ∃ (r : ℕ) (f : Fin r → A), V = koszulOpen A r f := by
  classical
  obtain ⟨t, ht⟩ := PrimeSpectrum.isCompact_isOpen_iff.mp ⟨hV, V.isOpen⟩
  let e := Fintype.equivFin t
  refine ⟨Fintype.card t, fun i ↦ (e.symm i).val, ?_⟩
  ext x
  change x ∈ (V : Set (Spec (.of A))) ↔ x ∈ koszulOpen A _ _
  rw [← ht]
  simp only [koszulOpen, Opens.mem_iSup]
  change (¬ ∀ a ∈ t, a ∈ (x : PrimeSpectrum A).asIdeal) ↔
    ∃ i, (e.symm i).val ∉ (x : PrimeSpectrum A).asIdeal
  push Not
  constructor
  · rintro ⟨a, ha, hx⟩
    exact ⟨e ⟨a, ha⟩, by simpa using hx⟩
  · rintro ⟨i, hi⟩
    exact ⟨(e.symm i).val, (e.symm i).property, hi⟩

private theorem transportHomColimit
    {C₁ C₂ B₁ B₂ : Type*} [Category.{wD} C₁] [Category.{wD} C₂]
    [Category.{wD} B₁] [Category.{wD} B₂]
    (F : C₁ ≌ C₂) (G : B₁ ≌ B₂) (R₁ : C₁ ⥤ B₁) (R₂ : C₂ ⥤ B₂)
    (β : F.functor ⋙ R₂ ≅ R₁ ⋙ G.functor)
    (T E : C₁) (T' E' : C₂) (q : F.functor.obj T ≅ T')
    (c : F.functor.obj E ≅ E') (P : ℕ → C₁) (a : ∀ n, P n ⟶ T)
    (v : ∀ n, R₁.obj T ⟶ R₁.obj (P n))
    (hav : ∀ n, R₁.map (a n) ≫ v n = 𝟙 _)
    (hva : ∀ n, v n ≫ R₁.map (a n) = 𝟙 _)
    (D : ℕ ⥤ Type wD) (hD : ∀ n, D.obj n = (P n ⟶ E))
    (ι : D ⟶ (Functor.const ℕ).obj (R₁.obj T ⟶ R₁.obj E))
    (hι : ∀ n ξ, ι.app n (cast (hD n).symm ξ) = v n ≫ R₁.map ξ)
    (hc : Nonempty (IsColimit (Cocone.mk _ ι))) :
    ∃ v' : ∀ n, R₂.obj T' ⟶ R₂.obj (F.functor.obj (P n)),
      (∀ n, R₂.map (F.functor.map (a n) ≫ q.hom) ≫ v' n = 𝟙 _) ∧
      (∀ n, v' n ≫ R₂.map (F.functor.map (a n) ≫ q.hom) = 𝟙 _) ∧
      ∃ (D' : ℕ ⥤ Type wD) (hD' : ∀ n, D'.obj n = (F.functor.obj (P n) ⟶ E')),
        ∃ ι' : D' ⟶ (Functor.const ℕ).obj (R₂.obj T' ⟶ R₂.obj E'),
          (∀ n ξ, ι'.app n (cast (hD' n).symm ξ) = v' n ≫ R₂.map ξ) ∧
          Nonempty (IsColimit (Cocone.mk _ ι')) := by
  classical
  let l : ∀ n, D.obj n ≃ (F.functor.obj (P n) ⟶ E') := fun n ↦
    (Equiv.cast (hD n)).trans
      (F.fullyFaithfulFunctor.homEquiv.trans (c.homToEquiv))
  let D' : ℕ ⥤ Type wD :=
    { obj n := F.functor.obj (P n) ⟶ E'
      map {i j} f := TypeCat.ofHom (fun x ↦ l j (D.map f ((l i).symm x)))
      map_id i := by ext x; simp
      map_comp f g := by ext x; simp }
  let t : (R₁.obj T ⟶ R₁.obj E) ≃ (R₂.obj T' ⟶ R₂.obj E') :=
    G.fullyFaithfulFunctor.homEquiv.trans
      (Iso.homCongr (β.app T).symm (β.app E).symm |>.trans
        (Iso.homCongr (R₂.mapIso q) (R₂.mapIso c)))
  let v' : ∀ n, R₂.obj T' ⟶ R₂.obj (F.functor.obj (P n)) := fun n ↦
    R₂.map q.inv ≫ β.hom.app T ≫ G.functor.map (v n) ≫ β.inv.app (P n)
  let ι' : D' ⟶ (Functor.const ℕ).obj (R₂.obj T' ⟶ R₂.obj E') :=
    { app n := TypeCat.ofHom (fun x ↦ t (ι.app n ((l n).symm x)))
      naturality {i j} f := by
        ext x
        change t (ι.app j ((l j).symm (l j (D.map f ((l i).symm x))))) = _
        rw [Equiv.symm_apply_apply]
        exact congrArg t (ConcreteCategory.congr_hom (ι.naturality f) ((l i).symm x)) }
  refine ⟨v', ?_, ?_, D', fun _ ↦ rfl, ι', ?_, ?_⟩
  · intro n
    have hn : R₂.map (F.functor.map (a n)) ≫ β.hom.app T =
        β.hom.app (P n) ≫ G.functor.map (R₁.map (a n)) := β.hom.naturality _
    have hq : R₂.map q.hom ≫ R₂.map q.inv = 𝟙 _ := by
      rw [← Functor.map_comp, q.hom_inv_id, CategoryTheory.Functor.map_id]
    dsimp [v']
    simp only [Functor.map_comp, Category.assoc]
    rw [← Category.assoc (R₂.map q.hom), hq, Category.id_comp]
    rw [← Category.assoc (R₂.map (F.functor.map (a n))), hn, Category.assoc]
    rw [← Category.assoc (G.functor.map (R₁.map (a n))),
      ← Functor.map_comp, hav, CategoryTheory.Functor.map_id, Category.id_comp]
    exact β.hom_inv_id_app _
  · intro n
    have hn : β.inv.app (P n) ≫ R₂.map (F.functor.map (a n)) =
        G.functor.map (R₁.map (a n)) ≫ β.inv.app T := (β.inv.naturality _).symm
    dsimp [v']
    simp only [Functor.map_comp, Category.assoc]
    rw [← Category.assoc (β.inv.app (P n)), hn, Category.assoc]
    rw [← Category.assoc (G.functor.map (v n)), ← Functor.map_comp, hva,
      CategoryTheory.Functor.map_id, Category.id_comp]
    rw [← Category.assoc (β.hom.app T), β.hom_inv_id_app, Category.id_comp,
      ← Functor.map_comp, q.inv_hom_id, CategoryTheory.Functor.map_id]
  · intro n ξ
    let φ : P n ⟶ E := cast (hD n) ((l n).symm ξ)
    have hφ : F.functor.map φ ≫ c.hom = ξ := by
      exact (l n).apply_symm_apply ξ
    change t (ι.app n ((l n).symm ξ)) = v' n ≫ R₂.map ξ
    have hcast : cast (hD n).symm φ = (l n).symm ξ := by simp [φ]
    rw [← hcast, hι, ← hφ]
    dsimp [t, v', Iso.homCongr, Iso.homToEquiv]
    simp only [Functor.map_comp, Category.assoc]
    change R₂.map q.inv ≫ β.hom.app T ≫ G.functor.map (v n ≫ R₁.map φ) ≫
      β.inv.app E ≫ R₂.map c.hom = _
    have hn : β.inv.app (P n) ≫ R₂.map (F.functor.map φ) =
        G.functor.map (R₁.map φ) ≫ β.inv.app E := (β.inv.naturality φ).symm
    rw [← Category.assoc (β.inv.app (P n)), hn]
    simp only [Functor.map_comp, Category.assoc]
  · have hnat : ∀ {i j} (f : i ⟶ j),
        (l j).symm ∘ D'.map f = D.map f ∘ (l i).symm := by
      intro i j f
      funext x
      exact (l j).symm_apply_apply _
    have hh := (Types.isColimit_iff_coconeTypesIsColimit _).mp hc
    have hp := hh.precompose (G := D') (fun n ↦ (l n).symm) hnat
    apply (Types.isColimit_iff_coconeTypesIsColimit _).mpr
    exact hp.of_equiv t (fun _ _ ↦ rfl)

end AlgebraicGeometry.Scheme
