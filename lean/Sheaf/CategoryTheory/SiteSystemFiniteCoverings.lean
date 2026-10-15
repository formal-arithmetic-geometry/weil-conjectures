/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.FinitePrecoverage
public import Mathlib.CategoryTheory.Sites.Finite
import Mathlib.Data.Finite.Sigma
import Sheaf.Paper.SiteCoveringIsomorphicFamily

/-! # Finite coverings on the pair categories

Source: Stacks Project, Categories 004A and Sites 00VH, 0A34.
(blueprint: lem-weil-pbc-site-system-finite-coverings)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Finite presieves whose image under evaluation covers.
Source: Stacks 00VH, the finite-family site transported across the evaluation equivalence.
(blueprint: lem-weil-pbc-site-system-finite-coverings) -/
def finiteEquivalencePrecoverage {A B : Type u} [SmallCategory A] [SmallCategory B]
    (p : A ⥤ B) (P : Precoverage B) : Precoverage A := Precoverage.finite A ⊓ P.comap p

variable {A B : Type u} [SmallCategory A] [SmallCategory B]
  (p : A ⥤ B) (P : Precoverage B)

instance [P.HasIsos] : (finiteEquivalencePrecoverage p P).HasIsos where
  mem_coverings_of_isIso f :=
    ⟨Precoverage.mem_coverings_of_isIso (J := Precoverage.finite A) f,
      Precoverage.mem_coverings_of_isIso (J := P.comap p) f⟩

instance [P.IsStableUnderComposition] :
    (finiteEquivalencePrecoverage p P).IsStableUnderFiniteComposition where
  comp_mem_coverings {ι} [Finite ι] {_S} {_X} f hf {σ} [∀ i, Finite (σ i)] {_Y} g hg :=
    ⟨Precoverage.ofArrows_mem_finite _ _,
      Precoverage.comp_mem_coverings (J := P.comap p) f hf.2 g (fun i ↦ (hg i).2)⟩

instance [p.IsEquivalence] [P.IsStableUnderBaseChange] :
    (finiteEquivalencePrecoverage p P).IsStableUnderFiniteBaseChange where
  mem_coverings_of_isPullback {ι} [Finite ι] {_S} {_X} f hf {_Y} g {_Z} p₁ p₂ h :=
    ⟨Precoverage.ofArrows_mem_finite _ _,
      Precoverage.mem_coverings_of_isPullback (J := P.comap p) f hf.2 g p₁ p₂ h⟩

instance [p.IsEquivalence] [P.HasPullbacks] :
    (finiteEquivalencePrecoverage p P).HasPullbacks where
  hasPullbacks_of_mem f hR := (P.comap p).hasPullbacks_of_mem f hR.2

/-- Every covering in the transported finite precoverage is finite. -/
theorem finiteEquivalencePrecoverage_finite (X : A) (R : Presieve X)
    (hR : R ∈ finiteEquivalencePrecoverage p P X) : Finite R.uncurry := hR.1.to_subtype

private theorem presieve_eq_ofArrows (X : A) (R : Presieve X) :
    R = Presieve.ofArrows (fun i : R.uncurry ↦ i.val.1) (fun i ↦ i.val.2) := by
  apply le_antisymm
  · intro Y f hf
    exact Presieve.ofArrows.mk (⟨⟨Y, f⟩, hf⟩ : R.uncurry)
  · rintro Y f ⟨i⟩
    exact i.property

private theorem finite_map (X : A) (R : Presieve X) (hf : R.uncurry.Finite) :
    (R.map p).uncurry.Finite := by
  have : Finite R.uncurry := hf.to_subtype
  rw [presieve_eq_ofArrows X R, Presieve.map_ofArrows]
  exact Precoverage.ofArrows_mem_finite _ _

private theorem covering_map_iso
    [P.HasIsos] [P.IsStableUnderComposition] [P.IsStableUnderBaseChange] [P.HasPullbacks]
    (q : A ⥤ B) (a : p ≅ q) (X : A) (R : Presieve X) :
    R.map p ∈ P (p.obj X) ↔ R.map q ∈ P (q.obj X) := by
  obtain ⟨ι, Y, f, rfl⟩ := R.exists_eq_ofArrows
  rw [Presieve.map_ofArrows, Presieve.map_ofArrows]
  constructor
  · intro hf
    exact (site_covering_isomorphic_family P (fun i ↦ p.map (f i)) hf
      (a.inv.app X) (fun i ↦ q.map (f i)) (fun i ↦ a.inv.app (Y i))
      (fun i ↦ inferInstance) (fun i ↦ (a.inv.naturality (f i)).symm)).2
  · intro hf
    exact (site_covering_isomorphic_family P (fun i ↦ q.map (f i)) hf
      (a.hom.app X) (fun i ↦ p.map (f i)) (fun i ↦ a.hom.app (Y i))
      (fun i ↦ inferInstance) (fun i ↦ (a.hom.naturality (f i)).symm)).2

/-- The section of evaluation preserves and reflects finite covering presieves. -/
theorem finiteEquivalencePrecoverage_inclusion
    (e : B ⥤ A) (hep : e ⋙ p = 𝟭 B)
    (hfinite : ∀ (X : B) (R : Presieve X), R ∈ P X → Finite R.uncurry)
    (X : B) (R : Presieve X) :
    R ∈ P X ↔ R.map e ∈ finiteEquivalencePrecoverage p P (e.obj X) := by
  have hc : R ∈ P X ↔ (R.map e).map p ∈ P (p.obj (e.obj X)) := by
    change R ∈ P X ↔ R ∈ (P.comap p).comap e X
    rw [← Precoverage.comap_comp, hep, Precoverage.comap_id]
  constructor
  · intro hR
    have : Finite R.uncurry := hfinite X R hR
    exact ⟨finite_map e X R (Set.toFinite _), hc.mp hR⟩
  · exact fun hR ↦ hc.mpr hR.2

/-- Covering families lift through the section, with repetitions lifted consistently. -/
theorem finiteEquivalencePrecoverage_lift
    [P.HasIsos] [P.IsStableUnderComposition] [P.IsStableUnderBaseChange] [P.HasPullbacks]
    (e : B ⥤ A) [e.IsEquivalence] (hep : e ⋙ p = 𝟭 B)
    (X : A) (K : Type u) (Y : K → A) (f : ∀ k, Y k ⟶ X)
    (hR : Presieve.ofArrows Y f ∈ finiteEquivalencePrecoverage p P X) :
    ∃ (Z : B) (T : K → B) (g : ∀ k, T k ⟶ Z)
      (t : e.obj Z ≅ X) (s : ∀ k, e.obj (T k) ≅ Y k),
      Presieve.ofArrows T g ∈ P Z ∧ ∀ k, e.map (g k) ≫ t.hom = (s k).hom ≫ f k := by
  let a : p ≅ e.inv :=
    p.leftUnitor.symm ≪≫ Functor.isoWhiskerRight e.asEquivalence.counitIso.symm p ≪≫
      Functor.associator e.inv e p ≪≫ Functor.isoWhiskerLeft e.inv (eqToIso hep) ≪≫
      e.inv.rightUnitor
  have hc := (covering_map_iso p P e.inv a X (Presieve.ofArrows Y f)).mp hR.2
  rw [Presieve.map_ofArrows] at hc
  exact ⟨e.inv.obj X, fun k ↦ e.inv.obj (Y k), fun k ↦ e.inv.map (f k),
    e.asEquivalence.counitIso.app X, fun k ↦ e.asEquivalence.counitIso.app (Y k), hc,
    fun k ↦ e.asEquivalence.counit.naturality (f k)⟩

/-- A transition compared with an original cover-preserving functor preserves covers. -/
theorem finiteEquivalencePrecoverage_transition
    {A' B' : Type u} [SmallCategory A'] [SmallCategory B']
    (p' : A' ⥤ B') (P' : Precoverage B')
    [P'.HasIsos] [P'.IsStableUnderComposition] [P'.IsStableUnderBaseChange]
    [P'.HasPullbacks]
    (U : B ⥤ B')
    (hcover : ∀ (X : B) (R : Presieve X), R ∈ P X → R.map U ∈ P' (U.obj X))
    (T : A ⥤ A') (a : T ⋙ p' ≅ p ⋙ U) (X : A) (R : Presieve X)
    (hR : R ∈ finiteEquivalencePrecoverage p P X) :
    R.map T ∈ finiteEquivalencePrecoverage p' P' (T.obj X) := by
  have hc : R ∈ P'.comap (p ⋙ U) X := by
    rw [Precoverage.comap_comp]
    exact hcover (p.obj X) (R.map p) hR.2
  have ht := (covering_map_iso (T ⋙ p') P' (p ⋙ U) a X R).mpr hc
  refine ⟨finite_map T X R hR.1, ?_⟩
  change R ∈ (P'.comap p').comap T X
  rw [← Precoverage.comap_comp]
  exact ht

/-- Pullback preservation is transported through the evaluation equivalences. -/
theorem finiteEquivalencePrecoverage_transition_pullback
    [p.IsEquivalence]
    {A' B' : Type u} [SmallCategory A'] [SmallCategory B']
    (p' : A' ⥤ B') [p'.IsEquivalence] (U : B ⥤ B')
    (hpullback : ∀ (X Y Z : B) (R : Presieve X), R ∈ P X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f → PreservesLimit (cospan f g) U)
    (T : A ⥤ A') (a : T ⋙ p' ≅ p ⋙ U)
    (X Y Z : A) (R : Presieve X) (hR : R ∈ finiteEquivalencePrecoverage p P X)
    (f : Y ⟶ X) (g : Z ⟶ X) (hf : R f) : PreservesLimit (cospan f g) T := by
  have := hpullback (p.obj X) (p.obj Y) (p.obj Z) (R.map p) hR.2
    (p.map f) (p.map g) (R.map_map hf)
  have : PreservesLimit (cospan f g ⋙ p) U :=
    preservesLimit_of_iso_diagram U (cospanCompIso p f g).symm
  have : PreservesLimit (cospan f g) (p ⋙ U) := inferInstance
  have : PreservesLimit (cospan f g) (T ⋙ p') :=
    preservesLimit_of_natIso (cospan f g) a.symm
  exact preservesLimit_of_reflects_of_preserves T p'

end CategoryTheory
