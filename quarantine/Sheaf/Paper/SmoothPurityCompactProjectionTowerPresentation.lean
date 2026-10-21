/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F8
-/
module

public import Sheaf.Paper.SmoothPurityCompactProjectionData
import Sheaf.Paper.SmoothPurityCompactProjectionTowerOperations
import Sheaf.CategoryTheory.DiagramSiteTopology
import Sheaf.Paper.SmoothPurityTowerInjectiveComponents

/-! # Normalized compact-projection presentations

Source: Stacks 03D7, 07A4, 03DI, 0GL1 and the finite/tower construction in
blueprint `lem-sp-compact-projection-base-change`, proof step 1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open SheafOfModules.OpenTensorNormalization
open AlgebraicGeometry.Scheme.ProjectionRestriction
namespace AlgebraicGeometry.ProEtale.CompactProjectionBaseChange

private theorem tower_topology (T : Scheme.{u}) :
    topology .systems T = verticalDiagramSiteTopology ℕ T.ProEt (ProEt.topology T) := by
  apply le_antisymm
  · apply Precoverage.toGrothendieck_le_iff_le_toPrecoverage.mpr
    intro W P hP
    obtain ⟨S, hS, rfl⟩ := hP
    apply (ProEt.topology T).superset_covering _ hS
    intro V f hf
    exact Sieve.le_generate _ _ _ (show W.1 = W.1 ∧ S f from ⟨rfl, hf⟩)
  · intro W S hS
    let P : Presieve W := fun V a ↦ V.1 = W.1 ∧
      S ((Prod.sectR W.1 T.ProEt).map a.2)
    have hP : P ∈ verticalCoverage T W :=
      ⟨S.functorPullback (Prod.sectR W.1 T.ProEt), hS, rfl⟩
    apply (topology .systems T).superset_covering _
      (Precoverage.generate_mem_toGrothendieck hP)
    apply (Sieve.generate_le_iff _ _).mpr
    rintro ⟨n, V⟩ f ⟨hn, hf⟩
    dsimp only at hn
    subst n
    have hfmap : (Prod.sectR W.1 T.ProEt).map f.2 = f := by
      ext
      · exact Subsingleton.elim _ _
      · rfl
    rwa [hfmap] at hf

private def tower_ring_presheaf (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u}) :
    (ℕ × T.ProEt)ᵒᵖ ⥤ CommRingCat.{u + 1} where
  obj W := ((spCoefficientCommRings l E T).obj (op W.unop.1)).obj.obj (op W.unop.2)
  map f := CommRingCat.ofHom ((spCoefficientPresheaf l E T).map f).hom
  map_id W := by
    apply CommRingCat.hom_ext
    exact congrArg RingCat.Hom.hom ((spCoefficientPresheaf l E T).map_id W)
  map_comp f g := by
    apply CommRingCat.hom_ext
    exact congrArg RingCat.Hom.hom ((spCoefficientPresheaf l E T).map_comp f g)

private theorem tower_ring_presheaf_forget (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u}) :
    tower_ring_presheaf l E T ⋙ forget₂ CommRingCat RingCat =
      spCoefficientPresheaf l E T := by
  rfl

private def tower_ring (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u}) :
    Sheaf (topology .systems T) CommRingCat.{u + 1} where
  obj := tower_ring_presheaf l E T
  property := by
    rw [tower_topology]
    apply (verticalDiagramSite_isSheaf_iff ℕ T.ProEt (ProEt.topology T) _).2
    intro n
    let e : (Prod.sectR n T.ProEt).op ⋙ tower_ring_presheaf l E T ≅
        ((spCoefficientCommRings l E T).obj (op n)).obj :=
      NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
        intro V W f
        simp [tower_ring_presheaf, spCoefficientPresheaf, spCoefficientRings,
          spCoefficientCommRings, Prod.sectR]
        rfl)
    exact (Presheaf.isSheaf_of_iso_iff e).2
      ((spCoefficientCommRings l E T).obj (op n)).property

private def tower_coefficients (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] : Coefficients.{u} .systems where
  ring := tower_ring l E
  map {X Y} f := ⟨{
    app W := CommRingCat.ofHom (spTowerRingMapApp l E f W).hom
    naturality := by
      intro V W a
      apply CommRingCat.hom_ext
      exact congrArg RingCat.Hom.hom (spTowerRingMap_naturality l E f a) }⟩

private theorem tower_coefficients_normalized (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    TowerCoefficients l E (tower_coefficients l E) := by
  refine ⟨fun T ↦ rfl, ?_, ?_⟩
  · intro X Y f n W
    rfl
  · intro T
    have hs (M : PresheafOfModules.{u + 1} (spCoefficientPresheaf l E T)) :
        Presheaf.IsSheaf (topology .systems T) M.presheaf ↔
          spCoefficientTowerSheafCondition l E T M := by
      rw [tower_topology]
      exact verticalDiagramSite_isSheaf_iff ℕ T.ProEt (ProEt.topology T) M.presheaf
    let F : spCoefficientTowers l E T ⥤ Mod ((tower_coefficients l E).ring T) :=
      { obj := fun M ↦ ⟨M.obj, (hs M.obj).2 M.property⟩
        map := fun f ↦ ⟨f.hom⟩ }
    let G : Mod ((tower_coefficients l E).ring T) ⥤ spCoefficientTowers l E T :=
      { obj := fun M ↦ ⟨M.val, (hs M.val).1 M.isSheaf⟩
        map := fun f ↦ CategoryTheory.ObjectProperty.homMk f.val }
    let e : spCoefficientTowers l E T ≌ Mod ((tower_coefficients l E).ring T) :=
      { functor := F
        inverse := G
        unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)
        counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) }
    refine ⟨e, ?_, fun M ↦ HEq.rfl, fun M N f ↦ HEq.rfl⟩
    refine { map_add := ?_ }
    intro X Y f g
    rfl

/-- Simultaneous canonical operations for the actual varying coefficient-ring system,
including the equivalence that preserves whole module presheaves and linear maps.
Source: blueprint coefficient-tower lemma; Stacks 00Z4, 03D7, 03DI, 07A4 and 0GL1
(blueprint: lem-sp-compact-projection-tower-presentation).

Proof: uncurry `spCoefficientCommRings` on the vertical diagram site. The vertical
sheaf condition identifies this commutative ring sheaf with the recorded coefficient
presheaf after forgetting commutativity. Rebundle the very same module presheaves
as sheaves of modules on this site. The inverse forgets only the global sheaf proof,
so the equivalence fixes presheaves, morphisms and all semilinear transitions.
Use the constant-section direct-image maps at every level; their naturality for
quotient-ring reductions gives the ring-system structural maps. Scheme inverse image
is levelwise exact and leaves the coefficient index fixed. Its module adjoint,
K-injective derived direct image, and flat-term K-flat signed total tensor give the
fields of `Presentation`. Fibre-product comparison acts on sections at every index,
giving the prescribed `rightSquare` and `rightSections`. Extension by zero is exact
on the vertical site. Apply open normalization there, rather than detecting derived
equalities level by level, to obtain `OpenComparisons`. No scalar-extension functor
along a nonflat coefficient transition is asserted to be exact. -/
theorem tower_presentation_exists (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    ∃ c : Coefficients.{u} .systems, TowerCoefficients l E c ∧
      ∃ o : Presentation c, Nonempty (OpenComparisons o) := by
  refine ⟨tower_coefficients l E, tower_coefficients_normalized l E, ?_⟩
  exact normalized_tower_operations_exists l E _ (tower_coefficients_normalized l E)

end AlgebraicGeometry.ProEtale.CompactProjectionBaseChange
