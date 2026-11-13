/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenRestrictionData
public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.SingleComplexOpenCoordinateStalkTransportData

/-! # Stalkwise conjugacy for transported open coordinates.

The proof is the termwise stalk calculation: open-immersion stalk isomorphisms
identify the four local rings and complexes, and naturality of tensor extension,
homology, and the representing map conjugates the two comparison arrows.

## References

* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

open SingleComplexBaseChange in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem stalkComparison_normalized
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    {K : schemeDerivedCategory X} {K' : schemeDerivedCategory X'}
    {φ : (derivedPullback g').obj K ⟶ K'}
    (c : Coordinates g' K K' φ) (z : X') (i : ℤ) :
    stalkComparison f f' g g' sq c z i ≫
        ((comparisonStalkHomologyIso X' z c.N i).inv ≫
          (comparisonStalkCohomology X' z i).map c.e'.hom) =
      comparisonIntoPullback f f' g g' sq z c.P c.counit_isIso i ≫
        (comparisonStalkCohomology X' z i).map ((derivedPullback g').map c.e.hom ≫ φ) := by
  let := leftAlgebra f g' z
  let := rightAlgebra f f' g g' sq z
  let := (tensorMap f f' g g' sq z).toAlgebra
  let := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
  let := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
  have := c.counit_isIso
  have ht := comparisonStalkHomologyIso_naturality X' z c.t i
  have ht' : HomologicalComplex.homologyMap
      (((RingedSpace.moduleStalkFunctor X'.toRingedSpace z).mapHomologicalComplex
        (.up ℤ)).map c.t) i ≫ (comparisonStalkHomologyIso X' z c.N i).inv =
      (comparisonStalkHomologyIso X' z
        (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj c.P) i).inv ≫
          (comparisonStalkCohomology X' z i).map (DerivedCategory.Q.map c.t) := by
    apply (cancel_epi (comparisonStalkHomologyIso X' z
      (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj c.P) i).hom).mp
    rw [← Category.assoc, ← ht]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  have ht'' := congrArg (fun a => a ≫ (comparisonStalkCohomology X' z i).map c.e'.hom) ht'
  simp only [Category.assoc] at ht''
  simp only [stalkComparison, comparisonIntoPullback, Category.assoc, Functor.map_comp, cast_eq]
  rw [← Functor.map_comp, ← Functor.map_comp, ← c.represents]
  simp only [Functor.map_comp, cast_eq, IsIso.inv_hom_id_assoc]
  rw [ht'']

private theorem normalized_square
    {D : Type*} [Category D] {A₀ A B₀ B L₀ L M₀ M : D}
    (a : A₀ ⟶ B₀) (b : A ⟶ B) (l : A₀ ≅ A)
    (td : B₀ ≅ M₀) (tc : B ≅ M) (ν : M₀ ≅ M) (v : L₀ ≅ L)
    (p : A₀ ⟶ L₀) (q : A ⟶ L) (μ : L₀ ⟶ M₀) (η : L ⟶ M)
    (hd : a ≫ td.hom = p ≫ μ) (hc : b ≫ tc.hom = q ≫ η)
    (hl : p ≫ v.hom = l.hom ≫ q) (hn : μ ≫ ν.hom = v.hom ≫ η) :
    l.hom ≫ b = a ≫ (td ≪≫ ν ≪≫ tc.symm).hom := by
  apply (cancel_mono tc.hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  rw [hc, ← Category.assoc, ← hl, Category.assoc, ← hn, ← Category.assoc, ← hd]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Elaborating the mapped normalization equations unfolds nested derived tensor sources.
/-- The restricted and original stalk comparison arrows are isomorphic after
forgetting scalars, for any coordinates of the canonical restricted coefficient.
No invertibility of either comparison is assumed. -/
theorem nonempty_singleComplexOpen_stalk_arrow_iso
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (c : SingleComplexBaseChange.Coordinates g' K K' φ)
    (V : S.Opens) (V' : S'.Opens) (hV' : V' ≤ g ⁻¹ᵁ V)
    (j : (f' ⁻¹ᵁ V').toScheme ⟶ (f ⁻¹ᵁ V).toScheme)
    (hj : j ≫ (f ⁻¹ᵁ V).ι = (f' ⁻¹ᵁ V').ι ≫ g')
    (sq₀ : IsPullback j (f' ∣_ V') (f ∣_ V) (g.resLE V V' hV'))
    (d : SingleComplexBaseChange.Coordinates j
      ((schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategory.obj K)
      ((schemeOpenRestriction X' (f' ⁻¹ᵁ V')).mapDerivedCategory.obj K')
      (singleComplexRestrictedCoefficient g' K K' φ
        (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj)) :
    ∀ (z : (f' ⁻¹ᵁ V').toScheme) (i : ℤ),
      Nonempty
        (Arrow.mk ((forget₂ (ModuleCat.{u} ((f' ⁻¹ᵁ V').toScheme.presheaf.stalk z))
            AddCommGrpCat.{u}).map
              (SingleComplexBaseChange.stalkComparison
                (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ d z i)) ≅
          Arrow.mk ((forget₂ (ModuleCat.{u} (X'.presheaf.stalk z.val))
            AddCommGrpCat.{u}).map
              (SingleComplexBaseChange.stalkComparison f f' g g' sq c z.val i))) :=
  open SingleComplexBaseChange in by
    intro z i
    let F₀ := forget₂ (ModuleCat.{u} ((f' ⁻¹ᵁ V').toScheme.presheaf.stalk z)) AddCommGrpCat.{u}
    let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk z.val)) AddCommGrpCat.{u}
    let H₀ := comparisonStalkCohomology (f' ⁻¹ᵁ V').toScheme z i
    let H := comparisonStalkCohomology X' z.val i
    let R := (schemeOpenRestriction X' (f' ⁻¹ᵁ V')).mapDerivedCategory
    let θ := singleComplexRestrictedCoefficient g' K ((derivedPullback g').obj K) (𝟙 _)
      (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj
    obtain ⟨ν, l, hl⟩ := exists_singleComplexOpen_normalized_transport
      f f' g g' sq K V V' hV' j hj sq₀ c.P d.P c.e d.e
      c.isKFlat d.isKFlat c.counit_isIso d.counit_isIso z i
    let td := F₀.mapIso ((comparisonStalkHomologyIso (f' ⁻¹ᵁ V').toScheme z d.N i).symm ≪≫
      H₀.mapIso d.e')
    let tc := F.mapIso ((comparisonStalkHomologyIso X' z.val c.N i).symm ≪≫ H.mapIso c.e')
    let r := td ≪≫ ν.app K' ≪≫ tc.symm
    refine ⟨Arrow.isoMk l r ?_⟩
    have hφ : singleComplexRestrictedCoefficient g' K K' φ
        (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj = θ ≫ R.map φ := by
      simp [θ, R, singleComplexRestrictedCoefficient, Category.assoc]
    have hd : F₀.map (stalkComparison (f ∣_ V) (f' ∣_ V')
        (g.resLE V V' hV') j sq₀ d z i) ≫ td.hom =
        F₀.map (comparisonIntoPullback (f ∣_ V) (f' ∣_ V')
            (g.resLE V V' hV') j sq₀ z d.P d.counit_isIso i ≫
          H₀.map ((derivedPullback j).map d.e.hom ≫ θ)) ≫
            (R ⋙ H₀ ⋙ F₀).map φ := by
      have hd₀ := congrArg F₀.map (stalkComparison_normalized (f ∣_ V) (f' ∣_ V')
        (g.resLE V V' hV') j sq₀ d z i)
      have hp := congrArg (fun t ↦ F₀.map
        (comparisonIntoPullback (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀
          z d.P d.counit_isIso i ≫ H₀.map ((derivedPullback j).map d.e.hom ≫ t))) hφ
      simpa only [td, H₀, Functor.mapIso_hom, Iso.trans_hom, Iso.symm_hom,
        Category.assoc, Functor.map_comp, Functor.comp_map] using hd₀.trans hp
    have hc : F.map (stalkComparison f f' g g' sq c z.val i) ≫ tc.hom =
        F.map (comparisonIntoPullback f f' g g' sq z.val c.P c.counit_isIso i ≫
          H.map ((derivedPullback g').map c.e.hom)) ≫ (H ⋙ F).map φ := by
      simpa only [tc, H, Functor.mapIso_hom, Iso.trans_hom, Iso.symm_hom,
        Category.assoc, Functor.map_comp, Functor.comp_map] using
        congrArg F.map (stalkComparison_normalized f f' g g' sq c z.val i)
    have hn := ν.hom.naturality φ
    exact normalized_square _ _ l td tc (ν.app K') (ν.app ((derivedPullback g').obj K))
      _ _ _ _ hd hc hl hn

end AlgebraicGeometry
