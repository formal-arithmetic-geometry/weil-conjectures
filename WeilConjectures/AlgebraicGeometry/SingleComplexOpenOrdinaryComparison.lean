/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenTensorRestrictionIso
public import WeilConjectures.AlgebraicGeometry.OpenDerivedAdditiveStalkIso
public import WeilConjectures.AlgebraicGeometry.AffineSpectrumOrdinaryComparisonSquare
public import WeilConjectures.AlgebraicGeometry.StalkComparisonPullbackNaturality
import WeilConjectures.Algebra.Homology.BaseDerivedTensorRingTransport
import WeilConjectures.AlgebraicGeometry.OpenOrdinaryTensorGermTransport

/-! # Open restriction of the ordinary tensor comparison

## References

* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry
open SingleComplexBaseChange
set_option synthInstance.maxSize 2048

/-- Inverting a pullback counit and then applying it recovers the ordinary comparison. -/
theorem comparisonIntoPullback_comp_counit
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) (z : X')
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hcP : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
    (i : ℤ) :
    comparisonIntoPullback f f' g g' sq z P hcP i ≫
      (comparisonStalkCohomology X' z i).map
        (cast (by rfl) ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) =
      comparisonIntoTensorPullback f f' g g' sq z P i := by
  have := hcP
  simp only [comparisonIntoPullback, comparisonIntoTensorPullback, cast_eq, Category.assoc,
    ← Functor.map_comp, IsIso.inv_hom_id]
  simp

set_option maxHeartbeats 1000000 in
-- Elaborating coefficient transport through the four stalk rings needs this budget.
/-- Scalar transport of the base-derived tensor comparison to the ordinary pullback.
This statement concerns arbitrary complexes, without K-flatness or derived counits. -/
theorem exists_singleComplexOpen_ordinary_comparison
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (V : S.Opens) (V' : S'.Opens) (hV' : V' ≤ g ⁻¹ᵁ V)
    (j : (f' ⁻¹ᵁ V').toScheme ⟶ (f ⁻¹ᵁ V).toScheme)
    (hj : j ≫ (f ⁻¹ᵁ V).ι = (f' ⁻¹ᵁ V').ι ≫ g')
    (sq₀ : IsPullback j (f' ∣_ V') (f ∣_ V) (g.resLE V V' hV'))
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (z : (f' ⁻¹ᵁ V').toScheme) (i : ℤ) :
    letI : (schemeOpenRestriction X (f ⁻¹ᵁ V)).Additive :=
      schemeOpenRestriction_additive X (f ⁻¹ᵁ V)
    letI : (schemeOpenRestriction X (f ⁻¹ᵁ V)).PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_additive _
    let Q := ((schemeOpenRestriction X (f ⁻¹ᵁ V)).mapHomologicalComplex (.up ℤ)).obj P
    let F₀ := forget₂ (ModuleCat.{u} ((f' ⁻¹ᵁ V').toScheme.presheaf.stalk z)) AddCommGrpCat.{u}
    let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk z.val)) AddCommGrpCat.{u}
    let H₀ := comparisonStalkCohomology (f' ⁻¹ᵁ V').toScheme z i
    let β := singleComplexOpenTensorRestrictionMap g' (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj P
    let ν := openDerivedAdditiveStalkIso X' (f' ⁻¹ᵁ V') z i
    ∃ l : F₀.obj ((Arrow.mk (comparisonIntoTensorPullback (f ∣_ V) (f' ∣_ V')
        (g.resLE V V' hV') j sq₀ z Q i)).left) ≅
        F.obj ((Arrow.mk (comparisonIntoTensorPullback f f' g g' sq z.val P i)).left),
      F₀.map (comparisonIntoTensorPullback (f ∣_ V) (f' ∣_ V')
          (g.resLE V V' hV') j sq₀ z Q i) ≫
        F₀.map (H₀.map β) ≫
          ν.hom.app (DerivedCategory.Q.obj
            (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P)) =
      l.hom ≫ F.map (comparisonIntoTensorPullback f f' g g' sq z.val P i) := by
  have : (schemeOpenRestriction X (f ⁻¹ᵁ V)).Additive :=
    schemeOpenRestriction_additive X (f ⁻¹ᵁ V)
  let Q₀ := ((schemeOpenRestriction X (f ⁻¹ᵁ V)).mapHomologicalComplex (.up ℤ)).obj P
  let := leftAlgebra (f ∣_ V) j z
  let := rightAlgebra (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z
  let := (tensorMap (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z).toAlgebra
  let := leftAlgebra f g' z.val
  let := rightAlgebra f f' g g' sq z.val
  let := (tensorMap f f' g g' sq z.val).toAlgebra
  let := HasDerivedCategory.standard (ModuleCat.{u} (R (f ∣_ V) j z))
  let := HasDerivedCategory.standard (ModuleCat.{u} (B (f' ∣_ V') z))
  let := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z.val))
  let := HasDerivedCategory.standard (ModuleCat.{u} (B f' z.val))
  obtain ⟨eR, eA, eB, eC, hRA, hRB, hCA, hCB, α, hα, τ, hτ, ht⟩ :=
    exists_openOrdinaryTensor_germ_transport f f' g g' sq V V' hV' j hj sq₀ P z i
  let M := cohomologyModel (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z Q₀
  let N := cohomologyModel f f' g g' sq z.val P
  obtain ⟨l, hl⟩ := ModuleCat.exists_baseDerivedTensor_ring_transport
    (stalkComplex j z Q₀) (stalkComplex g' z.val P) M N
    eR eA eB eC hRA hRB hCA hCB α hα τ hτ i
  let F₀ := forget₂ (ModuleCat.{u} ((f' ⁻¹ᵁ V').toScheme.presheaf.stalk z)) AddCommGrpCat.{u}
  let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk z.val)) AddCommGrpCat.{u}
  let T₀ := tensorComplex (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z Q₀
  let T := tensorComplex f f' g g' sq z.val P
  let k₀ := HomologicalComplex.homologyMap
    (tensorStalkIso (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z Q₀).hom i ≫
    (comparisonStalkHomologyIso (f' ⁻¹ᵁ V').toScheme z
      (((Scheme.Modules.tensorPullback j).mapHomologicalComplex (.up ℤ)).obj Q₀) i).inv
  let k := HomologicalComplex.homologyMap (tensorStalkIso f f' g g' sq z.val P).hom i ≫
    (comparisonStalkHomologyIso X' z.val
      (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P) i).inv
  let r := ((T₀.sc i).mapHomologyIso F₀).inv ≫
    HomologicalComplex.homologyMap τ.hom i ≫ ((T.sc i).mapHomologyIso F).hom
  let H₀ := comparisonStalkCohomology (f' ⁻¹ᵁ V').toScheme z i
  let β := singleComplexOpenTensorRestrictionMap g' (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj P
  let ν := openDerivedAdditiveStalkIso X' (f' ⁻¹ᵁ V') z i
  let W := letI : HasDerivedCategory.{w} X'.Modules :=
      (inferInstance : ∀ Y : Scheme.{u},
        HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))) X'
    DerivedCategory.Q.obj
      (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P)
  have ht' : F₀.map k₀ ≫ F₀.map (H₀.map β) ≫ ν.hom.app W = r ≫ F.map k := ht
  have hl' : F₀.map (M.localizedComparison i) ≫ r =
      l.hom ≫ F.map (N.localizedComparison i) := by
    simpa only [r, M, N, T, T₀, F₀, F, tensorComplex, RingHom.algebraMap_toAlgebra,
      Category.assoc] using hl
  refine ⟨l, ?_⟩
  change F₀.map (M.localizedComparison i ≫ k₀) ≫
      F₀.map (H₀.map β) ≫ ν.hom.app W =
    l.hom ≫ F.map (N.localizedComparison i ≫ k)
  simp only [Functor.map_comp, Category.assoc]
  rw [ht', ← Category.assoc, hl']
  simp only [Category.assoc]

end AlgebraicGeometry
