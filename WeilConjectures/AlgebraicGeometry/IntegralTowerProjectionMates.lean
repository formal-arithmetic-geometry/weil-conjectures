/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTowerData

import WeilConjectures.AlgebraicGeometry.IntegralProperBaseChange
import WeilConjectures.AlgebraicGeometry.OpenExtensionConstantModelConstructible
import WeilConjectures.AlgebraicGeometry.ConstantModelStratificationTransportSupplement
import all WeilConjectures.AlgebraicGeometry.IntegralCriterionReductionsSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionEssImage

/-! # Components of the integral direct-image tower argument -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  AlgebraicGeometry.ProEtale.CondensedRing.upperStar
  AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectProjectionMap

universe u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Transport the existing proper projection theorem along an equality of coefficient
monoid objects, retaining the multiplication as well as the underlying abelian sheaf. -/
private theorem proper_projection_coefficients
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    {Z Y : Scheme.{u}} [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (g : Z ⟶ Y) [g.IsOver (Spec (.of k))] [IsProper g]
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    [IsCommMonObj Λ.X] (hΛ : Mon.mk (DerivedNakayama.integerRing l E) = Λ)
    (N : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ.X Z)))
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ.X Y)))
    (hN : constantModelBoundedConstructible Λ.X Z N)
    (hL : constantModelBoundedConstructible Λ.X Y L) :
    IsIso (CondensedRing.moduleObjectProjectionMap Λ.X g N L) := by
  subst Λ
  exact (CondensedRing.integralProperDirectImageAndFormulas l E k g).2.2.2 N L hN hL

/-- Extend the finite stratification of a constructible module by zero. -/
private theorem open_preserves_heart_constructible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    {X Z : Scheme.{u}} [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    (j : X ⟶ Z) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hN : IsConstantModelConstructible Λ X N) :
    IsConstantModelConstructible Λ Z ((CondensedRing.openImmersionLowerShriek Λ j).obj N) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of k))
  have : QuasiSeparatedSpace X :=
    quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of k))
  have hX : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
  rw [IsConstantModelConstructible, if_pos hX] at hN
  obtain ⟨S, hcon, hS⟩ := (Scheme.constructibleStratification_iff_locallyClosed X
    (fun T f ↦ HasFiniteConstantLocalModel Λ T ((CondensedRing.upperStar Λ f).obj N))).1.mp hN
  exact (constantModelConstructible_openImmersionLowerShriek l (ringChar k)
    (Fact.out : ringChar k ≠ l) k Λ j
    N S hcon hS).1

/-- Apply the sheaf result to homology and use the exact derived homology comparison. -/
private theorem open_preserves_constructible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    {X Z : Scheme.{u}} [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    (j : X ⟶ Z) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (M : ConstantModelBoundedConstructible Λ X) :
    constantModelBoundedConstructible Λ Z
      ((CondensedRing.openImmersionLowerShriek Λ j).mapDerivedCategory.obj M.obj) := by
  refine ⟨(CondensedRing.openImmersionLowerShriek Λ j).bounded_mapDerivedCategory_obj
    M.property.1, ?_⟩
  intro n
  exact constantModelConstructible_transport Λ
    (((CondensedRing.openImmersionLowerShriek Λ j).mapDerivedCategoryHomologyFunctorIso n).app
      M.obj)
    (open_preserves_heart_constructible l Λ k j
      ((DerivedCategory.homologyFunctor _ n).obj M.obj) (M.property.2 n))


/-- The open unit is invertible and the tensor target lies in the essential image of
exact extension by zero. Apply the generic adjunction projection theorem with the
specified inverse tensor comparison; this is exactly the defining open mate. -/
private theorem open_projection_isIso {U T : Scheme.{u}} (j : U ⟶ T)
    [IsOpenImmersion j] (M : Integral l E U) (K : Integral l E T) :
    IsIso (openProjection l E j M K) := by
  let a := CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction
    (spIntegralCondensed l E) j
  let a₀ := CondensedRing.openImmersionLowerShriekUpperStarAdjunction
    (spIntegralCondensed l E) j
  have hff := a.fullyFaithfulLOfCompIsoId
    ((Functor.mapDerivedCategoryCompIso
        (CondensedRing.openImmersionLowerShriek (spIntegralCondensed l E) j)
        (CondensedRing.upperStar (spIntegralCondensed l E) j)).symm ≪≫
      Functor.mapDerivedCategoryNatIso (asIso a₀.unit).symm ≪≫
        Functor.mapDerivedCategoryIdIso _)
  have := hff.full
  have := hff.faithful
  have : IsIso (openAdjunction l E j).unit :=
    Adjunction.unit_isIso_of_L_fully_faithful _
  obtain ⟨Z, ⟨e⟩⟩ :=
    CondensedRing.tensorObj_mem_essImage_mapDerivedCategory_openImmersionLowerShriek
      (spIntegralCondensed l E) j M K
  have h := Adjunction.isIso_projectionMap_app_app_of_iso
    (openAdjunction l E j) (pull l E j) (tensor l E U) (tensor l E T)
    (CondensedRing.leftDerivedUpperStarTensorIso (spIntegralCondensed l E) j).inv
    M K Z e.symm
  rw [Adjunction.projectionMap_app_app] at h
  exact h

/-- Invertibility of the actual integral proper and open compact-support projection mates.
Source: blueprint latest direct-image.proof.md paragraph (3), final sentence.
Proof: exact open extension preserves bounded constant-model constructibility, by
applying the existing constructible extension theorem to each cohomology sheaf. The proper
projection theorem applies to this extension and K. Its absolute-value coefficient
presentation equals the spectral-norm integral ring as a monoid object, so transport of
the entire quantified assertion retains the canonical map. The open projection is the
existing source-library unit-transpose projection for an open immersion, hence invertible
on all unbounded complexes. The pullback factorization is invertible, as are its tensor
image, its compact-support image, and the proper image of the open projection. Their
composite is compactOpenProjection. Zero inputs and empty schemes require no exclusions.
(blueprint: lem-sp-integral-tower-projection-mates). -/
theorem integral_projection_mates :
    ∀ (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
      (X Y : Scheme.{u}) [X.Over (Spec (.of k))]
      [Y.Over (Spec (.of k))]
      [LocallyOfFiniteType (X ↘ Spec (.of k))]
      [QuasiCompact (X ↘ Spec (.of k))]
      [IsSeparated (X ↘ Spec (.of k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of k))]
      [QuasiCompact (Y ↘ Spec (.of k))]
      [IsSeparated (Y ↘ Spec (.of k))]
      (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
      (d : ℕ) [SmoothOfRelativeDimension d f],
    ∀ (c : Compactification f) (M : Constructible l E X) (K : Constructible l E Y),
        IsIso (properProjection l E c M.obj K.obj) ∧
        IsIso (compactOpenProjection l E c M.obj K.obj) := by
  intro k _ _ _ X Y _ _ _ _ _ _ _ _ f _ d _ c M K
  classical
  let : c.Z.Over (Spec (.of k)) := ⟨c.g ≫ (Y ↘ Spec (.of k))⟩
  let : LocallyOfFiniteType (c.Z ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (c.g ≫ (Y ↘ Spec (.of k))))
  let : QuasiCompact (c.Z ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact (c.g ≫ (Y ↘ Spec (.of k))))
  let : IsSeparated (c.Z ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated (c.g ≫ (Y ↘ Spec (.of k))))
  let : c.g.IsOver (Spec (.of k)) :=
    (Scheme.Hom.isOver_iff (Spec (.of k))).mpr rfl
  let : c.i.IsOver (Spec (.of k)) :=
    (Scheme.Hom.isOver_iff (Spec (.of k))).mpr (by
      change c.i ≫ c.g ≫ (Y ↘ Spec (.of k)) = X ↘ Spec (.of k)
      rw [← Category.assoc, ← c.comm]
      exact comp_over f _)
  have hJ := open_preserves_constructible l (spIntegralCondensed l E) k c.i M
  constructor
  · change IsIso (CondensedRing.moduleObjectProjectionMap (spIntegralCondensed l E)
      c.g ((openD l E c.i).obj M.obj) K.obj)
    exact proper_projection_coefficients l E k c.g (sfbCondensedIntegers l E)
      (integralPointMon_eq l E) ((openD l E c.i).obj M.obj) K.obj hJ K.property
  · have hopen := open_projection_isIso l E c.i M.obj ((pull l E c.g).obj K.obj)
    let := hopen
    dsimp only [compactOpenProjection]
    infer_instance

end AlgebraicGeometry.ProEtale.IntegralDirectImageTower
