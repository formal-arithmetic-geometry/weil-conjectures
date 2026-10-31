/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralCompactSupportCoefficientData
public import WeilConjectures.AlgebraicGeometry.InverseImagePullbackComparisonDerived
import all WeilConjectures.AlgebraicGeometry.IsomorphismDerivedPullback
import all WeilConjectures.AlgebraicGeometry.ProEtaleIsomorphismInverseImage
import WeilConjectures.AlgebraicGeometry.IntegralCompactSupportCoefficientComparison
import WeilConjectures.AlgebraicGeometry.PullbackIdentitiesScalarExtension
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-! # Completed direct image under an isomorphism of targets

Source: the inverse-automorphism-square argument in blueprint lem-fix-weil-operations.
(blueprint: lem-sf-completed-direct-image-target-iso).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures
open PurCompactSupport

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private instance inverseImageAdd {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    (inverseImageIntegralModules l E g).Additive :=
  isoSectionwiseModuleInverseImage_additive g (inverseImageCompletedCoefficientMap l E g)

private instance inverseImageLimits {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    PreservesFiniteLimits (inverseImageIntegralModules l E g) :=
  isoSectionwiseModuleInverseImage_limits g (inverseImageCompletedCoefficientMap l E g)

private instance inverseImageColimits {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    PreservesFiniteColimits (inverseImageIntegralModules l E g) :=
  isoSectionwiseModuleInverseImage_colimits g (inverseImageCompletedCoefficientMap l E g)

private theorem completedDirectMap {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    let shAdj := isoSheafAdjunction g RingCat.{u + 1}
    shAdj.unit.app (completedIntegralCoefficientSheafUnrestricted l E Y) ≫
      (proEtaleSheafDirectImage g RingCat.{u + 1}).map
        (inverseImageCompletedCoefficientMap l E g) =
      (sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (proEtaleRingDirectImageMap g ((completed l E).ring Y) ((completed l E).ring X)
          ((completed l E).pull g)) := by
  dsimp only
  let shAdj := isoSheafAdjunction g RingCat.{u + 1}
  let G := proEtaleSheafDirectImage g RingCat.{u + 1}
  let F := isoSectionwiseInverseImage g RingCat.{u + 1}
  let V := sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  have he : proEtaleRingDirectImageMap g ((completed l E).ring Y)
      ((completed l E).ring X) ((completed l E).pull g) = sfCompletedCoefficientMap l E g := by
    change (proEtaleSheafAdjunction g CommRingCat).homEquiv _ _
      (((proEtaleSheafAdjunction g CommRingCat).homEquiv _ _).symm _) = _
    exact Equiv.apply_symm_apply _ _
  rw [he]
  let : G.IsRightAdjoint := shAdj.isRightAdjoint
  apply (isLimitOfPreserves G (limit.isLimit
    (integralCoefficientSheafSystem l E X))).hom_ext
  intro n
  change (_ ≫ _) ≫ G.map (limit.π _ n) = _ ≫ G.map (limit.π _ n)
  erw [Category.assoc, ← G.map_comp]
  have hc : inverseImageCompletedCoefficientMap l E g ≫
      limit.π (integralCoefficientSheafSystem l E X) n =
      F.map (limit.π (integralCoefficientSheafSystem l E Y) n) ≫
        inverseImageFiniteCoefficientMap l E g n.unop := limit.lift_π _ n
  erw [hc, G.map_comp, ← Category.assoc, ← shAdj.unit.naturality,
    Category.assoc, sectionwiseConstantDirectMap]
  exact (congrArg V.map
    ((sfCompletedCoefficientMap_existsUnique l E g).exists.choose_spec n.unop)).symm

private theorem inverseImageAdjunction {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    Nonempty (inverseImageIntegralModules l E g ⊣
      proEtaleRingModuleDirectImage g ((completed l E).ring Y)
        ((completed l E).ring X) ((completed l E).pull g)) := by
  obtain ⟨a⟩ := sectionwiseModuleAdjunction g
    (completedIntegralCoefficientSheafUnrestricted l E Y)
    (completedIntegralCoefficientSheafUnrestricted l E X)
    (inverseImageCompletedCoefficientMap l E g)
  exact ⟨a.ofNatIsoRight (SheafOfModules.pushforwardCongr (completedDirectMap l E g))⟩

/-- Direct image along the inverse of a target isomorphism is exact inverse image.
Source: the proper/open target-transport argument in
literature/blueprint/latest/blueprint/sec-six-functors/sk-rem-sf-pf-done/
lem-fix-weil-operations.proof.md.
(blueprint: lem-sf-completed-direct-image-target-iso).

Proof: on the small pro-etale sites an isomorphism induces inverse equivalences
by base change. The completed coefficient sheaves identify under these equivalences:
the identifications are the inverse limits of the same constant quotient-ring maps.
Sectionwise, direct image along the inverse is therefore the inverse-image functor,
with the identical scalar action. Both functors are exact. Derive their sectionwise
natural isomorphism and combine it with the canonical derived direct-image compositor
for p followed by e.inv. This gives the stated isomorphism on the entire unbounded
derived category; neither finite evaluation nor constructibility is used. Identity
isomorphisms give the usual unitor, and empty schemes and zero complexes are included.
-/
theorem completedDirectImageTargetIso
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T Y Z : Scheme.{u}} (p : T ⟶ Z) (e : Y ≅ Z) :
    Nonempty (push (completed l E) (p ≫ e.inv) ≅
      push (completed l E) p ⋙
        AlgebraicGeometry.ProEtale.inverseImageIntegralDerived l E e.hom) := by
  let g := e.inv
  let ε := pullbackIdentityModuleCounit l E g
  let εi : inverseImageIntegralModules l E (inv g) ⋙ inverseImageIntegralModules l E g ≅
      𝟭 (integralTowerModules l E Z) := by
    simpa only [IsIso.inv_inv] using pullbackIdentityModuleCounit l E (inv g)
  let eqv := CategoryTheory.Equivalence.mk (inverseImageIntegralModules l E g)
    (inverseImageIntegralModules l E (inv g)) ε.symm εi
  obtain ⟨a⟩ := inverseImageAdjunction l E g
  let Q : integralTowerModules l E Z ⥤ integralTowerModules l E Y :=
    proEtaleRingModuleDirectImage g ((completed l E).ring Y)
      ((completed l E).ring Z) ((completed l E).pull g)
  let d : Q ≅ inverseImageIntegralModules l E (inv g) :=
    a.rightAdjointUniq eqv.toAdjunction
  let δ₀ := @Functor.rightDerivedFunctorNatIso
    (integralTowerModules l E Z) (integralTowerModules l E Y)
    _ _ _ _ _ _ _ Q (inverseImageIntegralModules l E (inv g))
    (proEtaleRingModuleDirectImage_additive g ((completed l E).ring Y)
      ((completed l E).ring Z) ((completed l E).pull g))
    (inverseImageAdd l E (inv g)) d
  let δ : push (completed l E) g ≅ inverseImageIntegralDerived l E e.hom :=
    δ₀ ≪≫
      (inverseImageIntegralModules l E (inv g)).rightDerivedFunctorIsoMapDerivedCategory ≪≫
      eqToIso (by
        change (inverseImageIntegralModules l E (inv e.inv)).mapDerivedCategory =
          (inverseImageIntegralModules l E e.hom).mapDerivedCategory
        simp only [IsIso.inv_eq_of_hom_inv_id e.inv_hom_id])
  exact ⟨(geometricPushComposition (completed l E) p e.inv
      (completedPull_comp l E p e.inv)).symm ≪≫
    Functor.isoWhiskerLeft (push (completed l E) p) δ⟩

end WeilConjectures
