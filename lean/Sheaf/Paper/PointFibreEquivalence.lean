/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q60
-/
module

public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.PointFiniteCohomologyComplexes
public import Sheaf.Paper.PointFgCompleteComplexes
public import Sheaf.Paper.PointFdComplexes
public import Sheaf.Paper.PointFdQbarCategory
import Sheaf.Paper.PointQbarFibreShiftDescent
import Sheaf.Paper.PointRationalSectionsHom
import Sheaf.Paper.PointRationalSectionsLattice
import Sheaf.Paper.PointRationalFibreExact
import Mathlib.RingTheory.Localization.BaseChange
import Sheaf.Paper.PointIntegralSectionsConservative
import Sheaf.Paper.PointIntegralPerfectRealization
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.Paper.ProEtaleConstantModuleConstructibility
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary
import WeilConjectures.ConstructibleSheaf.SpecializationCriterion
import WeilConjectures.CategoryTheory.FilteredTwoColimitTransport
import Mathlib.CategoryTheory.Localization.Adjunction
import Mathlib.CategoryTheory.Adjunction.Restrict
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Sheaf.Paper.FiniteRingConstructibleSheafOrigin
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Sheaf.Paper.SfIntegralConstructibleTriangulated

/-!
# Exact equivalences given by the four geometric-point fibre functors

Source: Weil blueprint, `def-weil-finite-coefficient-point`, order 1509;
main-20261015, sec-six-functors-basics/sk-def-sf-admissible, order 1868
(blueprint: lem-weil-point-fibre-equivalence).

For the three full-subcategory targets, shifts and distinguished triangles are
expressed after their fully faithful inclusions into the ambient derived categories.
This is precisely the inherited shift and distinguished-triangle convention.
The fourth target uses its recorded common-stage distinguished-triangle predicate.
-/

@[expose] public section

set_option autoImplicit false
set_option cleanup.letToHave false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TensorProduct
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

section ExactAdjunction

variable {C : Type*} {C' : Type*} [Category C] [Category C'] [Abelian C] [Abelian C']
  [HasDerivedCategory C] [HasDerivedCategory C'] (L : C ⥤ C') (R : C' ⥤ C)
  [L.Additive] [R.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]

@[instance_reducible] private noncomputable def pointExactDerivedSquare :
    CatCommSq (L.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q DerivedCategory.Q
      L.mapDerivedCategory := ⟨L.mapDerivedCategoryFactors.symm⟩

attribute [local instance] pointExactDerivedSquare

private noncomputable def pointExactDerivedAdjunction (adj : L ⊣ R) :
    L.mapDerivedCategory ⊣ R.mapDerivedCategory :=
  (adj.mapHomologicalComplex (.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso C' (.up ℤ))
    L.mapDerivedCategory R.mapDerivedCategory

private theorem pointExactDerivedUnit_isIso (adj : L ⊣ R)
    [∀ M, IsIso (adj.unit.app M)] (K : DerivedCategory C) :
    IsIso ((pointExactDerivedAdjunction L R adj).unit.app K) := by
  let e := DerivedCategory.Q.objObjPreimageIso K
  rw [← NatTrans.isIso_app_iff_of_iso _ e]
  dsimp only [pointExactDerivedAdjunction]
  rw [Adjunction.localization_unit_app]
  have : IsIso ((adj.mapHomologicalComplex (.up ℤ)).unit.app
      (DerivedCategory.Q.objPreimage K)) :=
      by
        have (i : ℤ) : IsIso (((adj.mapHomologicalComplex (.up ℤ)).unit.app
            (DerivedCategory.Q.objPreimage K)).f i) := by
          change IsIso (adj.unit.app _)
          infer_instance
        exact HomologicalComplex.Hom.isIso_of_components _
  infer_instance

private theorem pointExactDerivedCounit_isIso (adj : L ⊣ R) (K : DerivedCategory C')
    (h : ∀ i : ℤ, IsIso (adj.counit.app ((DerivedCategory.homologyFunctor C' i).obj K))) :
    IsIso ((pointExactDerivedAdjunction L R adj).counit.app K) := by
  let P := DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Q.obj P ≅ K := DerivedCategory.Q.objObjPreimageIso K
  rw [← NatTrans.isIso_app_iff_of_iso _ e]
  dsimp only [pointExactDerivedAdjunction]
  rw [Adjunction.localization_counit_app]
  have hP : QuasiIso ((adj.mapHomologicalComplex (.up ℤ)).counit.app P) := by
    rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    let ei : P.homology i ≅ (DerivedCategory.homologyFunctor C' i).obj K :=
      ((DerivedCategory.homologyFunctorFactors C' i).app P).symm ≪≫
        (DerivedCategory.homologyFunctor C' i).mapIso e
    have : IsIso (adj.counit.app (P.sc i).homology) :=
      (NatTrans.isIso_app_iff_of_iso adj.counit ei).mpr (h i)
    change IsIso (ShortComplex.homologyMap ((P.sc i).mapNatTrans adj.counit))
    rw [ShortComplex.homologyMap_mapNatTrans]
    infer_instance
  infer_instance

end ExactAdjunction

private theorem pointRestrictedRight_equivalence
    {C C' : Type*} [Category C] [Category C'] {L : C ⥤ C'} {R : C' ⥤ C}
    (adj : L ⊣ R) (P : ObjectProperty C') (Q : ObjectProperty C)
    (F : P.FullSubcategory ⥤ Q.FullSubcategory) (e : F ⋙ Q.ι ≅ P.ι ⋙ R)
    (hL : ∀ M : Q.FullSubcategory, P (L.obj M.obj))
    (hu : ∀ M : Q.FullSubcategory, IsIso (adj.unit.app M.obj))
    (hc : ∀ K : P.FullSubcategory, IsIso (adj.counit.app K.obj)) : F.IsEquivalence := by
  let G := P.lift (Q.ι ⋙ L) hL
  let a : G ⊣ F := adj.restrictFullyFaithful Q.fullyFaithfulι P.fullyFaithfulι
    (Iso.refl _) e.symm
  have (M : Q.FullSubcategory) : IsIso (a.unit.app M) := by
    rw [← isIso_iff_of_reflects_iso _ Q.ι]
    dsimp only [a]
    rw [adj.map_restrictFullyFaithful_unit_app]
    have : IsIso (adj.unit.app (Q.ι.obj M)) := hu M
    infer_instance
  have (K : P.FullSubcategory) : IsIso (a.counit.app K) := by
    rw [← isIso_iff_of_reflects_iso _ P.ι]
    dsimp only [a]
    rw [adj.map_restrictFullyFaithful_counit_app]
    have : IsIso (adj.counit.app (P.ι.obj K)) := hc K
    infer_instance
  exact a.toEquivalence.isEquivalence_inverse

section FiniteReconstruction

variable (k B : Type u) [Field k] [IsAlgClosed k] [CommRing B] [Finite B]

omit [IsAlgClosed k] [Finite B] in
private theorem pointFiniteSheafifyProEt :
    HasSheafify (ProEt.topology (Spec (.of k)))
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) := inferInstance

attribute [local instance] pointFiniteSheafifyProEt

omit [IsAlgClosed k] [Finite B] in
private theorem pointFiniteSheafifyEtale :
    HasSheafify (Spec (.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) := inferInstance

attribute [local instance] pointFiniteSheafifyEtale

private noncomputable def pointFiniteConstant :
    ModuleCat.{u + 1} (ULift.{u + 1, u} B) ⥤
      proEtaleRingModules (Spec (.of k)) (proEtaleConstantRing (Spec (.of k)) B) :=
  constantSheaf (ProEt.topology (Spec (.of k)))
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) ⋙
    (proEtaleModuleEncoding (Spec (.of k)) B).inverse

private noncomputable def pointFiniteConstantAdjunction :
    pointFiniteConstant k B ⊣ pointFiniteSections k B :=
  ((constantSheafAdj (ProEt.topology (Spec (.of k)))
    (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) (ProEt.isTerminalMkId _)).comp
      (proEtaleModuleEncoding (Spec (.of k)) B).symm.toAdjunction)

omit [Finite B] in
private theorem pointFiniteConstant_full : (pointFiniteConstant k B).Full := by
  let e := AlgebraicGeometry.Etale.constantSheafEquivalenceOfIsSepClosed
    (ULift.{u + 1, u} B) (k := k)
  have : (constantSheaf (Spec (.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B))).Full :=
    inferInstanceAs e.functor.Full
  have : (constantSheaf (ProEt.topology (Spec (.of k)))
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B))).Full :=
    Functor.Full.of_iso (AlgebraicGeometry.ProEtale.comparisonUpperStarConstantSheafIso
      (ULift.{u + 1, u} B) (Spec (.of k)))
  exact inferInstanceAs (constantSheaf (ProEt.topology (Spec (.of k)))
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) ⋙
    (proEtaleModuleEncoding (Spec (.of k)) B).inverse).Full

attribute [local instance] pointFiniteConstant_full

omit [Finite B] in
private theorem pointFiniteConstant_faithful :
    (pointFiniteConstant k B).Faithful := by
  let e := AlgebraicGeometry.Etale.constantSheafEquivalenceOfIsSepClosed
    (ULift.{u + 1, u} B) (k := k)
  have : (constantSheaf (Spec (.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B))).Faithful :=
    inferInstanceAs e.functor.Faithful
  have : (constantSheaf (ProEt.topology (Spec (.of k)))
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B))).Faithful :=
    Functor.Faithful.of_iso (AlgebraicGeometry.ProEtale.comparisonUpperStarConstantSheafIso
      (ULift.{u + 1, u} B) (Spec (.of k)))
  exact inferInstanceAs (constantSheaf (ProEt.topology (Spec (.of k)))
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) ⋙
    (proEtaleModuleEncoding (Spec (.of k)) B).inverse).Faithful

attribute [local instance] pointFiniteConstant_faithful

omit [IsAlgClosed k] [Finite B] in
private theorem pointFiniteConstant_limits :
    PreservesFiniteLimits (pointFiniteConstant k B) := by
  dsimp only [pointFiniteConstant]
  infer_instance

attribute [local instance] pointFiniteConstant_limits

omit [IsAlgClosed k] [Finite B] in
private theorem pointFiniteConstant_additive :
    (pointFiniteConstant k B).Additive :=
  Functor.additive_of_preserves_binary_products _

attribute [local instance] pointFiniteConstant_additive

omit [IsAlgClosed k] [Finite B] in
private theorem pointFiniteConstant_colimits :
    PreservesFiniteColimits (pointFiniteConstant k B) := by
  let : PreservesColimitsOfSize.{0, 0} (pointFiniteConstant k B) :=
    (pointFiniteConstantAdjunction k B).leftAdjoint_preservesColimits
  infer_instance

attribute [local instance] pointFiniteConstant_colimits

private theorem pointFiniteConstant_counit (F :
    proEtaleRingModules (Spec (.of k)) (proEtaleConstantRing (Spec (.of k)) B))
    (hF : IsConstructibleProEtaleModuleSheaf (Spec (.of k)) B F) :
    IsIso ((pointFiniteConstantAdjunction k B).counit.app F) := by
  let E := proEtaleModuleEncoding (Spec (.of k)) B
  have h := (proEtaleModuleRestriction_constructible_iff (Spec (.of k)) B F).mp hF
  obtain ⟨G, _, ⟨eG⟩⟩ :=
    AlgebraicGeometry.ProEtale.exists_isConstructibleSheaf_iso_comparisonUpperStar_obj
      (ULift.{u + 1, u} B) h
  let A := AlgebraicGeometry.Etale.constantSheafEquivalenceOfIsSepClosed
    (ULift.{u + 1, u} B) (k := k)
  let ν := AlgebraicGeometry.ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) (Spec (.of k))
  let e : (constantSheaf (ProEt.topology (Spec (.of k)))
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B))).obj (A.inverse.obj G) ≅ E.functor.obj F :=
    ((AlgebraicGeometry.ProEtale.comparisonUpperStarConstantSheafIso
      (ULift.{u + 1, u} B) (Spec (.of k))).app (A.inverse.obj G)).symm ≪≫
        ν.mapIso (A.counitIso.app G) ≪≫ eG
  apply (pointFiniteConstantAdjunction k B).isIso_counit_app_iff_mem_essImage.mpr
  exact ⟨A.inverse.obj G, ⟨E.inverse.mapIso e ≪≫ E.unitIso.symm.app F⟩⟩

omit [IsAlgClosed k] in
private theorem pointFiniteConstant_constructible
    (M : ModuleCat.{u + 1} (ULift.{u + 1, u} B)) [Finite M] :
    IsConstructibleProEtaleModuleSheaf (Spec (.of k)) B
      ((pointFiniteConstant k B).obj M) := by
  let E := proEtaleModuleEncoding (Spec (.of k)) B
  apply (proEtaleModuleRestriction_constructible_iff (Spec (.of k)) B _).mpr
  have : Module.Finite (ULift.{u + 1, u} B) M := Module.Finite.of_finite
  have := Scheme.isConstructibleSheaf_constantSheaf
    (X := Spec (.of k)) M
  let e : (AlgebraicGeometry.ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) (Spec (.of k))).obj
      ((constantSheaf (Spec (.of k)).smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1, u} B))).obj M) ≅
        E.functor.obj ((pointFiniteConstant k B).obj M) :=
    (AlgebraicGeometry.ProEtale.comparisonUpperStarConstantSheafIso
      (ULift.{u + 1, u} B) (Spec (.of k))).app M ≪≫ (E.counitIso.app _).symm
  exact AlgebraicGeometry.ProEtale.isConstructible_of_iso e
    (AlgebraicGeometry.ProEtale.isConstructible_comparisonUpperStar_obj _)

omit [IsAlgClosed k] in
private theorem pointConstructible_of_iso
    {F G : proEtaleRingModules (Spec (.of k)) (proEtaleConstantRing (Spec (.of k)) B)}
    (e : F ≅ G) (hF : IsConstructibleProEtaleModuleSheaf (Spec (.of k)) B F) :
    IsConstructibleProEtaleModuleSheaf (Spec (.of k)) B G := by
  apply (proEtaleModuleRestriction_constructible_iff (Spec (.of k)) B G).mpr
  exact AlgebraicGeometry.ProEtale.isConstructible_of_iso
    ((proEtaleModuleRestriction (Spec (.of k)) B).mapIso e)
    ((proEtaleModuleRestriction_constructible_iff (Spec (.of k)) B F).mp hF)

end FiniteReconstruction

attribute [local instance] pointFiniteSheafifyProEt
attribute [local instance] pointFiniteSheafifyEtale
attribute [local instance] pointFiniteConstant_full
attribute [local instance] pointFiniteConstant_faithful
attribute [local instance] pointFiniteConstant_limits
attribute [local instance] pointFiniteConstant_additive
attribute [local instance] pointFiniteConstant_colimits


/-- Expose the existing inherited torsion-source triangulation, without choosing a
new structure. Source: blueprint order 1454, bounded constructible subcategory;
order 1509, torsion fibre (blueprint: lem-weil-point-fibre-equivalence). -/
noncomputable instance pointFibreTorsionSourceTriangulated
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) (hn : 1 ≤ n) (Y : Scheme.{u}) :
    ObjectProperty.IsTriangulated (intrinsicFiniteTorsionConstructible l E n hn Y) :=
  letI := Padic.finite_coefficientExtensionRing l E n hn
  (proEtale_bounded_constructible_isTriangulated Y
    (Padic.coefficientExtensionRing l E n)).2

/-- Expose the existing strict fullness of the torsion source.
Source: blueprint order 1454, full triangulated subcategory; order 1509, torsion fibre
(blueprint: lem-weil-point-fibre-equivalence). -/
noncomputable instance pointFibreTorsionSourceIsoClosed
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) (hn : 1 ≤ n) (Y : Scheme.{u}) :
    ObjectProperty.IsClosedUnderIsomorphisms
      (intrinsicFiniteTorsionConstructible l E n hn Y) :=
  letI := Padic.finite_coefficientExtensionRing l E n hn
  (proEtale_bounded_constructible_isTriangulated Y
    (Padic.coefficientExtensionRing l E n)).1

private theorem pointFiniteFibre_equivalence
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) (hn : 1 ≤ n) : (pointFiniteFibre D l hl E n hn).IsEquivalence := by
  classical
  let B := Padic.coefficientExtensionRing l E n
  let : Finite B := Padic.finite_coefficientExtensionRing l E n hn
  let : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  let L := pointFiniteConstant D.k B
  let R := pointFiniteSections D.k B
  let adj := pointFiniteConstantAdjunction D.k B
  apply pointRestrictedRight_equivalence (pointExactDerivedAdjunction L R adj)
    (intrinsicFiniteTorsionConstructible l E n hn (Spec (.of D.k)))
    (DerivedCategory.pointFiniteCohomology (ULift.{u + 1, u} B)) _ (Iso.refl _)
  · intro M
    refine ⟨?_, fun i ↦ ?_⟩
    · obtain ⟨s, hs⟩ := M.property.1
      apply s.finite_toSet.subset
      intro i hi
      by_contra hin
      exact hi (L.isZero_homologyFunctor_mapDerivedCategory_obj (hs i hin))
    · have := M.property.2 i
      exact pointConstructible_of_iso D.k B
        ((L.mapDerivedCategoryHomologyFunctorIso i).app M.obj)
        (pointFiniteConstant_constructible D.k B _)
  · intro M
    have (N : ModuleCat.{u + 1} (ULift.{u + 1, u} B)) :
        IsIso (adj.unit.app N) :=
      inferInstance
    exact pointExactDerivedUnit_isIso L R adj M.obj
  · intro K
    apply pointExactDerivedCounit_isIso L R adj K.obj
    intro i
    exact pointFiniteConstant_counit D.k B _ (K.property.2 i)

private theorem pointIntegralFibre_equivalence
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    (pointIntegralFibre D l hl E).IsEquivalence := by
  classical
  let : HasDerivedCategory.{u + 1}
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  let P := sfIntegralConstructible l E (Spec (.of D.k))
  let F := pointIntegralFibre D l hl E
  let G := P.ι ⋙ pointFibreIntegralAmbient D l E
  have hc (K : P.FullSubcategory) (hK : IsZero (G.obj K)) : IsZero K := by
    have h := pointIntegralSections_conservative D l hl E
      (fun n hn ↦ pointFiniteFibre_equivalence D l hl E n hn) K hK
    exact IsZero.of_full_of_faithful_of_isZero P.ι K h
  have hG : G.ReflectsIsomorphisms := by
    constructor
    intro X Y f hf
    obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
    let T := Triangle.mk f g h
    have hz : IsZero (G.obj Z) :=
      Triangle.isZero₃_of_isIso₁ (G.mapTriangle.obj T) (G.map_distinguished T hT) hf
    exact (Triangle.isZero₃_iff_isIso₁ T hT).mp (hc Z hz)
  have hF : F.ReflectsIsomorphisms := by
    constructor
    intro X Y f hf
    have : IsIso (G.map f) := by
      change IsIso ((DerivedCategory.pointFgComplete _ _).ι.map (F.map f))
      infer_instance
    exact isIso_of_reflects_iso f G
  obtain ⟨L, a, hu⟩ := pointIntegralPerfectRealization D l hl E
  have : ∀ M, IsIso (a.unit.app M) := hu
  have : L.Full := a.full_L_of_isSplitEpi_unit_app
  have : L.Faithful := a.faithful_L_of_mono_unit_app
  have : ∀ K, IsIso (a.counit.app K) := by
    intro K
    apply isIso_of_reflects_iso _ F
  exact a.toEquivalence.isEquivalence_inverse


private theorem pointTensor_eq_tmul {R : Type*} [CommRing R] (p : R)
    {M : Type*} [AddCommGroup M] [Module R M]
    (t : Localization.Away p ⊗[R] M) : ∃ a m, t = a ⊗ₜ[R] m := by
  let e := LocalizedModule.equivTensorProduct (Submonoid.powers p) M
  obtain ⟨y, rfl⟩ := e.surjective t
  induction y using LocalizedModule.induction_on with
  | _ m q =>
    exact ⟨Localization.mk 1 q, m,
      LocalizedModule.equivTensorProduct_apply_mk (Submonoid.powers p) m q⟩

private theorem pointFullSubcategory_heq
    {C : Type*} [Category C] {P : ObjectProperty C}
    {X Y X' Y' : P.FullSubcategory} (hX : X = X') (hY : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f.hom g.hom) : HEq f g := by
  subst X'
  subst Y'
  exact heq_of_eq (ObjectProperty.hom_ext P (eq_of_heq h))

private theorem pointCopyObj_map
    {C : Type*} [Category C] {D : Type*} [Category D] (F : C ⥤ D)
    (φ : C → D) (hφ : ∀ X, F.obj X = φ X) {X Y : C} (f : X ⟶ Y)
    (g : φ X ⟶ φ Y) (h : HEq (F.map f) g) :
    (F.copyObj φ (fun X ↦ eqToIso (hφ X))).map f = g := by
  have hh := (conj_eqToHom_iff_heq _ _ (hφ X) (hφ Y)).mpr h
  dsimp only [Functor.copyObj, eqToIso]
  rw [hh]
  simp [Category.assoc]

private theorem pointRationalFibre_equivalence
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    (pointRationalFibre D l hl E).IsEquivalence := by
  classical
  let F := pointRationalFibre D l hl E
  let φ (X : sfRationalConstructibleCategory l E (Spec (.of D.k))) :=
    (pointIntegralRationalFibre D l hl E).obj X.obj
  have ho : ∀ X, F.obj X = φ X :=
    (pointRationalFibre_existsUnique D l hl E).exists.choose_spec.1
  let G := F.copyObj φ (fun X ↦ eqToIso (ho X))
  have hi := pointIntegralFibre_equivalence D l hl E
  choose e he using pointRationalSectionsHom D l hl E hi
  have hm (X Y : sfRationalConstructibleCategory l E (Spec (.of D.k)))
      (f : X ⟶ Y) : G.map f = e X.obj Y.obj f := by
    obtain ⟨a, g, rfl⟩ := pointTensor_eq_tmul _ f
    apply pointCopyObj_map F φ ho
    apply pointFullSubcategory_heq (ho X) (ho Y)
    exact ((pointRationalFibre_existsUnique D l hl E).exists.choose_spec.2
      X.obj Y.obj g a).trans (heq_of_eq (he X.obj Y.obj a g).symm)
  have : G.Full := by
    constructor
    intro X Y f
    obtain ⟨g, rfl⟩ := (e X.obj Y.obj).surjective f
    exact ⟨g, hm X Y g⟩
  have : G.Faithful := by
    constructor
    intro X Y f g hfg
    apply (e X.obj Y.obj).injective
    simpa only [hm] using hfg
  have : G.EssSurj := by
    constructor
    intro V
    obtain ⟨K, hK⟩ := pointRationalSectionsLattice D l hl E hi V
    exact ⟨⟨K⟩, hK⟩
  have : G.IsEquivalence := ⟨inferInstance, inferInstance, inferInstance⟩
  exact Functor.isEquivalence_of_iso (F.isoCopyObj φ (fun X ↦ eqToIso (ho X))).symm


private theorem pointCommonStage_equivalence
    {I : Type*} [Preorder I] [IsDirectedOrder I] {C : I → Type*}
    [∀ i, Category (C i)] {V : Type*} [Category V]
    (S : StageSystem C) (Φ : ∀ i, C i ⥤ V)
    (β : ∀ {i j} (h : i ≤ j), S.T h ⋙ Φ j ≅ Φ i)
    (hc : (CategoryCocone.mk S.T Φ β).IsFilteredTwoColimit)
    (F : S.PairCategory ⥤ V) (ho : ∀ X, F.obj X = (Φ X.stage).obj X.obj)
    (hm : ∀ (X Y : S.PairCategory) (i : I) (hx : X.stage ≤ i) (hy : Y.stage ≤ i)
      (f : X.toStage hx ⟶ Y.toStage hy),
      HEq (F.map (StageSystem.PairCategory.mkHom i hx hy f))
        ((β hx).inv.app X.obj ≫ (Φ i).map f ≫ (β hy).hom.app Y.obj)) :
    F.IsEquivalence := by
  let G := F.copyObj (fun X ↦ (Φ X.stage).obj X.obj) (fun X ↦ eqToIso (ho X))
  have hG (X Y : S.PairCategory) (i : I) (hx : X.stage ≤ i) (hy : Y.stage ≤ i)
      (f : X.toStage hx ⟶ Y.toStage hy) :
      G.map (StageSystem.PairCategory.mkHom i hx hy f) =
        (β hx).inv.app X.obj ≫ (Φ i).map f ≫ (β hy).hom.app Y.obj := by
    have h := (conj_eqToHom_iff_heq _ _ (ho X) (ho Y)).mpr (hm X Y i hx hy f)
    dsimp only [G, Functor.copyObj, eqToIso]
    rw [h]
    simp [Category.assoc]
  have : G.Full := by
    constructor
    intro X Y f
    obtain ⟨i, hx, hy, g, hg⟩ := hc.homSurj X.stage Y.stage X.obj Y.obj f
    exact ⟨StageSystem.PairCategory.mkHom i hx hy g, (hG X Y i hx hy g).trans hg.symm⟩
  have : G.Faithful := by
    constructor
    intro X Y f g hfg
    obtain ⟨i, -, hx, hy, hx', hy', u, v, rfl, rfl⟩ :=
      StageSystem.PairCategory.exists_common_stage f g X.stage
    rw [hG, hG] at hfg
    have huv : (Φ i).map u = (Φ i).map v :=
      (cancel_epi ((β hx).inv.app X.obj)).mp
        ((cancel_mono ((β hy).hom.app Y.obj)).mp
          (by simpa only [Category.assoc] using hfg))
    obtain ⟨j, hij, hj⟩ := hc.homInj i _ _ u v huv
    exact (StageSystem.PairCategory.mkHom_eq_mkHom_iff u v).mpr ⟨j, hij, hj⟩
  have : G.EssSurj := by
    constructor
    intro Z
    obtain ⟨i, x, e⟩ := hc.essSurjObj Z
    exact ⟨⟨i, x⟩, e⟩
  have : G.IsEquivalence := ⟨inferInstance, inferInstance, inferInstance⟩
  exact Functor.isEquivalence_of_iso
    (F.isoCopyObj (fun X ↦ (Φ X.stage).obj X.obj) (fun X ↦ eqToIso (ho X))).symm

private noncomputable def pointFdScalarIdentity (K : Type u) [Field K] :
    DerivedCategory.pointFdScalarExtension (RingHom.id K) ≅
      𝟭 (DerivedCategory.pointFiniteDimensional K).FullSubcategory :=
  ((DerivedCategory.pointFiniteDimensional K).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (DerivedCategory.pointFiniteDimensional K).ι
      (DerivedCategory.fieldScalarUnit K))

private theorem pointFdScalarEquivalence {K L : Type u} [Field K] [Field L]
    (e : K ≃+* L) : (DerivedCategory.pointFdScalarExtension e.toRingHom).IsEquivalence := by
  let F := DerivedCategory.pointFdScalarExtension e.toRingHom
  let G := DerivedCategory.pointFdScalarExtension e.symm.toRingHom
  let α : F ⋙ G ≅ 𝟭 _ := pointFibreFdTensorTower _ _ ≪≫
    eqToIso (congrArg DerivedCategory.pointFdScalarExtension
      (show e.symm.toRingHom.comp e.toRingHom = RingHom.id K by ext; simp)) ≪≫
        pointFdScalarIdentity K
  let β : G ⋙ F ≅ 𝟭 _ := pointFibreFdTensorTower _ _ ≪≫
    eqToIso (congrArg DerivedCategory.pointFdScalarExtension
      (show e.toRingHom.comp e.symm.toRingHom = RingHom.id L by ext; simp)) ≪≫
        pointFdScalarIdentity L
  exact (CategoryTheory.Equivalence.mk F G α.symm β).isEquivalence_functor


private theorem pointMapTriple_eq
    {C V : Type*} [Category C] [Category V] (F : C ⥤ V)
    {X₀ X₁ X₂ X₃ : C} {A B : V} (a : A ⟶ F.obj X₀)
    (b : X₀ ⟶ X₁) (c : X₁ ⟶ X₂) (d : X₂ ⟶ X₃) (e : F.obj X₃ ⟶ B) :
    a ≫ F.map (b ≫ c ≫ d) ≫ e = (a ≫ F.map b) ≫ F.map c ≫ (F.map d ≫ e) := by
  simp only [Functor.map_comp, Category.assoc]

private theorem pointTransportRepresentative_eq
    {I : Type*} [Preorder I] {C C' : I → Type*}
    [∀ i, Category (C i)] [∀ i, Category (C' i)] {V : Type*} [Category V]
    (c : CategoryCocone C' V) (T : ∀ {i j : I}, i ≤ j → (C i ⥤ C j))
    (F : ∀ i, C i ⥤ C' i)
    (β : ∀ {i j : I} (h : i ≤ j), T h ⋙ F j ≅ F i ⋙ c.T h)
    {i j k : I} (hx : i ≤ k) (hy : j ≤ k) (X : C i) (Y : C j)
    (f : (T hx).obj X ⟶ (T hy).obj Y) :
    ((c.transport T F β).iso hx).inv.app X ≫
        ((c.transport T F β).Φ k).map f ≫ ((c.transport T F β).iso hy).hom.app Y =
      ((c.iso hx).inv.app ((F i).obj X) ≫ (c.Φ k).map ((β hx).inv.app X)) ≫
        (c.Φ k).map ((F k).map f) ≫
        ((c.Φ k).map ((β hy).hom.app Y) ≫ (c.iso hy).hom.app ((F j).obj Y)) := by
  rfl

attribute [local irreducible] pointStageFibre pointStageFibreScalarIso pointQbarFibre
  Functor.mapDerivedCategory DerivedCategory.pointFdQbarStageComp

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem pointQbarRepresentative_eq
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (X Y : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
    (i : Padic.FiniteCoefficientFields l Ω) (hx : X.stage ≤ i) (hy : Y.stage ≤ i)
    (f : X.toStage hx ⟶ Y.toStage hy) :
    pointQbarFibreRepresentative D l hl Ω X Y i hx hy f =
      (((DerivedCategory.pointFdQbarStageComp l Ω hx).inv.app _ ≫
        (DerivedCategory.pointFdQbarStage l Ω i).map
          ((pointStageFibreScalarIso D l hl Ω _ _ hx).inv.app X.obj)) ≫
        (DerivedCategory.pointFdQbarStage l Ω i).map ((pointStageFibre D l hl Ω i).map f) ≫
        ((DerivedCategory.pointFdQbarStage l Ω i).map
          ((pointStageFibreScalarIso D l hl Ω _ _ hy).hom.app Y.obj) ≫
        (DerivedCategory.pointFdQbarStageComp l Ω hy).hom.app _)) := by
  unfold pointQbarFibreRepresentative
  exact pointMapTriple_eq (DerivedCategory.pointFdQbarStage l Ω i)
    ((DerivedCategory.pointFdQbarStageComp l Ω hx).inv.app _)
    ((pointStageFibreScalarIso D l hl Ω _ _ hx).inv.app X.obj)
    ((pointStageFibre D l hl Ω i).map f)
    ((pointStageFibreScalarIso D l hl Ω _ _ hy).hom.app Y.obj)
    ((DerivedCategory.pointFdQbarStageComp l Ω hy).hom.app _)

private noncomputable def pointQbarCocone
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω] :
    CategoryCocone (GeneralAlgebraicallyClosedCoefficients.Stage l Ω (Spec (.of D.k)))
      (DerivedCategory.PointFdQbar l Ω) :=
  (DerivedCategory.pointFdQbarCocone l Ω).transport
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω (Spec (.of D.k))).T
    (pointStageFibre D l hl Ω) (fun {_ _} h ↦ pointStageFibreScalarIso D l hl Ω _ _ h)

private theorem pointQbarCocone_colimit
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (hs : ∀ i, (pointStageFibre D l hl Ω i).IsEquivalence) :
    (pointQbarCocone D l hl Ω).IsFilteredTwoColimit := by
  have : ∀ i, (pointStageFibre D l hl Ω i).IsEquivalence := hs
  exact (DerivedCategory.pointFdQbarCocone_isFilteredTwoColimit l Ω).transport

private theorem pointQbarCocone_obj
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (X : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k))) :
    ((pointQbarCocone D l hl Ω).Φ X.stage).obj X.obj =
      pointQbarFibreObj D l hl Ω X := rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem pointQbarCocone_map
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (X Y : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
    (i : Padic.FiniteCoefficientFields l Ω) (hx : X.stage ≤ i) (hy : Y.stage ≤ i)
    (f : X.toStage hx ⟶ Y.toStage hy) :
    HEq (pointQbarFibreRepresentative D l hl Ω X Y i hx hy f)
      (((pointQbarCocone D l hl Ω).iso hx).inv.app X.obj ≫
        ((pointQbarCocone D l hl Ω).Φ i).map f ≫
        ((pointQbarCocone D l hl Ω).iso hy).hom.app Y.obj) := by
  have ht := pointTransportRepresentative_eq (DerivedCategory.pointFdQbarCocone l Ω)
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω (Spec (.of D.k))).T
    (pointStageFibre D l hl Ω)
    (fun {_ _} h ↦ pointStageFibreScalarIso D l hl Ω _ _ h) hx hy X.obj Y.obj f
  have hr := pointQbarRepresentative_eq D l hl Ω X Y i hx hy f
  exact (heq_of_eq hr).trans (heq_of_eq ht.symm)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem pointQbarFormula_equivalence
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (hstage : ∀ i, (pointStageFibre D l hl Ω i).IsEquivalence)
    (F : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)) ⥤
      DerivedCategory.PointFdQbar l Ω)
    (ho : ∀ X, F.obj X = pointQbarFibreObj D l hl Ω X)
    (hm : ∀ X Y i (hx : X.stage ≤ i) (hy : Y.stage ≤ i)
      (f : X.toStage hx ⟶ Y.toStage hy),
      HEq (F.map (StageSystem.PairCategory.mkHom i hx hy f))
        (pointQbarFibreRepresentative D l hl Ω X Y i hx hy f)) :
    F.IsEquivalence := by
  apply pointCommonStage_equivalence
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω (Spec (.of D.k)))
    (pointQbarCocone D l hl Ω).Φ (pointQbarCocone D l hl Ω).iso
    (pointQbarCocone_colimit D l hl Ω hstage) F
    (fun X ↦ (ho X).trans (pointQbarCocone_obj D l hl Ω X).symm)
  intro X Y i hx hy f
  exact (hm X Y i hx hy f).trans (pointQbarCocone_map D l hl Ω X Y i hx hy f)


private theorem pointQbarFibre_equivalence
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (hstage : ∀ i, (pointStageFibre D l hl Ω i).IsEquivalence) :
    (pointQbarFibre D l hl Ω).IsEquivalence := by
  unfold pointQbarFibre
  exact pointQbarFormula_equivalence D l hl Ω hstage _
    (pointQbarFibre_existsUnique D l hl Ω).exists.choose_spec.1
    (pointQbarFibre_existsUnique D l hl Ω).exists.choose_spec.2


/-- The four specified geometric-point fibres are exact equivalences.
Source: blueprint order 1509; main-20261015 order 1868.
(blueprint: lem-weil-point-fibre-equivalence).

Proof: for finite coefficients the constant-module/sections adjunction descends
termwise through derived localization. Finite constructible origin and the
algebraically closed etale-point equivalence identify the counit on constructible
cohomology; the constant functor is fully faithful, so the unit is invertible.
Restriction therefore gives the specified finite fibre equivalence.

Integral sections are conservative: reduction commutes with sections, the finite
fibres detect each zero reduction, and the completeness triangle detects the
original zero object. The completed perfect-realization adjunction has invertible
unit. The triangle identity and reflection of isomorphisms make its counit
invertible as well.

The normalized rational Hom comparison identifies every morphism of the copied
rational fibre: each localization tensor is a single pure tensor. The comparison
is an additive isomorphism, giving full faithfulness. The integral lattice theorem
gives essential surjectivity. Finite-stage fibres are rational fibres followed by
scalar extension along the coefficient ring equivalence. Transport the target
filtered two-colimit cocone along them. Its Hom-surjectivity, eventual
Hom-injectivity and object-surjectivity give the common-stage equivalence, with
exactly the representative formula defining the specified Qbar fibre.

Finite and integral exactness are inherited from termwise derived sections.
Rational exactness descends through the actual raw scalar localization, using its
coefficient-one factorization isomorphism and shift universal property. For Qbar,
use the common-stage shift comparison and finite-stage exactness; every source
distinguished triangle is isomorphic to a stage image. Applying the fibre and
realization to that triangle isomorphism transports the stage witness, including
its last arrow, to the required target distinguished-triangle predicate. -/
theorem point_fibre_equivalence
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (E : Padic.FiniteCoefficientFields l Ω) (n : ℕ) (hn : 1 ≤ n) :
    (pointFiniteFibre D l hl E.val n hn).IsEquivalence ∧
    (pointIntegralFibre D l hl E.val).IsEquivalence ∧
    (pointRationalFibre D l hl E.val).IsEquivalence ∧
    (pointQbarFibre D l hl Ω).IsEquivalence ∧
    (∃ c : (pointFiniteFibre D l hl E.val n hn ⋙
        (DerivedCategory.pointFiniteCohomology
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E.val n))).ι).CommShift ℤ,
      ∀ T, T ∈ distTriang _ →
        (@Functor.mapTriangle _ _ _ _ _ _ _ c).obj T ∈ distTriang _) ∧
    (∃ c : (pointIntegralFibre D l hl E.val ⋙
        (DerivedCategory.pointFgComplete
          (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E.val))
          (Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer l E.val)})).ι).CommShift ℤ,
      ∀ T, T ∈ distTriang _ →
        (@Functor.mapTriangle _ _ _ _ _ _ _ c).obj T ∈ distTriang _) ∧
    (∃ c : (pointRationalFibre D l hl E.val ⋙
        (DerivedCategory.pointFiniteDimensional E.val).ι).CommShift ℤ,
      ∀ T, T ∈ distTriang _ →
        (@Functor.mapTriangle _ _ _ _ _ _ _ c).obj T ∈ distTriang _) ∧
    (∃ c : (pointQbarFibre D l hl Ω).CommShift ℤ,
      ∀ T, T ∈ distTriang _ →
        DerivedCategory.pointFdQbarDistinguished l Ω
          ((@Functor.mapTriangle _ _ _ _ _ _ _ c).obj T)) := by
  classical
  have hfinite : (pointFiniteFibre D l hl E.val n hn).IsEquivalence :=
    pointFiniteFibre_equivalence D l hl E.val n hn
  have hintegral : (pointIntegralFibre D l hl E.val).IsEquivalence :=
    pointIntegralFibre_equivalence D l hl E.val
  have hrational : (pointRationalFibre D l hl E.val).IsEquivalence :=
    pointRationalFibre_equivalence D l hl E.val
  have hqbar : (pointQbarFibre D l hl Ω).IsEquivalence := by
    apply pointQbarFibre_equivalence D l hl Ω
    intro i
    unfold pointStageFibre
    have := pointRationalFibre_equivalence D l hl
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i)
    have := pointFdScalarEquivalence
      (Shrink.algEquiv ℚ_[l] i.val).toRingEquiv
    infer_instance
  refine ⟨hfinite, hintegral, hrational, hqbar, ?_, ?_, ?_, ?_⟩
  · have : CategoryTheory.IsGrothendieckAbelian.{u + 1}
        (ModuleCat.{u + 1} (ULift.{u + 1, u}
          (Padic.coefficientExtensionRing l E.val n))) := inferInstance
    let : HasDerivedCategory.{u + 1}
        (ModuleCat.{u + 1} (ULift.{u + 1, u}
          (Padic.coefficientExtensionRing l E.val n))) :=
      HasDerivedCategory.ofIsGrothendieckAbelian _
    let F := pointFiniteFibre D l hl E.val n hn ⋙
      (DerivedCategory.pointFiniteCohomology
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E.val n))).ι
    have hF : F = (intrinsicFiniteTorsionConstructible l E.val n hn
        (Spec (.of D.k))).ι ⋙
        (pointFiniteSections D.k
          (Padic.coefficientExtensionRing l E.val n)).mapDerivedCategory.{u + 2, u + 1} := rfl
    rw [show (pointFiniteFibre D l hl E.val n hn ⋙ _) = _ from hF]
    refine ⟨inferInstance, ?_⟩
    exact Functor.map_distinguished _
  · let : HasDerivedCategory.{u + 1}
        (ModuleCat.{u + 1} (ULift.{u + 1, u}
          (Padic.coefficientExtensionIntegers l E.val))) :=
      HasDerivedCategory.ofIsGrothendieckAbelian _
    let F := pointIntegralFibre D l hl E.val ⋙
      (DerivedCategory.pointFgComplete
        (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E.val))
        (Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer l E.val)})).ι
    have hF : F = (sfIntegralConstructible l E.val (Spec (.of D.k))).ι ⋙
        pointFibreIntegralAmbient D l E.val := rfl
    rw [show (pointIntegralFibre D l hl E.val ⋙ _) = _ from hF]
    refine ⟨inferInstance, ?_⟩
    exact Functor.map_distinguished _
  · exact pointRationalFibre_exact D l hl E.val
  · obtain ⟨c, hc⟩ := pointQbarFibre_shift_descent D l hl Ω
    let := c
    refine ⟨c, ?_⟩
    intro T hT
    obtain ⟨i, U, hU, ⟨e⟩⟩ :=
      (GeneralAlgebraicallyClosedCoefficients.distinguished_iff T).mp hT
    obtain ⟨j, V, hV, h₁, h₂, h₃, ⟨a⟩⟩ := hc i U hU
    exact ⟨j, V, hV, h₁, h₂, h₃,
      ⟨a ≪≫ (DerivedCategory.pointFdQbarRealization l Ω).mapTriangle.mapIso
        ((pointQbarFibre D l hl Ω).mapTriangle.mapIso e.symm)⟩⟩

end WeilConjectures
