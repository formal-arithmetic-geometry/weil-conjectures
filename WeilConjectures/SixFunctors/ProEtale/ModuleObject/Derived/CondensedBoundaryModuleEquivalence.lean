/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.PointFiberFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFdComplexes
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableCriterion
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.DisjointUnion
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionEssImage
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed

/-! # Internal coefficient modules on the finite geometric boundary -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [IsAlgClosed k]
  (I : Type w) [Finite I]

private def adjunctionFan {C : Type*} [Category C] {J : Type*}
    {D : J → Type*} [∀ i, Category (D i)] (r : ∀ i, C ⥤ D i)
    (s : ∀ i, D i ⥤ C) (adj : ∀ i, r i ⊣ s i) (M : C) :
    Fan (fun i ↦ (s i).obj ((r i).obj M)) :=
  Fan.mk M (fun i ↦ (adj i).unit.app M)

private def fanFullyFaithful {C : Type*} [Category C] {J : Type*}
    {D : J → Type*} [∀ i, Category (D i)] (r : ∀ i, C ⥤ D i)
    (s : ∀ i, D i ⥤ C) (adj : ∀ i, r i ⊣ s i)
    (h : ∀ M, IsLimit (adjunctionFan r s adj M)) :
    (Functor.pi' r).FullyFaithful where
  preimage {M N} f := (h N).lift
    (Fan.mk M fun i ↦ (adj i).homEquiv _ _ (f i))
  map_preimage {M N} f := by
    funext i
    apply (adj i).homEquiv _ _ |>.injective
    change (adj i).unit.app M ≫ (r i ⋙ s i).map
      ((h N).lift (Fan.mk M fun i ↦ (adj i).homEquiv _ _ (f i))) =
        (adj i).unit.app M ≫ (s i).map (f i)
    exact ((adj i).unit.naturality _).symm.trans ((h N).fac _ ⟨i⟩)
  preimage_map {M N} f := by
    apply (h N).hom_ext
    intro i
    rw [(h N).fac]
    simpa only [Adjunction.homEquiv_unit, Functor.pi'_map, Functor.comp_map,
      Functor.id_map, adjunctionFan, Fan.mk_π_app] using
      ((adj i.as).unit.naturality f).symm

private def fullyFaithfulPiOfEquiv {C D : Type*} [Category C] [Category D]
    {J J' : Type*} (e : J' ≃ J) (r : J → C ⥤ D)
    (h : (Functor.pi' (fun i ↦ r (e i))).FullyFaithful) :
    (Functor.pi' r).FullyFaithful where
  preimage f := h.preimage (fun i ↦ f (e i))
  map_preimage f := by
    funext j
    obtain ⟨i, rfl⟩ := e.surjective j
    exact congrFun (h.map_preimage (fun i ↦ f (e i))) i
  preimage_map f := h.preimage_map f

private def smallSchemeFamilyFullyFaithful
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U X : Scheme.{u}} {J : Type u} [Finite J]
    (j : J → (U ⟶ X)) (hj : IsColimit (Cofan.mk X j)) :
    (Functor.pi' (fun i ↦ CondensedRing.upperStar Λ (j i))).FullyFaithful :=
  fanFullyFaithful (fun i ↦ CondensedRing.upperStar Λ (j i))
    (fun i ↦ lowerStar Λ (j i)) (fun i ↦ upperStarLowerStarAdjunction Λ (j i))
    (fun M ↦ isLimitFanUnitOfIsColimitCofanConst Λ hj M)

private def schemeFamilyFullyFaithful
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U X : Scheme.{u}} {J : Type w} [Finite J]
    (j : J → (U ⟶ X)) (hj : IsColimit (Cofan.mk X j)) :
    (Functor.pi' (fun i ↦ CondensedRing.upperStar Λ (j i))).FullyFaithful := by
  let e : Shrink.{u} J ≃ J := (equivShrink.{u} J).symm
  apply fullyFaithfulPiOfEquiv e
  exact smallSchemeFamilyFullyFaithful Λ (fun i ↦ j (e i))
    ((Cofan.isColimitEquivOfEquiv e (Cofan.mk X j)) hj)

private def boundaryFullyFaithful :
    (Functor.pi' (condensedBoundaryRestriction ℓ k I)).FullyFaithful := by
  change (Functor.pi' (fun i ↦ CondensedRing.upperStar
    (Profinite.padicAlgClRingObj ℓ) (Sigma.ι (fun _ : I ↦ (point k).left) i))).FullyFaithful
  exact schemeFamilyFullyFaithful (Profinite.padicAlgClRingObj ℓ)
    (Sigma.ι _) (coproductIsCoproduct _)

private def biproduct_single_iso {C : Type*} [Category C] [Preadditive C]
    {J : Type*} [Finite J] (A : J → C) [HasBiproduct A] (j : J)
    (hz : ∀ i, i ≠ j → IsZero (A i)) : (⨁ A) ≅ A j := by
  classical
  refine ⟨biproduct.π A j, biproduct.ι A j, ?_, by simp⟩
  apply biproduct.hom_ext
  intro i
  by_cases h : i = j
  · subst i
    simp
  · exact (hz i h).eq_of_tgt _ _

private theorem schemeFamilyEssSurj
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U X : Scheme.{u}}
    (j : I → (U ⟶ X)) [∀ i, IsOpenImmersion (j i)]
    (hd : Pairwise (fun i t ↦ Disjoint (Set.range (j i)) (Set.range (j t)))) :
    (Functor.pi' (fun i ↦ CondensedRing.upperStar Λ (j i))).EssSurj := by
  classical
  constructor
  intro M
  let J (i : I) : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U) ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X) := openImmersionLowerShriek Λ (j i)
  let N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) :=
    ⨁ fun i : I ↦ (J i).obj (M i)
  refine ⟨N, ⟨Pi.isoMk (fun t ↦ ?_)⟩⟩
  let A (i : I) := (CondensedRing.upperStar Λ (j t)).obj ((J i).obj (M i))
  have hz : ∀ i, i ≠ t → IsZero (A i) := by
    intro i hij
    apply isZero_upperStar_obj_openImmersionLowerShriek_of_disjoint
    exact hd hij
  let adj := openImmersionLowerShriekUpperStarAdjunction
    Λ (j t)
  have : IsIso adj.unit := adj.unit_isIso_of_L_fully_faithful
  exact (CondensedRing.upperStar Λ (j t)).mapBiproduct
      (fun i : I ↦ (J i).obj (M i)) ≪≫
    biproduct_single_iso A t hz ≪≫ (asIso (adj.unit.app (M t))).symm

omit [IsAlgClosed k] in
/-- Restriction identifies boundary module objects with families of point modules.
Source: blueprint local boundary duality, Step 5, finite clopen gluing.
Proof: the adjunction units form a limiting fan by reconstruction on a finite
scheme coproduct. Adjunction therefore identifies morphisms with coordinate
morphisms. For essential surjectivity take the finite sum of the extensions by
zero of the given point modules. Its restriction to a component has that module
as the diagonal summand; all other summands vanish by disjointness. The same
argument covers an empty family, whose sum is the zero object.
(blueprint: lem-a1-condensed-boundary-module-equivalence) -/
theorem condensed_boundary_module_equivalence :
    ∃ E : CondensedBoundaryMod ℓ k I ≌ (I → PointMod ℓ k),
      E.functor = Functor.pi' (condensedBoundaryRestriction ℓ k I) := by
  classical
  let F := Functor.pi' (condensedBoundaryRestriction ℓ k I)
  have : F.Full := (boundaryFullyFaithful ℓ k I).full
  have : F.Faithful := (boundaryFullyFaithful ℓ k I).faithful
  have : F.EssSurj := by
    change (Functor.pi' (fun i ↦ CondensedRing.upperStar
      (Profinite.padicAlgClRingObj ℓ)
      (Sigma.ι (fun _ : I ↦ (point k).left) i))).EssSurj
    apply schemeFamilyEssSurj I (Profinite.padicAlgClRingObj.{u} ℓ)
      (U := (point k).left) (X := condensedPointBoundary k I) (Sigma.ι _)
    intro i t hit
    simpa only [condensedPointBoundary, ← TopologicalSpace.Opens.coe_disjoint,
      Scheme.Hom.coe_opensRange] using
      disjoint_opensRange_sigmaι (fun _ : I ↦ (point k).left) i t hit
  have : F.IsEquivalence := {}
  exact ⟨F.asEquivalence, rfl⟩

end AlgebraicGeometry.ProEtale.CondensedRing
