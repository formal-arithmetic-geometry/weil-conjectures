/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.Algebra.Homology.KFlatFixedTensor.KFlatFixedTensorTriangulatedSupplement
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.SmoothPurity.Ringed.RingedSiteKInjectiveResolutionsSupplement
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import WeilConjectures.Algebra.Homology.Ringed.RingedTensorSquarePresentation
public import WeilConjectures.CategoryTheory.Projection.ProjectionFormulaArrows
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Shift.Adjunction
import WeilConjectures.Algebra.Homology.CanonicalRingedTensorComparison.RingedTopoiCanonicalTensorPullbackSupplement
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.SmoothPurity.Supporting.ChangeOfRingsKFlatQuasiIsoSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.ProperBaseChange.FormalExactProjectionMate
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.CategoryTheory.LeftDerivedKanSourceTriangles
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import WeilConjectures.CategoryTheory.ProperBaseChange.ResolvingRepresentativeWhiskeringSupplement
import WeilConjectures.Algebra.Homology.PullbackTensorCanonical.PullbackTensorCanonicalShiftUnit
import WeilConjectures.Mathlib.CategoryTheory.Shift.Localization

/-!
# Exact projection mates for ringed topoi

Source: Stacks Project, Cohomology on Sites, Tags 06YU, 07A4, 07A6 and 0B56;
Derived Categories, Tag 0A8D (blueprint: lem-weil-pbc-ringed-projection-mate-exact).
-/

@[expose] public section

universe u w

set_option Elab.async true
set_option genSizeOf false
set_option genInjectivity false
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open MonoidalCategory

namespace SheafOfModules

section



/-- The module category of a recorded corner; this is a transparent interface abbreviation.
Source: Stacks Tag 06YU (blueprint: lem-weil-pbc-ringed-projection-mate-exact). -/
abbrev RingedTensorCorner.mateModules (A : RingedTensorCorner.{u, w}) :=
  ringedSiteModules.{u, u, u, u}
    ((sheafCompose A.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj A.ring)

/-- The existing derived category, with the size chosen in the corner.
Source: Stacks Tag 06YU (blueprint: lem-weil-pbc-ringed-projection-mate-exact). -/
abbrev RingedTensorCorner.mateDerived (A : RingedTensorCorner.{u, w}) :=
  DerivedCategory A.mateModules

/-- The degree-zero ring complex, the tensor unit before localization.
Source: Stacks Tag 06YU (blueprint: lem-weil-pbc-ringed-projection-mate-exact). -/
noncomputable abbrev RingedTensorCorner.mateUnitComplex (A : RingedTensorCorner.{u, w}) :=
  letI := monoidalCategory A.ring
  HomologicalComplex.tensorUnit A.mateModules (.up ℤ)

/-- The degree-zero ring in the derived category, rather than an arbitrary unit object.
Source: Stacks Tag 06YU (blueprint: lem-weil-pbc-ringed-projection-mate-exact). -/
noncomputable abbrev RingedTensorCorner.mateUnit (A : RingedTensorCorner.{u, w}) :=
  DerivedCategory.Q.obj A.mateUnitComplex

/-- The ordinary tensor bifunctor already used by the representative presentation.
Source: Stacks Tag 06YU (blueprint: lem-weil-pbc-ringed-projection-mate-exact). -/
noncomputable abbrev RingedTensorCorner.mateTensor (A : RingedTensorCorner.{u, w}) :=
  KFlatFixedTensor.ordinaryTensor A.ring

/-- Flat-term K-flat representatives, with the same predicate as `RingedTensorModel`.
Source: Stacks Tags 06YS, 06YU (blueprint: lem-weil-pbc-ringed-projection-mate-exact). -/
abbrev RingedTensorCorner.mateFlat (A : RingedTensorCorner.{u, w}) :
    ObjectProperty (CochainComplex A.mateModules ℤ) :=
  fun P ↦ P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat

attribute [local instance 4000] KFlatFixedTensor.tensorAdditive
  KFlatFixedTensor.tensorObjAdditive KFlatFixedTensor.tensorHasMapBifunctor

/-- The source of the recorded representative comparison, using the named ordinary tensor.
Source: Stacks, Tag 06YU
(blueprint: lem-weil-pbc-ringed-projection-mate-exact). -/
noncomputable def RingedTensorCorner.mateRepresentativeSource (A : RingedTensorCorner.{u, w}) :=
  (A.mateFlat.ι.prod A.mateFlat.ι) ⋙
    Functor.uncurry.obj A.mateTensor.map₂CochainComplex ⋙ DerivedCategory.Q

/-- The target of the recorded representative comparison.
Source: Stacks, Tag 06YU
(blueprint: lem-weil-pbc-ringed-projection-mate-exact). -/
noncomputable def RingedTensorCorner.mateRepresentativeTarget (A : RingedTensorCorner.{u, w}) :=
  ((A.mateFlat.ι ⋙ DerivedCategory.Q).prod (A.mateFlat.ι ⋙ DerivedCategory.Q)) ⋙ A.tensor

/-- The given representative comparison in its named total-tensor interface.
Its data is the recorded comparison itself.
Source: Stacks, Tag 06YU
(blueprint: lem-weil-pbc-ringed-projection-mate-exact). -/
noncomputable def RingedTensorModel.mateRepresentative {A : RingedTensorCorner.{u, w}}
    (a : RingedTensorModel A) : A.mateRepresentativeSource ≅ A.mateRepresentativeTarget :=
  a.representative

/-- The named representative interface preserves the recorded isomorphism.
Source: Stacks, Tag 06YU
(blueprint: lem-weil-pbc-ringed-projection-mate-exact).
Proof: the interface returns exactly the recorded isomorphism. -/
theorem RingedTensorModel.mateRepresentative_eq {A : RingedTensorCorner.{u, w}}
    (a : RingedTensorModel A) : a.mateRepresentative = a.representative := rfl

/-- Canonical representative shift equations for a tensor localized from cochain complexes.
This is the same unsigned first shift and signed second shift used by ringed tensor models.
Source: Stacks, Tag 06YU (blueprint: lem-weil-pbc-ringed-projection-mate-exact). -/
def MateCanonicalShiftData
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    (F : C ⥤ C ⥤ C) [F.Additive] [∀ U : C, (F.obj U).Additive]
    [∀ P Q : CochainComplex C ℤ, CochainComplex.HasMapBifunctor P Q F]
    (q : CochainComplex C ℤ ⥤ D) [q.CommShift ℤ]
    (T : D × D ⥤ D) [(Functor.curryObj T).CommShift₂Int]
    (flat : ObjectProperty (CochainComplex C ℤ))
    (r : ∀ (P Q : CochainComplex C ℤ) (_hp : flat P) (_hq : flat Q),
      q.obj (CochainComplex.mapBifunctor P Q F) ≅ T.obj (q.obj P, q.obj Q)) : Prop :=
  (∀ (P : CochainComplex C ℤ) (n : ℤ), flat P → flat (P⟦n⟧)) ∧
  (∀ (P Q : CochainComplex C ℤ) (hP : flat P) (hQ : flat Q)
      (n : ℤ) (hPn : flat (P⟦n⟧)),
    (r (P⟦n⟧) Q hPn hQ).hom ≫
        T.map (Prod.mkHom ((q.commShiftIso n).hom.app P)
          (𝟙 (q.obj Q))) ≫
        (((Functor.curryObj T).flip.obj (q.obj Q)).commShiftIso n).hom.app
          (q.obj P) =
      q.map (CochainComplex.mapBifunctorShift₁Iso P Q F n).hom ≫
        (q.commShiftIso n).hom.app
          (CochainComplex.mapBifunctor P Q F) ≫
        (shiftFunctor D n).map ((r P Q hP hQ).hom)) ∧
  (∀ (P Q : CochainComplex C ℤ) (hP : flat P) (hQ : flat Q)
      (n : ℤ) (hQn : flat (Q⟦n⟧)),
    (r P (Q⟦n⟧) hP hQn).hom ≫
        T.map (Prod.mkHom (𝟙 (q.obj P))
          ((q.commShiftIso n).hom.app Q)) ≫
        (((Functor.curryObj T).obj (q.obj P)).commShiftIso n).hom.app
          (q.obj Q) =
      q.map (CochainComplex.mapBifunctorShift₂Iso P Q F n).hom ≫
        (q.commShiftIso n).hom.app
          (CochainComplex.mapBifunctor P Q F) ≫
        (shiftFunctor D n).map ((r P Q hP hQ).hom))


/-- On representatives the first shift is unsigned and the second has the Koszul sign.
The equations transport these existing chain isomorphisms through the representative
identification and the canonical shift comparison of the localization functor.
Source: Stacks Tag 06YU, signed total convention
(blueprint: lem-weil-pbc-ringed-projection-mate-exact). -/
def RingedTensorModel.MateCanonicalShifts {A : RingedTensorCorner.{u, w}}
    (a : RingedTensorModel A) [(Functor.curryObj A.tensor).CommShift₂Int] : Prop :=
  letI := monoidalCategory A.ring
  letI := ringedTensorPreadditive A.ring
  MateCanonicalShiftData A.mateTensor DerivedCategory.Q A.tensor A.mateFlat
    (fun P Q hp hq ↦ a.mateRepresentative.app (⟨P, hp⟩, ⟨Q, hq⟩))

/-- Representative normalization of a right unit, with its specified cochain summands.
The multiplication morphisms are parameters so that transport is independent of the site.
Source: Stacks, Tags 06YU and 07A4
(blueprint: lem-weil-pbc-ringed-projection-mate-exact). -/
def MateCanonicalUnitData
    {C D : Type*} [Category* C] [Category* D] [Preadditive C]
    (F : C ⥤ C ⥤ C) [F.Additive] [∀ U : C, (F.obj U).Additive]
    [∀ P Q : CochainComplex C ℤ, CochainComplex.HasMapBifunctor P Q F]
    (q : CochainComplex C ℤ ⥤ D) (T : D × D ⥤ D)
    (flat : ObjectProperty (CochainComplex C ℤ)) (I : CochainComplex C ℤ)
    (mul : ∀ (P : CochainComplex C ℤ) (n : ℤ),
      (F.obj (P.X n)).obj (I.X 0) ⟶ P.X n)
    (r : ∀ (P Q : CochainComplex C ℤ) (_hp : flat P) (_hq : flat Q),
      q.obj (CochainComplex.mapBifunctor P Q F) ≅ T.obj (q.obj P, q.obj Q))
    (rho : ∀ U : D, T.obj (U, q.obj I) ≅ U) : Prop :=
  ∃ hi : flat I, ∀ (P : CochainComplex C ℤ) (hp : flat P),
    ∃ j : CochainComplex.mapBifunctor P I F ≅ P,
      (∀ n : ℤ, CochainComplex.ιMapBifunctor P I F n 0 n (add_zero n) ≫
        j.hom.f n = mul P n) ∧
      (r P I hp hi).hom ≫ (rho (q.obj P)).hom = q.map j.hom

/-- Canonical right unitors are induced by multiplication on every total-complex summand.
The chain map is specified by its composites with all summand inclusions, so its data
cannot be replaced by an arbitrary isomorphism. This also asserts that the unit is K-flat.
Source: Stacks Tags 06YU, 07A4 (blueprint: lem-weil-pbc-ringed-projection-mate-exact). -/
def RingedTensorModel.MateCanonicalUnit {A : RingedTensorCorner.{u, w}}
    (a : RingedTensorModel A) (r : ∀ U : A.mateDerived, A.tensor.obj (U, A.mateUnit) ≅ U) :
    Prop :=
  letI := monoidalCategory A.ring
  letI := ringedTensorPreadditive A.ring
  MateCanonicalUnitData A.mateTensor DerivedCategory.Q A.tensor A.mateFlat A.mateUnitComplex
    (fun P n ↦ (A.mateTensor.obj (P.X n)).map
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (SheafOfModules.unit ((sheafCompose A.topology
          (forget₂ CommRingCat.{u} RingCat.{u})).obj A.ring))).hom ≫
      ((monoidalCategory A.ring).rightUnitor (P.X n)).hom)
    (fun P Q hp hq ↦ a.mateRepresentative.app (⟨P, hp⟩, ⟨Q, hq⟩)) r

attribute [local irreducible] RingedTensorModel.mateRepresentative

attribute [-instance] cochainModulesMonoidal cochainModulesSymmetric

set_option backward.defeqAttrib.useBackward false
set_option synthInstance.maxSize 512


attribute [local irreducible] monoidalCategory siteDerivedTensorIndependentCoefficients
  RingedTensorEdge.tensorComparison ringedTopoiCanonicalDerivedTensorComparison
  CochainComplex.IsAcyclicTensorKFlat CochainComplex.IsKFlatIndependentCoefficients
  KFlatFixedTensor.representativeIso HomologicalComplex₂.total
  MorphismProperty.Q'

private theorem mateFlatOnSite (A : RingedTensorCorner.{u, w})
    (M : A.mateModules) : M.IsFlat ↔ IsFlatOnSite (J := A.topology) (R := A.ring) M := by
  let := monoidalCategory A.ring
  constructor
  · exact ObjectProperty.prop_of_iso (exactFunctor _ _)
      (siteSheafTensorRightIso A.ring M).symm
  · exact ObjectProperty.prop_of_iso (exactFunctor _ _)
      (siteSheafTensorRightIso A.ring M)

set_option maxHeartbeats 20000 in
-- Diagnose conversion without expanding the tensor definitions.
private theorem mateFlatIndependent (A : RingedTensorCorner.{u, w})
    (P : CochainComplex A.mateModules ℤ) :
    A.mateFlat P ↔ CochainComplex.IsKFlatIndependentCoefficients (R := A.ring) P ∧
      ∀ n : ℤ, IsFlatOnSite (J := A.topology) (R := A.ring) (P.X n) := by
  constructor
  · intro h
    exact ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat (R := A.ring) P).2 h.1,
      fun n ↦ (mateFlatOnSite A (P.X n)).1 (h.2 n)⟩
  · intro h
    exact ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat (R := A.ring) P).1 h.1,
      fun n ↦ (mateFlatOnSite A (P.X n)).2 (h.2 n)⟩

private theorem mateFlatResolution (A : RingedTensorCorner.{u, w})
    (K : CochainComplex A.mateModules ℤ) :
    ∃ (P : CochainComplex A.mateModules ℤ) (p : P ⟶ K),
      P.IsAcyclicTensorKFlat ∧ (∀ n : ℤ, (P.X n).IsFlat) ∧
        QuasiIso p ∧ (∀ n : ℤ, Epi (p.f n)) := by
  obtain ⟨P, p, hp, hf, hq, hepi⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := A.ring) K
  exact ⟨P, p,
    (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).1 hp, hf, hq, hepi⟩

set_option maxHeartbeats 50000 in
-- Elaboration must compare the large two-variable localization interfaces.
private theorem mateResolvingFF (A : RingedTensorCorner.{u, w})
    (E : Type*) [Category* E] :
    Nonempty (((Functor.whiskeringLeft
      (A.mateFlat.FullSubcategory × A.mateFlat.FullSubcategory)
      (A.mateDerived × A.mateDerived) E).obj
      ((A.mateFlat.ι ⋙ DerivedCategory.Q).prod
        (A.mateFlat.ι ⋙ DerivedCategory.Q))).FullyFaithful) := by
  let S : ObjectProperty (HomotopyCategory A.mateModules (.up ℤ)) :=
    fun T ↦ A.mateFlat T.as
  refine resolvingRepresentativesFullyFaithfulWhiskering E
    (HomotopyCategory.quotient A.mateModules (.up ℤ))
    HomotopyCategory.quotient_obj_surjective
    (HomotopyCategory.quasiIso A.mateModules (.up ℤ)) DerivedCategory.Qh
    A.mateFlat S (fun _ ↦ Iff.rfl) ?_
  intro T
  obtain ⟨P, p, hp, hf, hq, _⟩ := mateFlatResolution A T.as
  exact ⟨⟨(HomotopyCategory.quotient A.mateModules (.up ℤ)).obj P, hp, hf⟩,
    (HomotopyCategory.quotient A.mateModules (.up ℤ)).map p,
    (HomotopyCategory.quotient_map_mem_quasiIso_iff p).2 hq⟩

set_option maxHeartbeats 50000 in
-- Elaboration must compare the large two-variable localization interfaces.
private theorem mateLiftModelIso
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (q : C ⥤ D) (F G : D ⥤ E)
    (ff : ((Functor.whiskeringLeft C D E).obj q).FullyFaithful)
    {H : C ⥤ E} (a : H ≅ q ⋙ F) (b : H ≅ q ⋙ G) :
    ∃ z : F ≅ G, ∀ P : C, a.hom.app P ≫ z.hom.app (q.obj P) = b.hom.app P := by
  let z := ff.preimageIso (X := F) (Y := G) (a.symm ≪≫ b)
  refine ⟨z, ?_⟩
  intro P
  have hz := congrArg (fun t ↦ t.app P) (ff.map_preimage (a.symm ≪≫ b).hom)
  change z.hom.app (q.obj P) = a.inv.app P ≫ b.hom.app P at hz
  exact (congrArg (a.hom.app P ≫ ·) hz).trans
    (by simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp])

private theorem mateCochainShiftEquation₁
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    (F : C ⥤ C ⥤ C) [F.Additive] [∀ X : C, (F.obj X).Additive]
    [∀ P Q : CochainComplex C ℤ, CochainComplex.HasMapBifunctor P Q F]
    (q : CochainComplex C ℤ ⥤ D) [q.CommShift ℤ]
    (T : D × D ⥤ D) [(Functor.curryObj T).CommShift₂Int]
    (P Q : CochainComplex C ℤ) (n : ℤ)
    (c : F.map₂CochainComplex.flip.obj Q ⋙ q ⟶
      q ⋙ (Functor.curryObj T).flip.obj (q.obj Q))
    [NatTrans.CommShift c ℤ]
    (r0 : q.obj (CochainComplex.mapBifunctor P Q F) ⟶ T.obj (q.obj P, q.obj Q))
    (rn : q.obj (CochainComplex.mapBifunctor (P⟦n⟧) Q F) ⟶ T.obj (q.obj (P⟦n⟧), q.obj Q))
    (h0 : c.app P = r0) (hn : c.app (P⟦n⟧) = rn) :
    rn ≫ T.map (Prod.mkHom ((q.commShiftIso n).hom.app P) (𝟙 (q.obj Q))) ≫
      (((Functor.curryObj T).flip.obj (q.obj Q)).commShiftIso n).hom.app (q.obj P) =
    q.map (CochainComplex.mapBifunctorShift₁Iso P Q F n).hom ≫
      (q.commShiftIso n).hom.app (CochainComplex.mapBifunctor P Q F) ≫
      (shiftFunctor D n).map r0 := by
  have h := (NatTrans.shift_app_comm c n P).symm
  rw [h0, hn] at h
  simp only [Functor.commShiftIso_comp_hom_app,
    Functor.commShiftIso_map₂CochainComplex_flip_hom_app] at h
  dsimp only [Functor.comp_obj, Functor.flip_obj_obj,
    Functor.map₂CochainComplex, Functor.map₂HomologicalComplex] at h
  simpa only [Functor.curryObj, Functor.flip_obj_map, Functor.flip_obj_obj,
    Category.assoc] using h

private theorem mateCochainShiftEquation₂
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    (F : C ⥤ C ⥤ C) [F.Additive] [∀ X : C, (F.obj X).Additive]
    [∀ P Q : CochainComplex C ℤ, CochainComplex.HasMapBifunctor P Q F]
    (q : CochainComplex C ℤ ⥤ D) [q.CommShift ℤ]
    (T : D × D ⥤ D) [(Functor.curryObj T).CommShift₂Int]
    (P Q : CochainComplex C ℤ) (n : ℤ)
    (c : F.map₂CochainComplex.obj P ⋙ q ⟶
      q ⋙ (Functor.curryObj T).obj (q.obj P))
    [NatTrans.CommShift c ℤ]
    (r0 : q.obj (CochainComplex.mapBifunctor P Q F) ⟶ T.obj (q.obj P, q.obj Q))
    (rn : q.obj (CochainComplex.mapBifunctor P (Q⟦n⟧) F) ⟶ T.obj (q.obj P, q.obj (Q⟦n⟧)))
    (h0 : c.app Q = r0) (hn : c.app (Q⟦n⟧) = rn) :
    rn ≫ T.map (Prod.mkHom (𝟙 (q.obj P)) ((q.commShiftIso n).hom.app Q)) ≫
      (((Functor.curryObj T).obj (q.obj P)).commShiftIso n).hom.app (q.obj Q) =
    q.map (CochainComplex.mapBifunctorShift₂Iso P Q F n).hom ≫
      (q.commShiftIso n).hom.app (CochainComplex.mapBifunctor P Q F) ≫
      (shiftFunctor D n).map r0 := by
  have h := (NatTrans.shift_app_comm c n Q).symm
  rw [h0, hn] at h
  simp only [Functor.commShiftIso_comp_hom_app,
    Functor.commShiftIso_map₂CochainComplex_hom_app] at h
  dsimp only [Functor.comp_obj, Functor.flip_obj_obj,
    Functor.map₂CochainComplex, Functor.map₂HomologicalComplex] at h
  simpa only [Functor.curryObj, Functor.flip_obj_map, Functor.flip_obj_obj,
    Category.assoc] using h

private theorem mateShiftDataOfComputations
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
    (F : C ⥤ C ⥤ C) [F.Additive] [∀ U : C, (F.obj U).Additive]
    [∀ P Q : CochainComplex C ℤ, CochainComplex.HasMapBifunctor P Q F]
    (q : CochainComplex C ℤ ⥤ D) [q.CommShift ℤ]
    (T : D × D ⥤ D) [(Functor.curryObj T).CommShift₂Int]
    (flat : ObjectProperty (CochainComplex C ℤ))
    (r : ∀ (P Q : CochainComplex C ℤ) (_hp : flat P) (_hq : flat Q),
      q.obj (CochainComplex.mapBifunctor P Q F) ≅ T.obj (q.obj P, q.obj Q))
    (hstable : ∀ (P : CochainComplex C ℤ) (n : ℤ), flat P → flat (P⟦n⟧))
    (hcan : ∀ (P : CochainComplex C ℤ) (hp : flat P),
      (∃ c : F.map₂CochainComplex.obj P ⋙ q ≅
          q ⋙ (Functor.curryObj T).obj (q.obj P),
        NatTrans.CommShift c.hom ℤ ∧ ∀ (Q : CochainComplex C ℤ) (hq : flat Q),
          c.app Q = r P Q hp hq) ∧
      (∃ c : F.map₂CochainComplex.flip.obj P ⋙ q ≅
          q ⋙ (Functor.curryObj T).flip.obj (q.obj P),
        NatTrans.CommShift c.hom ℤ ∧ ∀ (Q : CochainComplex C ℤ) (hq : flat Q),
          c.app Q = r Q P hq hp)) : MateCanonicalShiftData F q T flat r := by
  refine ⟨hstable, ?_, ?_⟩
  · intro P Q hp hq n hpn
    obtain ⟨c, hc, heq⟩ := (hcan Q hq).2
    let := hc
    exact mateCochainShiftEquation₁ F q T P Q n c.hom
      (r P Q hp hq).hom (r (P⟦n⟧) Q hpn hq).hom
      (congrArg Iso.hom (heq P hp)) (congrArg Iso.hom (heq (P⟦n⟧) hpn))
  · intro P Q hp hq n hqn
    obtain ⟨c, hc, heq⟩ := (hcan P hp).1
    let := hc
    exact mateCochainShiftEquation₂ F q T P Q n c.hom
      (r P Q hp hq).hom (r P (Q⟦n⟧) hp hqn).hom
      (congrArg Iso.hom (heq Q hq)) (congrArg Iso.hom (heq (Q⟦n⟧) hqn))

private structure MatePublishedData (A : RingedTensorCorner.{u, w})
    [s : (KFlatFixedTensor.derivedTensor A.ring).CommShift₂Int] where
  model : RingedTensorModel
    { A with tensor := siteDerivedTensorIndependentCoefficients.{u, u, u, w} A.topology A.ring }
  canonical :
    let : (Functor.curryObj
      (siteDerivedTensorIndependentCoefficients.{u, u, u, w} A.topology A.ring)).CommShift₂Int :=
      s
    model.MateCanonicalShifts
  representative : ∀ (P Q : CochainComplex A.mateModules ℤ)
      (hp : A.mateFlat P) (hq : A.mateFlat Q),
    model.mateRepresentative.app (⟨P, hp⟩, ⟨Q, hq⟩) =
      KFlatFixedTensor.representativeIso.{u, u, u, w} A.ring P Q
        ((mateFlatIndependent A P).1 hp).1 ((mateFlatIndependent A Q).1 hq).1
        ((mateFlatIndependent A P).1 hp).2 ((mateFlatIndependent A Q).1 hq).2

private theorem mateUncurryMap {C D E : Type*}
    [Category* C] [Category* D] [Category* E]
    (T : C × D ⥤ E) {P Q : C × D} (f : P ⟶ Q) :
    (Functor.uncurry.obj (Functor.curryObj T)).map f = T.map f := by
  rcases P with ⟨P, P'⟩
  rcases Q with ⟨Q, Q'⟩
  rcases f with ⟨f, g⟩
  simp [Functor.uncurry, Functor.curryObj, ← CategoryTheory.Functor.map_comp]

private theorem matePublishedDataExists (A : RingedTensorCorner.{u, w})
    [s : (KFlatFixedTensor.derivedTensor A.ring).CommShift₂Int]
    (hcan : PullbackTensorCanonical.HasCanonicalTensorShifts (R := A.ring)) :
    Nonempty (MatePublishedData A) := by
  let : (Functor.curryObj
      (siteDerivedTensorIndependentCoefficients.{u, u, u, w} A.topology A.ring)).CommShift₂Int :=
    s
  let r (P Q : CochainComplex A.mateModules ℤ) (hp : A.mateFlat P) (hq : A.mateFlat Q) :=
    KFlatFixedTensor.representativeIso.{u, u, u, w} A.ring P Q
      ((mateFlatIndependent A P).1 hp).1 ((mateFlatIndependent A Q).1 hq).1
      ((mateFlatIndependent A P).1 hp).2 ((mateFlatIndependent A Q).1 hq).2
  have hcomp (P : CochainComplex A.mateModules ℤ) (hp : A.mateFlat P) :
      (∃ c : A.mateTensor.map₂CochainComplex.obj P ⋙ DerivedCategory.Q ≅
          DerivedCategory.Q ⋙ (Functor.curryObj
            (siteDerivedTensorIndependentCoefficients A.topology A.ring)).obj
              (DerivedCategory.Q.obj P),
        NatTrans.CommShift c.hom ℤ ∧ ∀ (Q : CochainComplex A.mateModules ℤ)
          (hq : A.mateFlat Q), c.app Q = r P Q hp hq) ∧
      (∃ c : A.mateTensor.map₂CochainComplex.flip.obj P ⋙ DerivedCategory.Q ≅
          DerivedCategory.Q ⋙ (Functor.curryObj
            (siteDerivedTensorIndependentCoefficients A.topology A.ring)).flip.obj
              (DerivedCategory.Q.obj P),
        NatTrans.CommShift c.hom ℤ ∧ ∀ (Q : CochainComplex A.mateModules ℤ)
          (hq : A.mateFlat Q), c.app Q = r Q P hq hp) := by
    have hP := (mateFlatIndependent A P).1 hp
    have h := hcan P hP.1 hP.2
    constructor
    · obtain ⟨c, hc, heq⟩ := h.1
      exact ⟨c, hc, fun Q hq ↦ heq Q ((mateFlatIndependent A Q).1 hq).1
        ((mateFlatIndependent A Q).1 hq).2⟩
    · obtain ⟨c, hc, heq⟩ := h.2
      exact ⟨c, hc, fun Q hq ↦ heq Q ((mateFlatIndependent A Q).1 hq).1
        ((mateFlatIndependent A Q).1 hq).2⟩
  have hstable (P : CochainComplex A.mateModules ℤ) (n : ℤ) (hp : A.mateFlat P) :
      A.mateFlat (P⟦n⟧) := by
    have h := (mateFlatIndependent A P).1 hp
    obtain ⟨_, ht⟩ := KFlatFixedTensor.kFlat_fixed_tensor_triangulated A.ring
    exact (mateFlatIndependent A (P⟦n⟧)).2 ((ht P h.1 h.2).2.1 n)
  let m : RingedTensorModel
      { A with tensor :=
          siteDerivedTensorIndependentCoefficients.{u, u, u, w} A.topology A.ring } :=
    ⟨NatIso.ofComponents
      (fun Z ↦ r Z.1.obj Z.2.obj Z.1.property Z.2.property) (by
        intro P Q g
        have h := PullbackTensorCanonical.canonicalRepresentativeIso_naturality hcan
          P.1.obj P.2.obj Q.1.obj Q.2.obj
          ((mateFlatIndependent A P.1.obj).1 P.1.property).1
          ((mateFlatIndependent A P.2.obj).1 P.2.property).1
          ((mateFlatIndependent A Q.1.obj).1 Q.1.property).1
          ((mateFlatIndependent A Q.2.obj).1 Q.2.property).1
          ((mateFlatIndependent A P.1.obj).1 P.1.property).2
          ((mateFlatIndependent A P.2.obj).1 P.2.property).2
          ((mateFlatIndependent A Q.1.obj).1 Q.1.property).2
          ((mateFlatIndependent A Q.2.obj).1 Q.2.property).2 g.1.hom g.2.hom
        change DerivedCategory.Q.map
            (((KFlatFixedTensor.totalTensor A.ring).map g.1.hom).app P.2.obj ≫
              ((KFlatFixedTensor.totalTensor A.ring).obj Q.1.obj).map g.2.hom) ≫
            (r Q.1.obj Q.2.obj Q.1.property Q.2.property).hom =
          (r P.1.obj P.2.obj P.1.property P.2.property).hom ≫
            (Functor.uncurry.obj (Functor.curryObj
              (siteDerivedTensorIndependentCoefficients A.topology A.ring))).map
                (Prod.mkHom (DerivedCategory.Q.map g.1.hom)
                  (DerivedCategory.Q.map g.2.hom)) at h
        exact h.trans (congrArg
          ((r P.1.obj P.2.obj P.1.property P.2.property).hom ≫ ·)
          (mateUncurryMap (siteDerivedTensorIndependentCoefficients A.topology A.ring)
            (Prod.mkHom (DerivedCategory.Q.map g.1.hom)
              (DerivedCategory.Q.map g.2.hom)))))⟩
  have hm (P Q : CochainComplex A.mateModules ℤ) (hp : A.mateFlat P)
      (hq : A.mateFlat Q) : m.mateRepresentative.app (⟨P, hp⟩, ⟨Q, hq⟩) = r P Q hp hq := by
    rw [RingedTensorModel.mateRepresentative_eq]
    rfl
  refine ⟨⟨m, ?_, ?_⟩⟩
  · delta RingedTensorModel.MateCanonicalShifts RingedTensorModel.mateRepresentative
    exact mateShiftDataOfComputations A.mateTensor DerivedCategory.Q
      (siteDerivedTensorIndependentCoefficients.{u, u, u, w} A.topology A.ring)
      A.mateFlat r hstable hcomp
  · exact hm

private def mateCurryIso {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {F G : C × D ⥤ E} (z : F ≅ G) : Functor.curryObj F ≅ Functor.curryObj G :=
  Functor.curry.mapIso z

private def mateFlipCurryIso {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {F G : C × D ⥤ E} (z : F ≅ G) :
    (Functor.curryObj F).flip ≅ (Functor.curryObj G).flip :=
  (flipFunctor _ _ _).mapIso (mateCurryIso z)

set_option maxHeartbeats 50000 in
-- Elaboration must compare the large two-variable localization interfaces.
private theorem mateTensorShiftOfIso {C : Type*} [Category* C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    (S T : C × C ⥤ C)
    [(Functor.curryObj T).CommShift₂Int] (z : S ≅ T) :
    ∃ s : (Functor.curryObj S).CommShift₂Int,
      let := s;
      (∀ U, NatTrans.CommShift ((mateCurryIso z).hom.app U) ℤ) ∧
      (∀ V, NatTrans.CommShift
        ((mateFlipCurryIso z).hom.app V) ℤ) := by
  classical
  let W := MorphismProperty.isomorphisms C
  let F := Functor.curryObj T
  let G := Functor.curryObj S
  let lifting : Localization.Lifting₂ (𝟭 C) (𝟭 C) W W F G :=
    ⟨Functor.curry.mapIso z⟩
  let s := Functor.commShift₂OfLocalization (𝟭 C) (𝟭 C) W W F G
    (.int)
  let := s
  refine ⟨s, ?_, ?_⟩
  · intro U
    let d := Functor.CommShift₂OfLocalization.liftingIsoApp
      (𝟭 C) (𝟭 C) W W F G U
    have hd : NatTrans.CommShift d ℤ :=
      Functor.CommShift₂OfLocalization.commShift_liftingIsoApp (M := ℤ)
        (𝟭 C) (𝟭 C) W W F G U
    let := hd
    have hc : NatTrans.CommShift ((Functor.leftUnitor (G.obj U)).inv ≫ d) ℤ :=
      inferInstance
    have he : (Functor.leftUnitor (G.obj U)).inv ≫ d =
        (mateCurryIso z).hom.app U := by
      ext V
      exact Category.id_comp _
    rw [he] at hc
    exact hc
  · intro V
    let d := Functor.CommShift₂OfLocalization.liftingIsoApp
      (𝟭 C) (𝟭 C) W W F.flip G.flip V
    have hd : NatTrans.CommShift d ℤ :=
      Functor.CommShift₂OfLocalization.commShift_liftingIsoApp (M := ℤ)
        (𝟭 C) (𝟭 C) W W F.flip G.flip V
    let := hd
    have hc : NatTrans.CommShift ((Functor.leftUnitor (G.flip.obj V)).inv ≫ d) ℤ :=
      inferInstance
    have he : (Functor.leftUnitor (G.flip.obj V)).inv ≫ d =
        (mateFlipCurryIso z).hom.app V := by
      ext U
      exact Category.id_comp _
    rw [he] at hc
    exact hc

private theorem mateShiftTransportEquation {C : Type*} [Category* C] (F : C ⥤ C)
    {X Y Z A0 A1 A2 B0 B1 B2 : C}
    (rS : X ⟶ A1) (rT : X ⟶ B1) (r0 : Y ⟶ A0) (rT0 : Y ⟶ B0)
    (z1 : A1 ⟶ B1) (z2 : A2 ⟶ B2) (z0 : A0 ⟶ B0) [IsIso z0]
    (f : A1 ⟶ A2) (g : B1 ⟶ B2) (h : A2 ⟶ F.obj A0) (i : B2 ⟶ F.obj B0)
    (l : X ⟶ Z) (k : Z ⟶ F.obj Y)
    (hRS : rS ≫ z1 = rT) (hR0 : r0 ≫ z0 = rT0)
    (hN : f ≫ z2 = z1 ≫ g) (hS : h ≫ F.map z0 = z2 ≫ i)
    (hT : rT ≫ g ≫ i = l ≫ k ≫ F.map rT0) :
    rS ≫ f ≫ h = l ≫ k ≫ F.map r0 := by
  apply (cancel_mono (F.map z0)).1
  simp only [Category.assoc]
  rw [hS, ← Category.assoc f z2, hN]
  simp only [Category.assoc]
  rw [← Category.assoc rS z1, hRS, hT, ← F.map_comp, hR0]

set_option maxHeartbeats 50000 in
-- Elaboration must compare the large two-variable localization interfaces.
private theorem mateCanonicalShiftTransport
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    (F : C ⥤ C ⥤ C) [F.Additive] [∀ U : C, (F.obj U).Additive]
    [∀ P Q : CochainComplex C ℤ, CochainComplex.HasMapBifunctor P Q F]
    (q : CochainComplex C ℤ ⥤ D) [q.CommShift ℤ]
    (S T : D × D ⥤ D) (flat : ObjectProperty (CochainComplex C ℤ))
    (a : ∀ (P Q : CochainComplex C ℤ) (_hp : flat P) (_hq : flat Q),
      q.obj (CochainComplex.mapBifunctor P Q F) ≅ S.obj (q.obj P, q.obj Q))
    (b : ∀ (P Q : CochainComplex C ℤ) (_hp : flat P) (_hq : flat Q),
      q.obj (CochainComplex.mapBifunctor P Q F) ≅ T.obj (q.obj P, q.obj Q))
    (z : S ≅ T)
    (hz : ∀ (P Q : flat.FullSubcategory),
      (a P.obj Q.obj P.property Q.property).hom ≫ z.hom.app
        (q.obj P.obj, q.obj Q.obj) = (b P.obj Q.obj P.property Q.property).hom)
    [(Functor.curryObj S).CommShift₂Int] [(Functor.curryObj T).CommShift₂Int]
    (hcL : ∀ U, NatTrans.CommShift ((mateCurryIso z).hom.app U) ℤ)
    (hcR : ∀ V, NatTrans.CommShift ((mateFlipCurryIso z).hom.app V) ℤ)
    (hb : MateCanonicalShiftData F q T flat b) : MateCanonicalShiftData F q S flat a := by
  refine ⟨hb.1, ?_, ?_⟩
  · intro P Q hp hq n hpn
    let := hcR (q.obj Q)
    have hs := NatTrans.shift_app_comm
      ((mateFlipCurryIso z).hom.app
        (q.obj Q)) n (q.obj P)
    change (((Functor.curryObj S).flip.obj (q.obj Q)).commShiftIso
        n).hom.app (q.obj P) ≫
        (shiftFunctor D n).map
          (z.hom.app (q.obj P, q.obj Q)) =
      z.hom.app ((q.obj P)⟦n⟧, q.obj Q) ≫
        (((Functor.curryObj T).flip.obj (q.obj Q)).commShiftIso
          n).hom.app (q.obj P) at hs
    have hn := z.hom.naturality (Prod.mkHom
      ((q.commShiftIso n).hom.app P) (𝟙 (q.obj Q)))
    apply mateShiftTransportEquation (shiftFunctor D n) _ _ _ _
      (z.hom.app (q.obj (P⟦n⟧), q.obj Q))
      (z.hom.app ((q.obj P)⟦n⟧, q.obj Q))
      (z.hom.app (q.obj P, q.obj Q)) _ _ _ _ _ _
    · exact hz ⟨P⟦n⟧, hpn⟩ ⟨Q, hq⟩
    · exact hz ⟨P, hp⟩ ⟨Q, hq⟩
    · exact hn
    · exact hs
    · exact hb.2.1 P Q hp hq n hpn
  · intro P Q hp hq n hqn
    let := hcL (q.obj P)
    have hs := NatTrans.shift_app_comm
      ((mateCurryIso z).hom.app (q.obj P)) n (q.obj Q)
    change (((Functor.curryObj S).obj (q.obj P)).commShiftIso
        n).hom.app (q.obj Q) ≫
        (shiftFunctor D n).map
          (z.hom.app (q.obj P, q.obj Q)) =
      z.hom.app (q.obj P, (q.obj Q)⟦n⟧) ≫
        (((Functor.curryObj T).obj (q.obj P)).commShiftIso
          n).hom.app (q.obj Q) at hs
    have hn := z.hom.naturality (Prod.mkHom (𝟙 (q.obj P))
      ((q.commShiftIso n).hom.app Q))
    apply mateShiftTransportEquation (shiftFunctor D n) _ _ _ _
      (z.hom.app (q.obj P, q.obj (Q⟦n⟧)))
      (z.hom.app (q.obj P, (q.obj Q)⟦n⟧))
      (z.hom.app (q.obj P, q.obj Q)) _ _ _ _ _ _
    · exact hz ⟨P, hp⟩ ⟨Q⟦n⟧, hqn⟩
    · exact hz ⟨P, hp⟩ ⟨Q, hq⟩
    · exact hn
    · exact hs
    · exact hb.2.2 P Q hp hq n hqn

section
-- The unit of this monoidal structure is definitionally the ring module.
attribute [local semireducible] monoidalCategory

private theorem mateGenericCochainRightUnitor
    {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]
    [MonoidalCategory C] [MonoidalPreadditive C]
    [∀ X : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X)]
    (P : CochainComplex C ℤ) (n : ℤ) :
    HomologicalComplex.ιTensorObj P (HomologicalComplex.tensorUnit C (.up ℤ))
        n 0 n (add_zero n) ≫ (HomologicalComplex.rightUnitor P).hom.f n =
      (P.X n) ◁ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ C)).hom ≫
        (ρ_ (P.X n)).hom := by
  let j := HomologicalComplex.rightUnitor P
  let i := HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ C)
  apply (cancel_epi ((ρ_ (P.X n)).inv ≫ (P.X n) ◁ i.inv)).1
  have hi := HomologicalComplex.rightUnitor'_inv P n
  change j.inv.f n = (ρ_ (P.X n)).inv ≫ (P.X n) ◁ i.inv ≫
    HomologicalComplex.ιTensorObj P (HomologicalComplex.tensorUnit C (.up ℤ))
      n 0 n (add_zero n) at hi
  simp only [← Category.assoc] at hi ⊢
  rw [← hi]
  simp only [Category.assoc]
  change j.inv.f n ≫ j.hom.f n =
    (ρ_ (P.X n)).inv ≫ (P.X n) ◁ i.inv ≫ (P.X n) ◁ i.hom ≫ (ρ_ (P.X n)).hom
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, i.inv_hom_id,
    MonoidalCategory.whiskerLeft_id, Category.id_comp, Iso.inv_hom_id]
  have hj := congrArg (fun f ↦ f.f n) j.inv_hom_id
  simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using hj

private theorem mateUnitDataOfNormalization
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [HasZeroObject C]
    [MonoidalCategory C] [MonoidalPreadditive C]
    [∀ X : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X)]
    [∀ P Q : CochainComplex C ℤ, CochainComplex.HasMapBifunctor P Q (curriedTensor C)]
    (q : CochainComplex C ℤ ⥤ D) (T : D × D ⥤ D)
    (flat : ObjectProperty (CochainComplex C ℤ))
    (r : ∀ (P Q : CochainComplex C ℤ) (_hp : flat P) (_hq : flat Q),
      q.obj (CochainComplex.mapBifunctor P Q (curriedTensor C)) ≅
        T.obj (q.obj P, q.obj Q))
    (rho : ∀ U : D, T.obj (U, q.obj (HomologicalComplex.tensorUnit C (.up ℤ))) ≅ U)
    (hi : flat (HomologicalComplex.tensorUnit C (.up ℤ)))
    (hn : ∀ (P : CochainComplex C ℤ) (hp : flat P),
      (r P (HomologicalComplex.tensorUnit C (.up ℤ)) hp hi).hom ≫ (rho (q.obj P)).hom =
        q.map (HomologicalComplex.rightUnitor P).hom) :
    MateCanonicalUnitData (curriedTensor C) q T flat
      (HomologicalComplex.tensorUnit C (.up ℤ))
      (fun P n ↦ (P.X n) ◁ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ C)).hom ≫
        (ρ_ (P.X n)).hom) r rho := by
  refine ⟨hi, ?_⟩
  intro P hp
  exact ⟨HomologicalComplex.rightUnitor P, fun n ↦ mateGenericCochainRightUnitor P n, hn P hp⟩

set_option maxHeartbeats 50000 in
-- Keep the monoidal unit behind the cochain unitor API.
private theorem matePublishedUnitNormalized (A : RingedTensorCorner.{u, w})
    (r : RingedTensorModel
      { A with tensor := siteDerivedTensorIndependentCoefficients.{u, u, u, w} A.topology A.ring })
    (hr : ∀ (P Q : CochainComplex A.mateModules ℤ) (hp : A.mateFlat P)
      (hq : A.mateFlat Q), r.mateRepresentative.app (⟨P, hp⟩, ⟨Q, hq⟩) =
        KFlatFixedTensor.representativeIso.{u, u, u, w} A.ring P Q
          ((mateFlatIndependent A P).1 hp).1 ((mateFlatIndependent A Q).1 hq).1
          ((mateFlatIndependent A P).1 hp).2 ((mateFlatIndependent A Q).1 hq).2)
    (u : PullbackTensorCanonical.ActionUnits (R := A.ring)) :
    r.MateCanonicalUnit (fun M ↦ u.rho.app M) := by
  let := monoidalCategory A.ring
  let := ringedTensorPreadditive A.ring
  have hunit : A.mateFlat A.mateUnitComplex :=
    (mateFlatIndependent A _).2 ⟨u.unit_kflat, u.unit_flat⟩
  unfold RingedTensorModel.MateCanonicalUnit RingedTensorCorner.mateTensor
  apply mateUnitDataOfNormalization DerivedCategory.Q _ A.mateFlat
    (fun P Q hp hq ↦ r.mateRepresentative.app (⟨P, hp⟩, ⟨Q, hq⟩))
    (fun M ↦ u.rho.app M) hunit
  intro P hp
  have hrep := congrArg Iso.hom (hr P A.mateUnitComplex hp hunit)
  change r.mateRepresentative.hom.app (⟨P, hp⟩, ⟨A.mateUnitComplex, hunit⟩) = _ at hrep
  exact (congrArg (fun t ↦ t ≫ u.rho.hom.app (DerivedCategory.Q.obj P)) hrep).trans
    (u.rho_normalized P ((mateFlatIndependent A P).1 hp).1
      ((mateFlatIndependent A P).1 hp).2)

end

private theorem mateUnitTransport
    {C D : Type*} [Category* C] [Category* D] [Preadditive C]
    (F : C ⥤ C ⥤ C) [F.Additive] [∀ U : C, (F.obj U).Additive]
    [∀ P Q : CochainComplex C ℤ, CochainComplex.HasMapBifunctor P Q F]
    (q : CochainComplex C ℤ ⥤ D) (S T : D × D ⥤ D)
    (flat : ObjectProperty (CochainComplex C ℤ)) (I : CochainComplex C ℤ)
    (mul : ∀ (P : CochainComplex C ℤ) (n : ℤ),
      (F.obj (P.X n)).obj (I.X 0) ⟶ P.X n)
    (a : ∀ (P Q : CochainComplex C ℤ) (_hp : flat P) (_hq : flat Q),
      q.obj (CochainComplex.mapBifunctor P Q F) ≅ S.obj (q.obj P, q.obj Q))
    (b : ∀ (P Q : CochainComplex C ℤ) (_hp : flat P) (_hq : flat Q),
      q.obj (CochainComplex.mapBifunctor P Q F) ≅ T.obj (q.obj P, q.obj Q))
    (z : S ≅ T)
    (hz : ∀ (P Q : flat.FullSubcategory),
      (a P.obj Q.obj P.property Q.property).hom ≫ z.hom.app
        (q.obj P.obj, q.obj Q.obj) = (b P.obj Q.obj P.property Q.property).hom)
    (rho : (Functor.curryObj T).flip.obj (q.obj I) ≅ 𝟭 D)
    (hb : MateCanonicalUnitData F q T flat I mul b (fun U ↦ rho.app U)) :
    MateCanonicalUnitData F q S flat I mul a
      (fun U ↦ ((mateFlipCurryIso z).app (q.obj I) ≪≫ rho).app U) := by
  obtain ⟨hi, hb⟩ := hb
  refine ⟨hi, ?_⟩
  intro P hp
  obtain ⟨j, hj, heq⟩ := hb P hp
  refine ⟨j, hj, ?_⟩
  change (a P I hp hi).hom ≫
    (z.hom.app (q.obj P, q.obj I) ≫ rho.hom.app (q.obj P)) = q.map j.hom
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t ↦ t ≫ rho.hom.app (q.obj P)) (hz ⟨P, hp⟩ ⟨I, hi⟩)).trans heq)

private def mateUncurryComparison {C D : Type*} [Category* C] [Category* D]
    (L : C ⥤ D) (TC : C × C ⥤ C) (TD : D × D ⥤ D)
    (mu : Functor.uncurry.obj (Functor.curryObj TC) ⋙ L ≅
      (L.prod L) ⋙ Functor.uncurry.obj (Functor.curryObj TD)) :
    TC ⋙ L ≅ (L.prod L) ⋙ TD :=
  Functor.isoWhiskerRight (Functor.currying.counitIso.app TC).symm L ≪≫ mu ≪≫
    Functor.isoWhiskerLeft (L.prod L) (Functor.currying.counitIso.app TD)

private theorem mateUncurryComparison_hom_app
    {C D : Type*} [Category* C] [Category* D]
    (L : C ⥤ D) (TC : C × C ⥤ C) (TD : D × D ⥤ D)
    (mu : Functor.uncurry.obj (Functor.curryObj TC) ⋙ L ≅
      (L.prod L) ⋙ Functor.uncurry.obj (Functor.curryObj TD)) (P : C × C) :
    (mateUncurryComparison L TC TD mu).hom.app P = mu.hom.app P := by
  change L.map (𝟙 (TC.obj P)) ≫ mu.hom.app P ≫
      𝟙 (TD.obj (L.obj P.1, L.obj P.2)) = mu.hom.app P
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact Category.comp_id (mu.hom.app P)

private def mateComparisonAt {C D : Type*} [Category* C] [Category* D]
    (L : C ⥤ D) (TC : C × C ⥤ C) (TD : D × D ⥤ D)
    (mu : TC ⋙ L ≅ (L.prod L) ⋙ TD) (U : C) :
    (Functor.curryObj TC).obj U ⋙ L ≅ L ⋙ (Functor.curryObj TD).obj (L.obj U) :=
  NatIso.ofComponents (fun V ↦ mu.app (U, V)) (by
    intro V V' f
    simpa [Functor.curryObj]
      using mu.hom.naturality (Prod.mkHom (𝟙 U) f))

private def mateComparisonFlipAt {C D : Type*} [Category* C] [Category* D]
    (L : C ⥤ D) (TC : C × C ⥤ C) (TD : D × D ⥤ D)
    (mu : TC ⋙ L ≅ (L.prod L) ⋙ TD) (V : C) :
    (Functor.curryObj TC).flip.obj V ⋙ L ≅ L ⋙ (Functor.curryObj TD).flip.obj (L.obj V) :=
  NatIso.ofComponents (fun U ↦ mu.app (U, V)) (by
    intro U U' f
    simpa [Functor.curryObj, Functor.flip_obj_map]
      using mu.hom.naturality (Prod.mkHom f (𝟙 V)))

private theorem mateLeftDerivedOnComplexes
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    (G : A ⥤ B) [G.Additive]
    (L : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Qh ⋙ L ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (.up ℤ))] :
    ∃ εc : DerivedCategory.Q ⋙ L ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q,
      L.IsLeftDerivedFunctor εc (HomologicalComplex.quasiIso A (.up ℤ)) ∧
      ∀ P, εc.app P = ε.app ((HomotopyCategory.quotient A (.up ℤ)).obj P) := by
  let π := HomotopyCategory.quotient A (.up ℤ)
  let εc : DerivedCategory.Q ⋙ L ⟶
      G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    { app := fun P ↦ ε.app (π.obj P)
      naturality := fun _ _ f ↦ ε.naturality (π.map f) }
  refine ⟨εc, ⟨⟨⟨?_⟩⟩⟩, fun _ ↦ rfl⟩
  let lift (Z : DerivedCategory A ⥤ DerivedCategory B)
      (τ : DerivedCategory.Q ⋙ Z ⟶
        G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) :
      DerivedCategory.Qh ⋙ Z ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
    { app := fun X ↦ τ.app X.as
      naturality := by
        intro X Y f
        obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
        obtain ⟨Y, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
        obtain ⟨f, rfl⟩ := π.map_surjective f
        exact τ.naturality f }
  refine IsTerminal.ofUniqueHom (fun Z ↦ CostructuredArrow.homMk
    (L.leftDerivedLift ε (HomotopyCategory.quasiIso A (.up ℤ)) Z.left
      (lift Z.left Z.hom)) (by
        apply NatTrans.ext
        funext P
        exact L.leftDerived_fac_app ε (HomotopyCategory.quasiIso A (.up ℤ))
          Z.left (lift Z.left Z.hom) (π.obj P))) ?_
  intro Z m
  apply CostructuredArrow.hom_ext
  apply L.leftDerived_ext ε (HomotopyCategory.quasiIso A (.up ℤ))
  apply NatTrans.ext
  funext X
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  have hm := NatTrans.congr_app m.w P
  have hm' : m.left.app (DerivedCategory.Q.obj P) ≫ ε.app (π.obj P) =
      Z.hom.app P := by simpa using hm
  exact hm'.trans
    (L.leftDerived_fac_app ε (HomotopyCategory.quasiIso A (.up ℤ))
      Z.left (lift Z.left Z.hom) (π.obj P)).symm


private theorem mateDerivedComplexComparisonApp
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    (G : A ⥤ B) [G.Additive] (L : DerivedCategory A ⥤ DerivedCategory B)
    (epsilon : DerivedCategory.Qh ⋙ L ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex A ℤ) :
    derivedPullbackComplexComparison G L epsilon P =
      epsilon.app ((HomotopyCategory.quotient A (.up ℤ)).obj P) := by
  change L.map (𝟙 (DerivedCategory.Q.obj P)) ≫
      epsilon.app ((HomotopyCategory.quotient A (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map (𝟙 ((HomotopyCategory.quotient B (.up ℤ)).obj
        ((G.mapHomologicalComplex (.up ℤ)).obj P))) ≫ (𝟙 _) = _
  erw [L.map_id, DerivedCategory.Qh.map_id, Category.id_comp,
    Category.id_comp, Category.comp_id]

private theorem mateCommShiftOfWhisker {C D E : Type*}
    [Category* C] [Category* D] [Category* E]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    (Q : C ⥤ D) [Q.CommShift ℤ] (hq : Function.Surjective Q.obj)
    {F G : D ⥤ E} [F.CommShift ℤ] [G.CommShift ℤ] (a : F ⟶ G)
    [NatTrans.CommShift (Functor.whiskerLeft Q a) ℤ] : NatTrans.CommShift a ℤ := by
  constructor
  intro n
  ext X
  obtain ⟨P, rfl⟩ := hq X
  apply (cancel_epi (F.map ((Q.commShiftIso n).hom.app P))).1
  have h := NatTrans.shift_app_comm (Functor.whiskerLeft Q a) n P
  simp only [Functor.commShiftIso_comp_hom_app, Functor.whiskerLeft_app,
    Category.assoc] at h
  rw [← a.naturality_assoc] at h
  exact h

private theorem mateEpsilonShift
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    (G : A ⥤ B) [G.Additive] (L : DerivedCategory A ⥤ DerivedCategory B)
    [L.CommShift ℤ]
    (epsilon : DerivedCategory.Qh ⋙ L ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (ec : DerivedCategory.Q ⋙ L ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    [NatTrans.CommShift ec ℤ]
    (hecapp : ∀ P, ec.app P = epsilon.app ((HomotopyCategory.quotient A (.up ℤ)).obj P)) :
    NatTrans.CommShift epsilon ℤ := by
  let pi := HomotopyCategory.quotient A (.up ℤ)
  let piB := HomotopyCategory.quotient B (.up ℤ)
  let GC := G.mapHomologicalComplex (.up ℤ)
  let GH := G.mapHomotopyCategory (.up ℤ)
  let iL := (Functor.associator pi DerivedCategory.Qh L).symm ≪≫
    Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A) L
  let iG := Functor.isoWhiskerLeft GC (DerivedCategory.quotientCompQhIso B).symm ≪≫
    (Functor.associator GC piB DerivedCategory.Qh).symm ≪≫
    Functor.isoWhiskerRight (G.mapHomotopyCategoryFactors (.up ℤ)).symm DerivedCategory.Qh ≪≫
    Functor.associator pi GH DerivedCategory.Qh
  let delta := iL.hom ≫ ec ≫ iG.hom
  have hd : delta = Functor.whiskerLeft pi epsilon := by
    ext P
    have hIL : iL.hom.app P = 𝟙 (L.obj (DerivedCategory.Q.obj P)) := by
      change (𝟙 _) ≫ L.map (𝟙 (DerivedCategory.Q.obj P)) = 𝟙 _
      rw [Category.id_comp]
      exact L.map_id _
    have hIG : iG.hom.app P = 𝟙 (DerivedCategory.Q.obj (GC.obj P)) := by
      change (𝟙 _) ≫ (𝟙 _) ≫ DerivedCategory.Qh.map (𝟙 (piB.obj (GC.obj P))) ≫
        (𝟙 _) = 𝟙 _
      rw [Category.id_comp, Category.id_comp, Category.comp_id]
      exact DerivedCategory.Qh.map_id _
    change iL.hom.app P ≫ ec.app P ≫ iG.hom.app P = epsilon.app (pi.obj P)
    erw [hIL, hIG, Category.id_comp, Category.comp_id]
    exact hecapp P
  have hdelta : NatTrans.CommShift delta ℤ := by
    dsimp only [delta, iL, iG]
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom]
    infer_instance
  have : NatTrans.CommShift (Functor.whiskerLeft pi epsilon) ℤ := hd ▸ hdelta
  exact mateCommShiftOfWhisker pi HomotopyCategory.quotient_obj_surjective epsilon

attribute [local semireducible] monoidalCategory

set_option maxHeartbeats 50000 in
-- Specialize the published unique comparison to the edge's normalized models.
private theorem matePullbackComparisonSquare
    {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X)
    (a : RingedTensorModel Y) (b : RingedTensorModel X)
    (P Q : CochainComplex Y.mateModules ℤ) (hp : Y.mateFlat P) (hq : Y.mateFlat Q) :
    ∃ (hp' : X.mateFlat ((e.pullback.mapHomologicalComplex (.up ℤ)).obj P))
      (hq' : X.mateFlat ((e.pullback.mapHomologicalComplex (.up ℤ)).obj Q)),
      e.left.map (a.mateRepresentative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
          (e.tensorComparison a b).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
          X.tensor.map (Prod.mkHom (derivedPullbackComplexComparison e.pullback e.left e.epsilon P)
            (derivedPullbackComplexComparison e.pullback e.left e.epsilon Q)) =
        derivedPullbackComplexComparison e.pullback e.left e.epsilon
            (CochainComplex.mapBifunctor P Q Y.mateTensor) ≫
          (DerivedCategory.Q.mapIso (e.ordinaryTensor.totalIso Y.ring X.ring e.inverseRing
            e.inverse e.algebraic e.ringMap e.pullback e.object_eq
            e.pushforward e.moduleAdjunction P Q)).inv ≫
          b.mateRepresentative.hom.app
            (⟨(e.pullback.mapHomologicalComplex (.up ℤ)).obj P, hp'⟩,
              ⟨(e.pullback.mapHomologicalComplex (.up ℤ)).obj Q, hq'⟩) := by
  have h := Classical.choose_spec (ringedTopoiCanonicalDerivedTensorPullback
    e.inverse e.direct e.adjunction e.algebraic e.ringMap e.pullback e.object_eq e.map_eq
    e.left e.epsilon e.isLeftDerived Y.mateFlat X.mateFlat (fun _ ↦ Iff.rfl)
    (fun _ ↦ Iff.rfl) Y.tensor X.tensor a.representative b.representative e.ordinaryTensor
    e.pushforward e.moduleAdjunction).2.exists
  delta RingedTensorModel.mateRepresentative RingedTensorCorner.mateTensor
    KFlatFixedTensor.ordinaryTensor RingedTensorEdge.tensorComparison
    ringedTopoiCanonicalDerivedTensorComparison
  exact h P Q hp hq

attribute [local irreducible] monoidalCategory

private theorem mateComparisonAtTransport {C D : Type*} [Category* C] [Category* D]
    (L : C ⥤ D) (TC TC0 : C × C ⥤ C) (TD TD0 : D × D ⥤ D)
    (zC : TC ≅ TC0) (zD : TD ≅ TD0)
    (mu : TC ⋙ L ≅ (L.prod L) ⋙ TD) (mu0 : TC0 ⋙ L ≅ (L.prod L) ⋙ TD0)
    (hmu : ∀ U V, L.map (zC.hom.app (U, V)) ≫ mu0.hom.app (U, V) =
      mu.hom.app (U, V) ≫ zD.hom.app (L.obj U, L.obj V)) (U : C) :
    mateComparisonAt L TC TD mu U =
      Functor.isoWhiskerRight ((Functor.curry.mapIso zC).app U) L ≪≫
        mateComparisonAt L TC0 TD0 mu0 U ≪≫
        Functor.isoWhiskerLeft L ((Functor.curry.mapIso zD).app (L.obj U)).symm := by
  apply Iso.ext
  ext V
  apply (cancel_mono (zD.hom.app (L.obj U, L.obj V))).1
  change mu.hom.app (U, V) ≫ zD.hom.app (L.obj U, L.obj V) =
    (L.map (zC.hom.app (U, V)) ≫ mu0.hom.app (U, V) ≫
      zD.inv.app (L.obj U, L.obj V)) ≫ zD.hom.app (L.obj U, L.obj V)
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id_app]
  exact (hmu U V).symm.trans
    (congrArg (fun t ↦ L.map (zC.hom.app (U, V)) ≫ t)
      (Category.comp_id (mu0.hom.app (U, V))).symm)

private theorem mateComparisonFlipAtTransport {C D : Type*} [Category* C] [Category* D]
    (L : C ⥤ D) (TC TC0 : C × C ⥤ C) (TD TD0 : D × D ⥤ D)
    (zC : TC ≅ TC0) (zD : TD ≅ TD0)
    (mu : TC ⋙ L ≅ (L.prod L) ⋙ TD) (mu0 : TC0 ⋙ L ≅ (L.prod L) ⋙ TD0)
    (hmu : ∀ U V, L.map (zC.hom.app (U, V)) ≫ mu0.hom.app (U, V) =
      mu.hom.app (U, V) ≫ zD.hom.app (L.obj U, L.obj V)) (V : C) :
    mateComparisonFlipAt L TC TD mu V =
      Functor.isoWhiskerRight
        (((flipFunctor _ _ _).mapIso (Functor.curry.mapIso zC)).app V) L ≪≫
        mateComparisonFlipAt L TC0 TD0 mu0 V ≪≫
        Functor.isoWhiskerLeft L
          (((flipFunctor _ _ _).mapIso (Functor.curry.mapIso zD)).app (L.obj V)).symm := by
  apply Iso.ext
  ext U
  apply (cancel_mono (zD.hom.app (L.obj U, L.obj V))).1
  change mu.hom.app (U, V) ≫ zD.hom.app (L.obj U, L.obj V) =
    (L.map (zC.hom.app (U, V)) ≫ mu0.hom.app (U, V) ≫
      zD.inv.app (L.obj U, L.obj V)) ≫ zD.hom.app (L.obj U, L.obj V)
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id_app]
  exact (hmu U V).symm.trans
    (congrArg (fun t ↦ L.map (zC.hom.app (U, V)) ≫ t)
      (Category.comp_id (mu0.hom.app (U, V))).symm)

private theorem mateComputationIsoExt (A : RingedTensorCorner.{u, w})
    (F G : CochainComplex A.mateModules ℤ ⥤ A.mateDerived) (c d : F ≅ G)
    (hinv : ∀ {P Q : CochainComplex A.mateModules ℤ} (p : P ⟶ Q),
      QuasiIso p → IsIso (F.map p))
    (hcd : ∀ (P : CochainComplex A.mateModules ℤ), A.mateFlat P → c.app P = d.app P) :
    c = d := by
  apply Iso.ext
  ext K
  obtain ⟨P, p, hp, hf, hq, _⟩ := mateFlatResolution A K
  let := hinv p hq
  apply (cancel_epi (F.map p)).1
  rw [c.hom.naturality, d.hom.naturality]
  exact congrArg (fun t ↦ t ≫ G.map p) (congrArg Iso.hom (hcd P ⟨hp, hf⟩))

private theorem mateExactShiftUnique (C : Type*) [Category* C] [Abelian C]
    [HasDerivedCategory.{w} C]
    (H : CochainComplex C ℤ ⥤ DerivedCategory C) [H.CommShift ℤ]
    (F : DerivedCategory C ⥤ DerivedCategory C) (s t : F.CommShift ℤ)
    (c : H ≅ DerivedCategory.Q ⋙ F)
    (hc : let := s; NatTrans.CommShift c.hom ℤ)
    (ht : let := t; NatTrans.CommShift c.hom ℤ)
    (hs : let := s; F.IsTriangulated) : let := t; F.IsTriangulated := by
  have heq : s = t := Functor.CommShift.eq_of_natTransCommShift
    DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ)) s t c.symm
    (by let := s; let := hc; infer_instance)
    (by let := t; let := ht; infer_instance)
  cases heq
  exact hs

set_option maxHeartbeats 500000 in
-- Compare the normalized fixed-factor computation maps before transporting exactness.
private theorem matePublishedExact (A : RingedTensorCorner.{u, w})
    [s : (KFlatFixedTensor.derivedTensor A.ring).CommShift₂Int]
    (hcan : PullbackTensorCanonical.HasCanonicalTensorShifts (R := A.ring)) :
    ∀ U : A.mateDerived,
      ((KFlatFixedTensor.derivedTensor A.ring).obj U).IsTriangulated ∧
        ((KFlatFixedTensor.derivedTensor A.ring).flip.obj U).IsTriangulated := by
  obtain ⟨s0, h0⟩ := KFlatFixedTensor.kFlat_fixed_tensor_triangulated A.ring
  let := s
  have hrep (P : CochainComplex A.mateModules ℤ) (hp : A.mateFlat P) :
      ((KFlatFixedTensor.derivedTensor A.ring).obj (DerivedCategory.Q.obj P)).IsTriangulated ∧
      ((KFlatFixedTensor.derivedTensor A.ring).flip.obj
        (DerivedCategory.Q.obj P)).IsTriangulated := by
    have hi := (mateFlatIndependent A P).1 hp
    have hfixed := h0 P hi.1 hi.2
    have hpres := hfixed.1
    have htri := hfixed.2.2.1
    obtain ⟨c0L, hc0L, hn0L⟩ := hfixed.2.2.2.1
    obtain ⟨c0R, hc0R, hn0R⟩ := hfixed.2.2.2.2.1
    have hcanonical := hcan P hi.1 hi.2
    obtain ⟨cL, hcL, hnL⟩ := hcanonical.1
    obtain ⟨cR, hcR, hnR⟩ := hcanonical.2
    have heL : c0L = cL := mateComputationIsoExt A _ _ c0L cL
      (fun f hf ↦ by
        change IsIso (DerivedCategory.Q.map
          (((KFlatFixedTensor.totalTensor A.ring).obj P).map f))
        exact (DerivedCategory.isIso_Q_map_iff_quasiIso A.mateModules _).2
          (hpres _ _ f hf).1) (fun Q hq ↦ by
          have hqi := (mateFlatIndependent A Q).1 hq
          exact (hn0L Q hqi.1 hqi.2).trans (hnL Q hqi.1 hqi.2).symm)
    have heR : c0R = cR := mateComputationIsoExt A _ _ c0R cR
      (fun f hf ↦ by
        change IsIso (DerivedCategory.Q.map
          (((KFlatFixedTensor.totalTensor A.ring).flip.obj P).map f))
        exact (DerivedCategory.isIso_Q_map_iff_quasiIso A.mateModules _).2
          (hpres _ _ f hf).2) (fun Q hq ↦ by
          have hqi := (mateFlatIndependent A Q).1 hq
          exact (hn0R Q hqi.1 hqi.2).trans (hnR Q hqi.1 hqi.2).symm)
    have hcL' : NatTrans.CommShift c0L.hom ℤ := by rw [heL]; exact hcL
    have hcR' : NatTrans.CommShift c0R.hom ℤ := by rw [heR]; exact hcR
    constructor
    · exact mateExactShiftUnique A.mateModules _ _ (s0.commShiftObj _)
        inferInstance c0L hc0L hcL' htri.1
    · exact mateExactShiftUnique A.mateModules _ _ (s0.commShiftFlipObj _)
        inferInstance c0R hc0R hcR' htri.2
  intro U
  let K := (DerivedCategory.Q (C := A.mateModules)).objPreimage U
  obtain ⟨P, p, hp, hf, hq, _⟩ := mateFlatResolution A K
  let := hq
  let z : DerivedCategory.Q.obj P ≅ U := asIso (DerivedCategory.Q.map p) ≪≫
    (DerivedCategory.Q (C := A.mateModules)).objObjPreimageIso U
  obtain ⟨hl, hr⟩ := hrep P ⟨hp, hf⟩
  let := hl
  let := hr
  constructor
  · let : NatTrans.CommShift
        ((KFlatFixedTensor.derivedTensor A.ring).mapIso z).hom ℤ :=
      s.commShift_map z.hom
    exact Functor.isTriangulated_of_iso ((KFlatFixedTensor.derivedTensor A.ring).mapIso z)
  · let : NatTrans.CommShift
        ((KFlatFixedTensor.derivedTensor A.ring).flip.mapIso z).hom ℤ :=
      s.commShift_flip_map z.hom
    exact Functor.isTriangulated_of_iso ((KFlatFixedTensor.derivedTensor A.ring).flip.mapIso z)

set_option maxHeartbeats 50000 in
-- Elaboration must compare the large two-variable localization interfaces.
private theorem mateLeftDerivedExact
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    (G : A ⥤ B) [G.Additive] (L : DerivedCategory A ⥤ DerivedCategory B)
    [L.CommShift ℤ]
    (epsilon : DerivedCategory.Qh ⋙ L ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor epsilon (HomotopyCategory.quasiIso A (.up ℤ))]
    (S : ObjectProperty (CochainComplex A ℤ))
    (hresC : ∀ K0 : CochainComplex A ℤ,
      ∃ (K : CochainComplex A ℤ) (p : K ⟶ K0), S K ∧ QuasiIso p)
    (hpres : ∀ {P Q : CochainComplex A ℤ} (g : P ⟶ Q),
      S P → S Q → QuasiIso g → QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map g))
    (hcounit : NatTrans.CommShift epsilon ℤ) : L.IsTriangulated := by
  classical
  let F := G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let W := HomotopyCategory.quasiIso A (.up ℤ)
  have hkan : L.IsRightKanExtension epsilon :=
    Functor.IsLeftDerivedFunctor.isRightKanExtension L epsilon W
  let P : Set (HomotopyCategory A (.up ℤ)) :=
    { T | ∃ K : CochainComplex A ℤ,
      (HomotopyCategory.quotient A (.up ℤ)).obj K = T ∧ S K }
  have hres : ∀ T : HomotopyCategory A (.up ℤ),
      ∃ (T' : HomotopyCategory A (.up ℤ)) (s : T' ⟶ T), T' ∈ P ∧ W s := by
    intro T
    obtain ⟨K0, rfl⟩ := HomotopyCategory.quotient_obj_surjective T
    obtain ⟨K, s, hk, hs⟩ := hresC K0
    exact ⟨_, (HomotopyCategory.quotient A (.up ℤ)).map s, ⟨K, rfl, hk⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  have hinv : ∀ T T' : HomotopyCategory A (.up ℤ), ∀ s : T ⟶ T',
      T ∈ P → T' ∈ P → W s → IsIso (F.map s) := by
    intro T T' s hT hT' hs
    obtain ⟨K, rfl, hk⟩ := hT
    obtain ⟨K', rfl, hk'⟩ := hT'
    obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient A (.up ℤ)).map_surjective s
    have hg := (HomotopyCategory.quotient_map_mem_quasiIso_iff g).1 hs
    have hpg := hpres g hk hk' hg
    dsimp only [F, Functor.comp_map, Functor.mapHomotopyCategory_map]
    exact Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso B (.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hpg)
  obtain ⟨hl, hr, ht, hs, htwo, _, _, _, _⟩ :=
    HomotopyCategory.quasiIso_saturated_triangulated A
  let : W.HasLeftCalculusOfFractions := hl
  let : W.HasRightCalculusOfFractions := hr
  let : W.HasTwoOutOfThreeProperty := htwo
  have hW : W.IsSaturatedTriangulatedMultiplicativeSystem :=
    ⟨⟨⟨hl, hr⟩, fun _ _ _ _ f g k ↦ hs _ _ _ _ g f k⟩, ht⟩
  have hdefined : ∀ T, F.IsTriangulatedLeftDerivedDefinedAt W hW T := by
    intro T
    obtain ⟨T', _, hc, _, _⟩ :=
      Functor.resolvingClass_essentialConstancy W F P hres hinv T
    exact ⟨T', hc⟩
  have hsource : (DerivedCategory.Qh ⋙ L).IsTriangulated := by
    constructor
    intro T hT
    exact Functor.leftDerived_kan_map_source_distinguished _ _ _ F W hW
      DerivedCategory.Qh L epsilon hkan hdefined hcounit T hT
  let : (DerivedCategory.Qh ⋙ L).IsTriangulated := hsource
  let := Localization.essSurj_mapArrow (DerivedCategory.Qh (C := A)) W
  exact Functor.isTriangulated_of_precomp DerivedCategory.Qh L

private theorem matePullbackExact
    {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X) [e.left.CommShift ℤ]
    (hcounit : NatTrans.CommShift e.epsilon ℤ) : e.left.IsTriangulated := by
  let data := ringedTopoiDerivedPullback e.inverse e.direct e.adjunction
    e.algebraic e.ringMap e.pullback e.object_eq e.map_eq
  let := e.isLeftDerived
  apply mateLeftDerivedExact e.pullback e.left e.epsilon Y.mateFlat ?_ ?_ hcounit
  · intro K0
    obtain ⟨K, p, hk, hf, hs, _⟩ := mateFlatResolution Y K0
    exact ⟨K, p, ⟨hk, hf⟩, hs⟩
  · intro P Q g hp hq hs
    exact data.choose_spec.choose_spec.2.2.1 g hp.1 hp.2 hq.1 hq.2 hs

private def mateTriangleMap {C D : Type*} [Category* C] [Category* D]
    [HasShift C ℤ] [HasShift D ℤ] {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
    (a : F ⟶ G) [NatTrans.CommShift a ℤ] (T : Triangle C) :
    F.mapTriangle.obj T ⟶ G.mapTriangle.obj T where
  hom₁ := a.app T.obj₁
  hom₂ := a.app T.obj₂
  hom₃ := a.app T.obj₃
  comm₁ := a.naturality T.mor₁
  comm₂ := a.naturality T.mor₂
  comm₃ := by
    change (F.map T.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁) ≫
        (shiftFunctor D (1 : ℤ)).map (a.app T.obj₁) =
      a.app T.obj₃ ≫ G.map T.mor₃ ≫ (G.commShiftIso (1 : ℤ)).hom.app T.obj₁
    rw [Category.assoc, NatTrans.shift_app_comm, ← Category.assoc,
      a.naturality, Category.assoc]

-- Unit comparisons below use the definitional identification with the ring complex.
attribute [local semireducible] monoidalCategory

-- The formal mate assembly needs extra elaboration for the large normalized interface.
private theorem mateComparisonSquareEquation
    {C : Type*} [Category* C] {A Y Y0 B0 B1 B2 B3 B4 : C}
    (p : A ⟶ Y) [Epi p] (p0 : A ⟶ Y0) (z : Y ⟶ Y0)
    (m : Y ⟶ B1) (m0 : Y0 ⟶ B2)
    (f : B1 ⟶ B3) (f0 : B2 ⟶ B4) [Mono f0]
    (zL : B1 ⟶ B2) (zP : B3 ⟶ B4)
    (k : A ⟶ B0) (s : B0 ⟶ B3) (s0 : B0 ⟶ B4)
    (hpre : p ≫ z = p0) (hpost : s ≫ zP = s0)
    (hnat : f ≫ zP = zL ≫ f0)
    (hnorm : p ≫ m ≫ f = k ≫ s) (hnorm0 : p0 ≫ m0 ≫ f0 = k ≫ s0) :
    z ≫ m0 = m ≫ zL := by
  apply (cancel_epi p).1
  apply (cancel_mono f0).1
  simp only [Category.assoc]
  rw [← Category.assoc p z, hpre, hnorm0, ← hnat]
  rw [← Category.assoc m f, ← Category.assoc p (m ≫ f), hnorm,
    Category.assoc, hpost]

private theorem mateWhiskeredComparisonCommShift
    {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
    (L : C ⥤ D) [L.CommShift ℤ]
    {F F0 : C ⥤ C} {G G0 : D ⥤ D}
    [F.CommShift ℤ] [F0.CommShift ℤ] [G.CommShift ℤ] [G0.CommShift ℤ]
    (a : F ≅ F0) (b : F0 ⋙ L ≅ L ⋙ G0) (c : G ≅ G0)
    [NatTrans.CommShift a.hom ℤ] [NatTrans.CommShift b.hom ℤ]
    [NatTrans.CommShift c.hom ℤ] :
    NatTrans.CommShift
      (Functor.isoWhiskerRight a L ≪≫ b ≪≫ Functor.isoWhiskerLeft L c.symm).hom ℤ := by
  change NatTrans.CommShift
    (Functor.whiskerRight a.hom L ≫ b.hom ≫ Functor.whiskerLeft L c.inv) ℤ
  infer_instance

private theorem mateNormalizationSquare {C : Type*} [Category* C]
    {A B D E F : C} {p p' : A ⟶ B} {m m' : B ⟶ D} {f f' : D ⟶ E}
    {k k' : A ⟶ F} {s s' : F ⟶ E}
    (hp : p = p') (hm : m = m') (hf : f = f') (hk : k = k') (hs : s = s')
    (h : p' ≫ m' ≫ f' = k' ≫ s') : p ≫ m ≫ f = k ≫ s := by
  exact (congrArg₂ (fun x y ↦ x ≫ y) hp
    (congrArg₂ (fun x y ↦ x ≫ y) hm hf)).trans
    (h.trans (congrArg₂ (fun x y ↦ x ≫ y) hk hs).symm)

private theorem mateUnitTransportEquation {C D : Type*} [Category* C] [Category* D]
    (L : C ⥤ D) {U V W : C} {A B E F : D}
    (a : U ⟶ V) (r : V ⟶ W) (m : L.obj U ⟶ A) (m0 : L.obj V ⟶ E)
    (f : A ⟶ B) (f0 : E ⟶ F) (z0 : A ⟶ E) (z1 : B ⟶ F) (r0 : F ⟶ L.obj W)
    (hm : L.map a ≫ m0 = m ≫ z0) (hn : f ≫ z1 = z0 ≫ f0)
    (hu : m0 ≫ f0 ≫ r0 = L.map r) : m ≫ f ≫ (z1 ≫ r0) = L.map (a ≫ r) := by
  rw [L.map_comp]
  rw [← Category.assoc f z1 r0, hn]
  simp only [Category.assoc]
  rw [← Category.assoc m z0 (f0 ≫ r0), ← hm]
  simp only [Category.assoc]
  rw [hu]

private theorem mateUncurriedComparisonNaturality
    {C D : Type*} [Category* C] [Category* D]
    (TC : C × C ⥤ C) (TD : D × D ⥤ D) (L : C ⥤ D)
    (c : TC ⋙ L ≅ (L.prod L) ⋙ TD)
    (U U' V V' : C) (f : U ⟶ U') (g : V ⟶ V') :
    L.map (((Functor.curryObj TC).map f).app V ≫
      ((Functor.curryObj TC).obj U').map g) ≫ (c.app (U', V')).hom =
      (c.app (U, V)).hom ≫
        ((Functor.curryObj TD).map (L.map f)).app (L.obj V) ≫
        ((Functor.curryObj TD).obj (L.obj U')).map (L.map g) := by
  change L.map (TC.map (Prod.mkHom f (𝟙 V)) ≫
    TC.map (Prod.mkHom (𝟙 U') g)) ≫ (c.app (U', V')).hom =
      (c.app (U, V)).hom ≫ TD.map (Prod.mkHom (L.map f) (𝟙 _)) ≫
        TD.map (Prod.mkHom (𝟙 _) (L.map g))
  simpa only [Iso.app_hom, Functor.comp_map, Functor.prod_map,
    ← CategoryTheory.Functor.map_comp, CategoryTheory.prod_comp,
    Category.comp_id, Category.id_comp] using c.hom.naturality (Prod.mkHom f g)

private theorem mateFormalProjection
    {C D : Type*} [Category* C] [Category* D]
    (L : C ⥤ D) (R : D ⥤ C) (adj : L ⊣ R)
    (TC : C × C ⥤ C) (TD : D × D ⥤ D)
    (c : TC ⋙ L ≅ (L.prod L) ⋙ TD) (E : D) (P : C) :
    formalProjectionAlpha (Functor.curryObj TC) (Functor.curryObj TD) L R adj
        (fun U V ↦ c.app (U, V)) E P =
      derivedProjectionFormulaMate L R adj TC TD c E P := by
  change adj.unit.app _ ≫ R.map ((c.app (R.obj E, P)).hom ≫
      TD.map (Prod.mkHom (adj.counit.app E) (𝟙 (L.obj P)))) =
    adj.homEquiv _ _ ((c.hom.app (R.obj E, P) ≫ 𝟙 _) ≫
      TD.map (Prod.mkHom (adj.counit.app E) (𝟙 (L.obj P))))
  rw [Category.comp_id, Adjunction.homEquiv_unit]
  simp only [Iso.app_hom]

private theorem mateFormalExactProjection
    (C D : Type*) [Category* C] [Category* D]
    [HasZeroObject C] [HasZeroObject D] [Preadditive C] [Preadditive D]
    [HasShift C ℤ] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D] [IsTriangulated C] [IsTriangulated D]
    (TC : C × C ⥤ C) (TD : D × D ⥤ D)
    [(Functor.curryObj TC).CommShift₂Int] [(Functor.curryObj TD).CommShift₂Int]
    [∀ U : C, ((Functor.curryObj TC).obj U).IsTriangulated]
    [∀ U : C, ((Functor.curryObj TC).flip.obj U).IsTriangulated]
    [∀ U : D, ((Functor.curryObj TD).obj U).IsTriangulated]
    [∀ U : D, ((Functor.curryObj TD).flip.obj U).IsTriangulated]
    (L : C ⥤ D) (R : D ⥤ C) [L.CommShift ℤ] [R.CommShift ℤ]
    [L.IsTriangulated] [R.IsTriangulated] (adj : L ⊣ R) [adj.CommShift ℤ]
    (oneC : C) (oneD : D)
    (rhoY : (Functor.curryObj TC).flip.obj oneC ≅ 𝟭 C)
    (rhoX : (Functor.curryObj TD).flip.obj oneD ≅ 𝟭 D)
    (c : TC ⋙ L ≅ (L.prod L) ⋙ TD)
    (hs₂ : ∀ (n : ℤ) (U V : C),
        c.hom.app (U, V⟦n⟧) ≫
            TD.map (Prod.mkHom (𝟙 (L.obj U))
              ((L.commShiftIso n).hom.app V)) ≫
            (((Functor.curryObj TD).obj (L.obj U)).commShiftIso n).hom.app
              (L.obj V) =
          L.map ((((Functor.curryObj TC).obj U).commShiftIso n).hom.app V) ≫
            (L.commShiftIso n).hom.app (TC.obj (U, V)) ≫
            (shiftFunctor D n).map (c.hom.app (U, V)))
    (hs₁ : ∀ (n : ℤ) (U V : C),
        c.hom.app (U⟦n⟧, V) ≫
            TD.map (Prod.mkHom ((L.commShiftIso n).hom.app U)
              (𝟙 (L.obj V))) ≫
            (((Functor.curryObj TD).flip.obj (L.obj V)).commShiftIso n).hom.app
              (L.obj U) =
          L.map ((((Functor.curryObj TC).flip.obj V).commShiftIso n).hom.app U) ≫
            (L.commShiftIso n).hom.app (TC.obj (U, V)) ≫
            (shiftFunctor D n).map (c.hom.app (U, V)))
    (unitL : L.obj oneC ≅ oneD)
    (hunit : ∀ U : C, c.hom.app (U, oneC) ≫
      TD.map (Prod.mkHom (𝟙 (L.obj U)) unitL.hom) ≫ rhoX.hom.app (L.obj U) =
        L.map (rhoY.hom.app U)) :
∃ alpha : ∀ E : D,
          (Functor.curryObj TC).obj (R.obj E) ⟶
            L ⋙ (Functor.curryObj TD).obj E ⋙ R,
          (∀ (E : D) (P : C), (alpha E).app P =
            derivedProjectionFormulaMate L R adj TC TD
              c E P) ∧
          (∀ E : D,
            (L ⋙ (Functor.curryObj TD).obj E ⋙ R).IsTriangulated ∧
              NatTrans.CommShift (alpha E) ℤ) ∧
          (∀ (E : D) (T : Triangle C), T ∈ distTriang C →
            ∃ m : (Functor.mapTriangle
                ((Functor.curryObj TC).obj (R.obj E))).obj T ⟶
                (Functor.mapTriangle
                  (L ⋙ (Functor.curryObj TD).obj E ⋙ R)).obj T,
              m.hom₁ = (alpha E).app T.obj₁ ∧ m.hom₂ = (alpha E).app T.obj₂ ∧
                m.hom₃ = (alpha E).app T.obj₃) ∧
          (∀ (E E' : D) (q : E ⟶ E') (P : C),
            ((Functor.curryObj TC).map (R.map q)).app P ≫ (alpha E').app P =
              (alpha E).app P ≫
                (Functor.whiskerRight (Functor.whiskerLeft L
                  ((Functor.curryObj TD).map q)) R).app P) ∧
          (∀ E : D,
            (alpha E).app oneC ≫
              R.map (TD.map (Prod.mkHom (𝟙 E) unitL.hom) ≫ rhoX.hom.app E) =
                rhoY.hom.app (R.obj E)) := by
  let mu (U V : C) := c.app (U, V)
  have hmunat (U U' V V' : C) (f : U ⟶ U') (g : V ⟶ V') :
      L.map (((Functor.curryObj TC).map f).app V ≫
        ((Functor.curryObj TC).obj U').map g) ≫ (mu U' V').hom =
      (mu U V).hom ≫
        ((Functor.curryObj TD).map (L.map f)).app (L.obj V) ≫
        ((Functor.curryObj TD).obj (L.obj U')).map (L.map g) := by
    exact mateUncurriedComparisonNaturality TC TD L
      c U U' V V' f g
  obtain ⟨_, hnat, hshift, _, hunit'⟩ := formalExactProjectionMate
    C D (Functor.curryObj TC) (Functor.curryObj TD)
    oneC oneD rhoY rhoX L R adj mu hmunat
    (fun U V n ↦ by simpa only [mu, Iso.app_hom, Functor.curryObj] using hs₁ n U V)
    (fun U V n ↦ by simpa only [mu, Iso.app_hom, Functor.curryObj] using hs₂ n U V) unitL
    (fun U ↦ by simpa only [mu, Iso.app_hom, Functor.curryObj] using hunit U)
  let alpha (E : D) : (Functor.curryObj TC).obj (R.obj E) ⟶
      L ⋙ (Functor.curryObj TD).obj E ⋙ R := {
    app P := formalProjectionAlpha (Functor.curryObj TC)
      (Functor.curryObj TD) L R adj mu E P
    naturality := by
      intro P P' f
      have h := hnat E E P P' (𝟙 E) f
      rw [R.map_id, (Functor.curryObj TC).map_id,
        (Functor.curryObj TD).map_id] at h
      simpa only [NatTrans.id_app, Category.id_comp, Functor.comp_map] using h }
  have happ (E : D) (P : C) :
      (alpha E).app P = formalProjectionAlpha (Functor.curryObj TC)
        (Functor.curryObj TD) L R adj mu E P := rfl
  have hcomm (E : D) : NatTrans.CommShift (alpha E) ℤ := by
    constructor
    intro n
    ext P
    simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      happ, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
          Functor.commShiftIso_comp_hom_app, Functor.comp_obj,
      Functor.comp_map, CategoryTheory.Functor.map_comp, Category.assoc] using (hshift E n P).symm
  have halpha (E : D) (P : C) :
      (alpha E).app P = derivedProjectionFormulaMate L R adj
        TC TD c E P := by
    exact (happ E P).trans (mateFormalProjection L R adj
      TC TD c E P)
  refine ⟨alpha, halpha, ?_, ?_, ?_, ?_⟩
  · intro E
    exact ⟨inferInstance, hcomm E⟩
  · intro E T _
    let := hcomm E
    exact ⟨mateTriangleMap (alpha E) T, rfl, rfl, rfl⟩
  · intro E E' q P
    have h := hnat E E' P P q (𝟙 P)
    rw [((Functor.curryObj TC).obj (R.obj E')).map_id,
      L.map_id, ((Functor.curryObj TD).obj E').map_id] at h
    simpa only [happ, Category.id_comp, Category.comp_id, Functor.comp_map,
      Functor.whiskerRight_app,
      Functor.whiskerLeft_app] using h
  · intro E
    simpa only [happ, Functor.curryObj, Iso.app_hom] using hunit' E


private def MateProjectionStructureData
    {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X)
    (a : RingedTensorModel Y) (b : RingedTensorModel X) : Prop :=
  ∃ (_ : (Functor.curryObj Y.tensor).CommShift₂Int)
      (_ : (Functor.curryObj X.tensor).CommShift₂Int) (_ : e.left.CommShift ℤ),
      a.MateCanonicalShifts ∧ b.MateCanonicalShifts ∧
      NatTrans.CommShift e.epsilon ℤ ∧ e.left.IsTriangulated ∧
      (∀ U : Y.mateDerived, ((Functor.curryObj Y.tensor).obj U).IsTriangulated ∧
        ((Functor.curryObj Y.tensor).flip.obj U).IsTriangulated) ∧
      (∀ U : X.mateDerived, ((Functor.curryObj X.tensor).obj U).IsTriangulated ∧
        ((Functor.curryObj X.tensor).flip.obj U).IsTriangulated) ∧
      (∀ (n : ℤ) (U V : Y.mateDerived),
        (e.tensorComparison a b).hom.app (U, V⟦n⟧) ≫
            X.tensor.map (Prod.mkHom (𝟙 (e.left.obj U))
              ((e.left.commShiftIso n).hom.app V)) ≫
            (((Functor.curryObj X.tensor).obj (e.left.obj U)).commShiftIso n).hom.app
              (e.left.obj V) =
          e.left.map ((((Functor.curryObj Y.tensor).obj U).commShiftIso n).hom.app V) ≫
            (e.left.commShiftIso n).hom.app (Y.tensor.obj (U, V)) ≫
            (shiftFunctor X.mateDerived n).map ((e.tensorComparison a b).hom.app (U, V))) ∧
      (∀ (n : ℤ) (U V : Y.mateDerived),
        (e.tensorComparison a b).hom.app (U⟦n⟧, V) ≫
            X.tensor.map (Prod.mkHom ((e.left.commShiftIso n).hom.app U)
              (𝟙 (e.left.obj V))) ≫
            (((Functor.curryObj X.tensor).flip.obj (e.left.obj V)).commShiftIso n).hom.app
              (e.left.obj U) =
          e.left.map ((((Functor.curryObj Y.tensor).flip.obj V).commShiftIso n).hom.app U) ≫
            (e.left.commShiftIso n).hom.app (Y.tensor.obj (U, V)) ≫
            (shiftFunctor X.mateDerived n).map ((e.tensorComparison a b).hom.app (U, V))) ∧
      ∃ (unitL : e.left.obj Y.mateUnit ≅ X.mateUnit)
        (rhoY : (Functor.curryObj Y.tensor).flip.obj Y.mateUnit ≅ 𝟭 Y.mateDerived)
        (rhoX : (Functor.curryObj X.tensor).flip.obj X.mateUnit ≅ 𝟭 X.mateDerived),
        a.MateCanonicalUnit (fun U ↦ rhoY.app U) ∧
        b.MateCanonicalUnit (fun U ↦ rhoX.app U) ∧
        (∀ U : Y.mateDerived,
          (e.tensorComparison a b).hom.app (U, Y.mateUnit) ≫
            X.tensor.map (Prod.mkHom (𝟙 (e.left.obj U)) unitL.hom) ≫
            rhoX.hom.app (e.left.obj U) = e.left.map (rhoY.hom.app U))

attribute [local irreducible] MateProjectionStructureData

set_option maxHeartbeats 1500000 in
-- Normalize the two-variable localization interfaces and transport all exact structures.
private theorem mateProjectionStructures
    {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X)
    (a : RingedTensorModel Y) (b : RingedTensorModel X) : MateProjectionStructureData e a b := by
  let f : CategoryTheory.CochainPullback.RingedPullback.{u, u, u, u, u} Y.ring X.ring := {
    uInv := e.inverse
    uPush := e.direct
    adj := e.adjunction
    finiteLimits := e.finiteLimits
    RI := e.inverseRing
    I := e.algebraic
    coefficient := e.ringMap
    L := e.pullback
    hobj := e.object_eq
    hmap := e.map_eq
    V := e.pushforward
    moduleAdj := e.moduleAdjunction }
  let k : CategoryTheory.CochainPullback.Comparison.{u, u, u, u, u} f := {
    q := fun M ↦ e.ordinaryTensor.q M
    q_one := fun M W m ↦ e.ordinaryTensor.q_one M W m
    mu := fun M N ↦ e.ordinaryTensor.mu M N
    naturality := fun f g ↦ e.ordinaryTensor.naturality f g
    pure := fun M N Z x y z ↦ e.ordinaryTensor.pure M N Z x y z }
  let := e.isLeftDerived
  obtain ⟨ec, hec, hecapp⟩ := mateLeftDerivedOnComplexes e.pullback e.left e.epsilon
  obtain ⟨sL, sY0, sX0, hecs, hcanY, hcanX, hiso, muCurried, hnorm0,
    hunique, uY, uX, unitL0, hsubY, hsubX, hunitL, hshift₁, hshift₂, hunit, _⟩ :=
    PullbackTensorCanonical.pullback_tensor_canonical_shift_unit f k e.left ec hec
  let unitL : e.left.obj Y.mateUnit ≅ X.mateUnit := unitL0
  let := sL
  let := sY0
  let := sX0
  let : (Functor.curryObj
      (siteDerivedTensorIndependentCoefficients.{u, u, u, w} Y.topology Y.ring)).CommShift₂Int :=
    sY0
  let : (Functor.curryObj
      (siteDerivedTensorIndependentCoefficients.{u, u, u, w} X.topology X.ring)).CommShift₂Int :=
    sX0
  obtain ⟨⟨rY, ha0, hrY⟩⟩ := matePublishedDataExists Y hcanY
  obtain ⟨⟨rX, hb0, hrX⟩⟩ := matePublishedDataExists X hcanX
  let a0 := rY
  let b0 := rX
  let mu0 := mateUncurryComparison e.left
    (siteDerivedTensorIndependentCoefficients.{u, u, u, w} Y.topology Y.ring)
    (siteDerivedTensorIndependentCoefficients.{u, u, u, w} X.topology X.ring) muCurried
  have hmu0app (P : Y.mateDerived × Y.mateDerived) :
      mu0.hom.app P = muCurried.hom.app P :=
    mateUncurryComparison_hom_app _ _ _ _ P
  obtain ⟨ffY⟩ := mateResolvingFF Y Y.mateDerived
  obtain ⟨ffX⟩ := mateResolvingFF X X.mateDerived
  obtain ⟨zY, hzY0⟩ := mateLiftModelIso
    ((Y.mateFlat.ι ⋙ DerivedCategory.Q).prod (Y.mateFlat.ι ⋙ DerivedCategory.Q))
    Y.tensor _ ffY
    a.mateRepresentative a0.mateRepresentative
  obtain ⟨zX, hzX0⟩ := mateLiftModelIso
    ((X.mateFlat.ι ⋙ DerivedCategory.Q).prod (X.mateFlat.ι ⋙ DerivedCategory.Q))
    X.tensor _ ffX
    b.mateRepresentative b0.mateRepresentative
  have hzY := fun (P Q : Y.mateFlat.FullSubcategory) ↦ hzY0 (P, Q)
  have hzX := fun (P Q : X.mateFlat.FullSubcategory) ↦ hzX0 (P, Q)
  obtain ⟨sY, hcYL, hcYR⟩ := mateTensorShiftOfIso Y.tensor _ zY
  obtain ⟨sX, hcXL, hcXR⟩ := mateTensorShiftOfIso X.tensor _ zX
  let := sY
  let := sX
  have ha : a.MateCanonicalShifts := mateCanonicalShiftTransport
    Y.mateTensor DerivedCategory.Q Y.tensor _ Y.mateFlat
    (fun P Q hp hq ↦ a.mateRepresentative.app (⟨P, hp⟩, ⟨Q, hq⟩))
    (fun P Q hp hq ↦ a0.mateRepresentative.app (⟨P, hp⟩, ⟨Q, hq⟩))
    zY hzY hcYL hcYR ha0
  have hb : b.MateCanonicalShifts := mateCanonicalShiftTransport
    X.mateTensor DerivedCategory.Q X.tensor _ X.mateFlat
    (fun P Q hp hq ↦ b.mateRepresentative.app (⟨P, hp⟩, ⟨Q, hq⟩))
    (fun P Q hp hq ↦ b0.mateRepresentative.app (⟨P, hp⟩, ⟨Q, hq⟩))
    zX hzX hcXL hcXR hb0
  have hecDerived (P : CochainComplex Y.mateModules ℤ) :
      ec.app P = derivedPullbackComplexComparison e.pullback e.left e.epsilon P :=
    (hecapp P).trans (mateDerivedComplexComparisonApp e.pullback e.left e.epsilon P).symm
  have hmuNat : Functor.whiskerRight zY.hom e.left ≫ mu0.hom =
      (e.tensorComparison a b).hom ≫ Functor.whiskerLeft (e.left.prod e.left) zX.hom := by
    obtain ⟨ff⟩ := mateResolvingFF Y X.mateDerived
    apply ff.map_injective
    ext PQ
    obtain ⟨P, Q⟩ := PQ
    have hp := (mateFlatIndependent Y P.obj).1 P.property
    have hq := (mateFlatIndependent Y Q.obj).1 Q.property
    let normalized := hnorm0 P.obj Q.obj hp.1 hq.1 hp.2 hq.2
    have hn0 := normalized.choose_spec.choose_spec.choose_spec.choose_spec
    let comparison := matePullbackComparisonSquare e a b P.obj Q.obj
      P.property Q.property
    have hp' := comparison.choose
    have hq' := comparison.choose_spec.choose
    have hn := comparison.choose_spec.choose_spec
    let := hiso P.obj hp.1 hp.2
    let := hiso Q.obj hq.1 hq.2
    have hisopair : IsIso (Prod.mkHom (ec.app P.obj) (ec.app Q.obj)) :=
      (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
    have hz := zX.hom.naturality (Prod.mkHom (ec.app P.obj) (ec.app Q.obj))
    have hepair : Prod.mkHom (ec.app P.obj) (ec.app Q.obj) =
        Prod.mkHom (derivedPullbackComplexComparison e.pullback e.left e.epsilon P.obj)
          (derivedPullbackComplexComparison e.pullback e.left e.epsilon Q.obj) :=
      congrArg₂ (fun x y ↦ Prod.mkHom x y) (hecDerived P.obj) (hecDerived Q.obj)
    have hyr := congrArg Iso.hom (hrY P.obj Q.obj P.property Q.property)
    have hxr := congrArg Iso.hom (hrX
      ((e.pullback.mapHomologicalComplex (.up ℤ)).obj P.obj)
      ((e.pullback.mapHomologicalComplex (.up ℤ)).obj Q.obj) hp' hq')
    have hcomparison : DerivedCategory.Q.map
        (CategoryTheory.CochainPullback.comparison f k P.obj Q.obj).hom =
        (DerivedCategory.Q.mapIso (e.ordinaryTensor.totalIso Y.ring X.ring e.inverseRing
          e.inverse e.algebraic e.ringMap e.pullback e.object_eq
          e.pushforward e.moduleAdjunction P.obj Q.obj)).inv := by
      have h : (CategoryTheory.CochainPullback.comparison f k P.obj Q.obj).symm =
          e.ordinaryTensor.totalIso Y.ring X.ring e.inverseRing
            e.inverse e.algebraic e.ringMap e.pullback e.object_eq
            e.pushforward e.moduleAdjunction P.obj Q.obj := by
        apply Iso.ext
        rfl
      exact congrArg (fun z ↦ (DerivedCategory.Q.mapIso z).inv) h
    change e.left.map (zY.hom.app _) ≫ mu0.hom.app _ =
      (e.tensorComparison a b).hom.app _ ≫ zX.hom.app _
    refine mateComparisonSquareEquation
      (e.left.map (a.mateRepresentative.hom.app (P, Q)))
      (e.left.map (rY.mateRepresentative.hom.app (P, Q)))
      (e.left.map (zY.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)))
      ((e.tensorComparison a b).hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj))
      (mu0.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj))
      (X.tensor.map (Prod.mkHom (ec.app P.obj) (ec.app Q.obj)))
      ((siteDerivedTensorIndependentCoefficients X.topology X.ring).map
        (Prod.mkHom (ec.app P.obj) (ec.app Q.obj)))
      (zX.hom.app (e.left.obj (DerivedCategory.Q.obj P.obj),
        e.left.obj (DerivedCategory.Q.obj Q.obj)))
      (zX.hom.app
        (DerivedCategory.Q.obj ((e.pullback.mapHomologicalComplex (.up ℤ)).obj P.obj),
          DerivedCategory.Q.obj ((e.pullback.mapHomologicalComplex (.up ℤ)).obj Q.obj)))
      (derivedPullbackComplexComparison e.pullback e.left e.epsilon
        (CochainComplex.mapBifunctor P.obj Q.obj Y.mateTensor) ≫
        (DerivedCategory.Q.mapIso (e.ordinaryTensor.totalIso Y.ring X.ring e.inverseRing
          e.inverse e.algebraic e.ringMap e.pullback e.object_eq
          e.pushforward e.moduleAdjunction P.obj Q.obj)).inv)
      (b.mateRepresentative.hom.app
        (⟨(e.pullback.mapHomologicalComplex (.up ℤ)).obj P.obj, hp'⟩,
          ⟨(e.pullback.mapHomologicalComplex (.up ℤ)).obj Q.obj, hq'⟩))
      (rX.mateRepresentative.hom.app
        (⟨(e.pullback.mapHomologicalComplex (.up ℤ)).obj P.obj, hp'⟩,
          ⟨(e.pullback.mapHomologicalComplex (.up ℤ)).obj Q.obj, hq'⟩)) ?_ ?_ hz ?_ ?_
    · exact (e.left.map_comp _ _).symm.trans
        (congrArg e.left.map (hzY P Q))
    · exact hzX _ _
    · exact mateNormalizationSquare rfl rfl (congrArg X.tensor.map hepair) rfl rfl
        (by simpa only [Category.assoc] using hn)
    · exact mateNormalizationSquare (congrArg e.left.map hyr)
        (hmu0app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj))
        (mateUncurryMap (siteDerivedTensorIndependentCoefficients X.topology X.ring)
          (Prod.mkHom (ec.app P.obj) (ec.app Q.obj))).symm
        (congrArg₂ (fun x y ↦ x ≫ y)
          (hecDerived (CochainComplex.mapBifunctor P.obj Q.obj Y.mateTensor)).symm
          hcomparison.symm) hxr
        (by exact hn0.trans (Category.assoc _ _ _).symm)
  have hmu (U V : Y.mateDerived) :
      e.left.map (zY.hom.app (U, V)) ≫ mu0.hom.app (U, V) =
        (e.tensorComparison a b).hom.app (U, V) ≫
          zX.hom.app (e.left.obj U, e.left.obj V) :=
    NatTrans.congr_app hmuNat (U, V)
  have heps : NatTrans.CommShift e.epsilon ℤ := by
    let := hecs
    exact mateEpsilonShift e.pullback e.left e.epsilon ec hecapp
  have hL := matePullbackExact e heps
  have hY0 := matePublishedExact (s := sY0) Y hcanY
  have hX0 := matePublishedExact (s := sX0) X hcanX
  have hY : ∀ U : Y.mateDerived,
      ((Functor.curryObj Y.tensor).obj U).IsTriangulated ∧
        ((Functor.curryObj Y.tensor).flip.obj U).IsTriangulated := by
    intro U
    let cL : (Functor.curryObj Y.tensor).obj U ≅
        (Functor.curryObj (siteDerivedTensorIndependentCoefficients
          Y.topology Y.ring)).obj U := (mateCurryIso zY).app U
    let cR : (Functor.curryObj Y.tensor).flip.obj U ≅
        (Functor.curryObj (siteDerivedTensorIndependentCoefficients
          Y.topology Y.ring)).flip.obj U := (mateFlipCurryIso zY).app U
    let : NatTrans.CommShift cL.hom ℤ := hcYL U
    let : NatTrans.CommShift cR.hom ℤ := hcYR U
    exact ⟨(Functor.isTriangulated_iff_of_iso cL).2 (hY0 U).1,
      (Functor.isTriangulated_iff_of_iso cR).2 (hY0 U).2⟩
  have hX : ∀ U : X.mateDerived,
      ((Functor.curryObj X.tensor).obj U).IsTriangulated ∧
        ((Functor.curryObj X.tensor).flip.obj U).IsTriangulated := by
    intro U
    let cL : (Functor.curryObj X.tensor).obj U ≅
        (Functor.curryObj (siteDerivedTensorIndependentCoefficients
          X.topology X.ring)).obj U := (mateCurryIso zX).app U
    let cR : (Functor.curryObj X.tensor).flip.obj U ≅
        (Functor.curryObj (siteDerivedTensorIndependentCoefficients
          X.topology X.ring)).flip.obj U := (mateFlipCurryIso zX).app U
    let : NatTrans.CommShift cL.hom ℤ := hcXL U
    let : NatTrans.CommShift cR.hom ℤ := hcXR U
    exact ⟨(Functor.isTriangulated_iff_of_iso cL).2 (hX0 U).1,
      (Functor.isTriangulated_iff_of_iso cR).2 (hX0 U).2⟩
  let uYrho : (Functor.curryObj
      (siteDerivedTensorIndependentCoefficients Y.topology Y.ring)).flip.obj Y.mateUnit ≅
        𝟭 Y.mateDerived := uY.rho
  let uXrho : (Functor.curryObj
      (siteDerivedTensorIndependentCoefficients X.topology X.ring)).flip.obj X.mateUnit ≅
        𝟭 X.mateDerived := uX.rho
  let rhoY := (mateFlipCurryIso zY).app
    Y.mateUnit ≪≫ uYrho
  let rhoX := (mateFlipCurryIso zX).app
    X.mateUnit ≪≫ uXrho
  have huY : a.MateCanonicalUnit (fun U ↦ rhoY.app U) :=
    mateUnitTransport Y.mateTensor DerivedCategory.Q Y.tensor _
      Y.mateFlat Y.mateUnitComplex _
      (fun P Q hp hq ↦ a.mateRepresentative.app (⟨P, hp⟩, ⟨Q, hq⟩))
      (fun P Q hp hq ↦ a0.mateRepresentative.app (⟨P, hp⟩, ⟨Q, hq⟩))
      zY hzY uYrho (matePublishedUnitNormalized Y a0 hrY uY)
  have huX : b.MateCanonicalUnit (fun U ↦ rhoX.app U) :=
    mateUnitTransport X.mateTensor DerivedCategory.Q X.tensor _
      X.mateFlat X.mateUnitComplex _
      (fun P Q hp hq ↦ b.mateRepresentative.app (⟨P, hp⟩, ⟨Q, hq⟩))
      (fun P Q hp hq ↦ b0.mateRepresentative.app (⟨P, hp⟩, ⟨Q, hq⟩))
      zX hzX uXrho (matePublishedUnitNormalized X b0 hrX uX)
  unfold MateProjectionStructureData
  refine ⟨sY, sX, sL, ha, hb, heps, hL, hY, hX, ?_, ?_,
    unitL, rhoY, rhoX, huY, huX, ?_⟩
  · intro n U V
    let d0 := mateComparisonAt e.left _ _ mu0 U
    have hd0 : NatTrans.CommShift d0.hom ℤ := by
      constructor
      intro m
      ext Z
      simpa only [d0, mateComparisonAt, Iso.app_hom, NatIso.ofComponents_hom_app,
        NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Functor.commShiftIso_comp_hom_app, Functor.comp_obj, Functor.comp_map,
        PullbackTensorCanonical.canonicalDerivedTensor,
        KFlatFixedTensor.derivedTensor, Functor.curry, Functor.curryObj, hmu0app, Category.assoc]
        using (hshift₂ m U Z).symm
    have hd : NatTrans.CommShift
        (mateComparisonAt e.left _ _ (e.tensorComparison a b) U).hom ℤ := by
      let := hd0
      rw [mateComparisonAtTransport e.left _ _ _ _ zY zX _ mu0 hmu U]
      let cY : (Functor.curryObj Y.tensor).obj U ≅
          (Functor.curryObj (siteDerivedTensorIndependentCoefficients Y.topology Y.ring)).obj U :=
        (mateCurryIso zY).app U
      let cX : (Functor.curryObj X.tensor).obj (e.left.obj U) ≅
          (Functor.curryObj (siteDerivedTensorIndependentCoefficients X.topology X.ring)).obj
            (e.left.obj U) := (mateCurryIso zX).app (e.left.obj U)
      let : NatTrans.CommShift cY.hom ℤ := hcYL U
      let : NatTrans.CommShift cX.hom ℤ := hcXL (e.left.obj U)
      exact mateWhiskeredComparisonCommShift e.left cY d0 cX
    let := hd
    simpa only [mateComparisonAt, Iso.app_hom, NatIso.ofComponents_hom_app,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Functor.commShiftIso_comp_hom_app, Functor.comp_obj, Functor.comp_map,
        Functor.curryObj, hmu0app, Category.assoc]
      using (NatTrans.shift_app_comm
        (mateComparisonAt e.left _ _ (e.tensorComparison a b) U).hom n V).symm
  · intro n U V
    let d0 := mateComparisonFlipAt e.left _ _ mu0 V
    have hd0 : NatTrans.CommShift d0.hom ℤ := by
      constructor
      intro m
      ext Z
      simpa only [d0, mateComparisonFlipAt, Iso.app_hom, NatIso.ofComponents_hom_app,
        NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Functor.commShiftIso_comp_hom_app, Functor.comp_obj, Functor.comp_map,
        PullbackTensorCanonical.canonicalDerivedTensor,
        KFlatFixedTensor.derivedTensor, Functor.curry, Functor.curryObj,
        Functor.flip_obj_map, Functor.flip_obj_obj,
        hmu0app, Category.assoc] using (hshift₁ m Z V).symm
    have hd : NatTrans.CommShift
        (mateComparisonFlipAt e.left _ _ (e.tensorComparison a b) V).hom ℤ := by
      let := hd0
      rw [mateComparisonFlipAtTransport e.left _ _ _ _ zY zX _ mu0 hmu V]
      let cY : (Functor.curryObj Y.tensor).flip.obj V ≅
          (Functor.curryObj
            (siteDerivedTensorIndependentCoefficients Y.topology Y.ring)).flip.obj V :=
        (mateFlipCurryIso zY).app V
      let cX : (Functor.curryObj X.tensor).flip.obj (e.left.obj V) ≅
          (Functor.curryObj (siteDerivedTensorIndependentCoefficients X.topology X.ring)).flip.obj
            (e.left.obj V) := (mateFlipCurryIso zX).app (e.left.obj V)
      let : NatTrans.CommShift cY.hom ℤ := hcYR V
      let : NatTrans.CommShift cX.hom ℤ := hcXR (e.left.obj V)
      exact mateWhiskeredComparisonCommShift e.left cY d0 cX
    let := hd
    simpa only [mateComparisonFlipAt, Iso.app_hom, NatIso.ofComponents_hom_app,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Functor.commShiftIso_comp_hom_app, Functor.comp_obj, Functor.comp_map,
        Functor.curryObj, Functor.flip_obj_map, Functor.flip_obj_obj,
      Category.assoc] using (NatTrans.shift_app_comm
        (mateComparisonFlipAt e.left _ _ (e.tensorComparison a b) V).hom n U).symm
  · intro U
    change (e.tensorComparison a b).hom.app (U, Y.mateUnit) ≫
      X.tensor.map (Prod.mkHom (𝟙 (e.left.obj U)) unitL.hom) ≫
      (zX.hom.app (e.left.obj U, X.mateUnit) ≫ uXrho.hom.app (e.left.obj U)) =
        e.left.map (zY.hom.app (U, Y.mateUnit) ≫ uYrho.hom.app U)
    have hn := zX.hom.naturality (Prod.mkHom (𝟙 (e.left.obj U)) unitL.hom)
    apply mateUnitTransportEquation e.left
      (zY.hom.app (U, Y.mateUnit)) (uYrho.hom.app U)
      ((e.tensorComparison a b).hom.app (U, Y.mateUnit))
      (mu0.hom.app (U, Y.mateUnit))
      (X.tensor.map (Prod.mkHom (𝟙 (e.left.obj U)) unitL.hom))
      ((siteDerivedTensorIndependentCoefficients X.topology X.ring).map
        (Prod.mkHom (𝟙 (e.left.obj U)) unitL.hom))
      (zX.hom.app (e.left.obj U, e.left.obj Y.mateUnit))
      (zX.hom.app (e.left.obj U, X.mateUnit)) (uXrho.hom.app (e.left.obj U))
      (hmu U Y.mateUnit) hn
    apply (congrArg (fun x ↦ x ≫
      (siteDerivedTensorIndependentCoefficients X.topology X.ring).map
        (Prod.mkHom (𝟙 (e.left.obj U)) unitL.hom) ≫ uXrho.hom.app (e.left.obj U))
      (hmu0app (U, Y.mateUnit))).trans
    exact hunit U



set_option maxHeartbeats 500000 in
-- Elaboration must compare the large two-variable localization interfaces.
/-- Exactness, normalized tensor shifts, and the counit projection mate for a ringed topos.
Source: Stacks Tags 06YU, 07A4, 07A6, 0B56 and Derived Categories Tag 0A8D
(blueprint: lem-weil-pbc-ringed-projection-mate-exact).

Proof:
1. Descend total tensor from flat-term K-flat complexes using
`lem-weil-pbc-site-derived-tensor-descent` and `lem-pc-kflat-resolution`. Construct L by
`lem-weil-pbc-ringed-topoi-derived-pullback`; K-injective resolutions and
`lem-pc-right-derived-functor-triangulated` construct R. The module adjunction
`lem-weil-pbc-ringed-topoi-module-adjunction` and `lem-pc-derived-adjoint-functors`
give the derived adjunction.
2. The canonical comparison is `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`.
On representatives it sends a tensor (x tensor y) to (a tensor x) tensor (1 tensor y),
with inverse multiplying scalars. The first-factor shift has no sign; the second on
first-factor degree p has sign (-1)^(np). These chain maps are coherent for all integers,
natural, and compatible with pullback and multiplication by the unit. Descend them.
3. Tensor with a K-flat complex preserves cone triangles: the cone comparison is identity
on the unshifted summand and (-1)^p on the shifted summand. This commutes with the signed
connecting map. Symmetry proves exactness in the other variable. Compose the exact tensor,
L and R to obtain exactness of F and G.
4. Put beta = mu followed by counit tensor identity. Its adjunct is alpha, the existing
`derivedProjectionFormulaMate`. Shifted K-injective complexes stay K-injective by
`lem-weil-pbc-kinjective-shift`. The derived adjunction shift compatibility is the unique
one of `lem-weil-pbc-adjunction-shift-compatibility-unique`. Write alpha_(P[1]) for evaluation
at the shifted object and (alpha_P)[1] for the shifted morphism. Naturality of the unit and
the shift equation for beta give sG alpha_(P[1]) = (alpha_P)[1] sF, for every integer shift.
Naturality in E follows from naturality of the counit and mu. On distinguished triangles,
the first two squares are naturality and the third is this shift equation followed by
naturality at the connecting map. At the unit beta is the counit; the adjunction triangle
identity gives alpha = identity under the unitors. -/
theorem ringedProjectionMateExact
    {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X)
    (a : RingedTensorModel Y) (b : RingedTensorModel X) :
    ∃ (_ : (Functor.curryObj Y.tensor).CommShift₂Int)
      (_ : (Functor.curryObj X.tensor).CommShift₂Int)
      (_ : e.left.CommShift ℤ) (_ : e.right.CommShift ℤ),
      a.MateCanonicalShifts ∧ b.MateCanonicalShifts ∧
      NatTrans.CommShift e.epsilon ℤ ∧
      e.left.IsTriangulated ∧ e.right.IsTriangulated ∧ e.derivedAdjunction.CommShift ℤ ∧
      (∀ U : Y.mateDerived, ((Functor.curryObj Y.tensor).obj U).IsTriangulated ∧
        ((Functor.curryObj Y.tensor).flip.obj U).IsTriangulated) ∧
      (∀ U : X.mateDerived, ((Functor.curryObj X.tensor).obj U).IsTriangulated ∧
        ((Functor.curryObj X.tensor).flip.obj U).IsTriangulated) ∧
      (∀ (n : ℤ) (U V : Y.mateDerived),
        (e.tensorComparison a b).hom.app (U, V⟦n⟧) ≫
            X.tensor.map (Prod.mkHom (𝟙 (e.left.obj U))
              ((e.left.commShiftIso n).hom.app V)) ≫
            (((Functor.curryObj X.tensor).obj (e.left.obj U)).commShiftIso n).hom.app
              (e.left.obj V) =
          e.left.map ((((Functor.curryObj Y.tensor).obj U).commShiftIso n).hom.app V) ≫
            (e.left.commShiftIso n).hom.app (Y.tensor.obj (U, V)) ≫
            (shiftFunctor X.mateDerived n).map ((e.tensorComparison a b).hom.app (U, V))) ∧
      (∀ (n : ℤ) (U V : Y.mateDerived),
        (e.tensorComparison a b).hom.app (U⟦n⟧, V) ≫
            X.tensor.map (Prod.mkHom ((e.left.commShiftIso n).hom.app U)
              (𝟙 (e.left.obj V))) ≫
            (((Functor.curryObj X.tensor).flip.obj (e.left.obj V)).commShiftIso n).hom.app
              (e.left.obj U) =
          e.left.map ((((Functor.curryObj Y.tensor).flip.obj V).commShiftIso n).hom.app U) ≫
            (e.left.commShiftIso n).hom.app (Y.tensor.obj (U, V)) ≫
            (shiftFunctor X.mateDerived n).map ((e.tensorComparison a b).hom.app (U, V))) ∧
      ∃ (unitL : e.left.obj Y.mateUnit ≅ X.mateUnit)
        (unitY : ∀ U : Y.mateDerived, Y.tensor.obj (U, Y.mateUnit) ≅ U)
        (unitX : ∀ U : X.mateDerived, X.tensor.obj (U, X.mateUnit) ≅ U),
        a.MateCanonicalUnit unitY ∧ b.MateCanonicalUnit unitX ∧
        (∀ U : Y.mateDerived,
          (e.tensorComparison a b).hom.app (U, Y.mateUnit) ≫
            X.tensor.map (Prod.mkHom (𝟙 (e.left.obj U)) unitL.hom) ≫
            (unitX (e.left.obj U)).hom = e.left.map (unitY U).hom) ∧
        ∃ alpha : ∀ E : X.mateDerived,
          (Functor.curryObj Y.tensor).obj (e.right.obj E) ⟶
            e.left ⋙ (Functor.curryObj X.tensor).obj E ⋙ e.right,
          (∀ (E : X.mateDerived) (P : Y.mateDerived), (alpha E).app P =
            derivedProjectionFormulaMate e.left e.right e.derivedAdjunction Y.tensor X.tensor
              (e.tensorComparison a b) E P) ∧
          (∀ E : X.mateDerived,
            (e.left ⋙ (Functor.curryObj X.tensor).obj E ⋙ e.right).IsTriangulated ∧
              NatTrans.CommShift (alpha E) ℤ) ∧
          (∀ (E : X.mateDerived) (T : Triangle Y.mateDerived), T ∈ distTriang Y.mateDerived →
            ∃ m : (Functor.mapTriangle
                ((Functor.curryObj Y.tensor).obj (e.right.obj E))).obj T ⟶
                (Functor.mapTriangle
                  (e.left ⋙ (Functor.curryObj X.tensor).obj E ⋙ e.right)).obj T,
              m.hom₁ = (alpha E).app T.obj₁ ∧ m.hom₂ = (alpha E).app T.obj₂ ∧
                m.hom₃ = (alpha E).app T.obj₃) ∧
          (∀ (E E' : X.mateDerived) (q : E ⟶ E') (P : Y.mateDerived),
            ((Functor.curryObj Y.tensor).map (e.right.map q)).app P ≫ (alpha E').app P =
              (alpha E).app P ≫
                (Functor.whiskerRight (Functor.whiskerLeft e.left
                  ((Functor.curryObj X.tensor).map q)) e.right).app P) ∧
          (∀ E : X.mateDerived,
            (alpha E).app Y.mateUnit ≫
              e.right.map (X.tensor.map (Prod.mkHom (𝟙 E) unitL.hom) ≫ (unitX E).hom) =
                (unitY (e.right.obj E)).hom) := by
  classical
  have hdata := mateProjectionStructures e a b
  unfold MateProjectionStructureData at hdata
  obtain ⟨sY, sX, sL, ha, hb, heps, hL, hY, hX, hs₂, hs₁,
    unitL, rhoY, rhoX, huY, huX, hunit⟩ := hdata
  let := sY
  let := sX
  let := sL
  let := e.derivedAdjunction.rightAdjointCommShift ℤ
  let := e.derivedAdjunction.commShift_of_leftAdjoint ℤ
  let := hL
  let := e.derivedAdjunction.isTriangulated_rightAdjoint
  let (U : Y.mateDerived) := (hY U).1
  let (U : Y.mateDerived) := (hY U).2
  let (U : X.mateDerived) := (hX U).1
  let (U : X.mateDerived) := (hX U).2
  refine ⟨sY, sX, sL, inferInstance, ha, hb, heps, hL, inferInstance,
    inferInstance, hY, hX, hs₂, hs₁, unitL, (fun U ↦ rhoY.app U),
    (fun U ↦ rhoX.app U), huY, huX, hunit, ?_⟩
  exact mateFormalExactProjection Y.mateDerived X.mateDerived Y.tensor X.tensor
    e.left e.right e.derivedAdjunction Y.mateUnit X.mateUnit rhoY rhoX
    (e.tensorComparison a b) hs₂ hs₁ unitL hunit

end

end SheafOfModules
