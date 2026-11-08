/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Submission.WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import Submission.WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Data.ZMod.Basic
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Submission.WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Submission.WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import Submission.WeilConjectures.CategoryTheory.Sites.TorsionSheafConstantModule
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Homology.Monoidal
import Submission.WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Submission.WeilConjectures.AlgebraicGeometry.DivisibleExtensionDerivedReduction
public import Mathlib.AlgebraicGeometry.AffineScheme

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Derived reduction of an extension by a divisible sheaf

Source: the Cartier unit proof, paragraphs 4 and 5, in blueprint main-20261015;
Stacks Tags 06YU, 06YV, 06YY, 0152, 09T5 and 0FND
(blueprint: lem-sfb-divisible-extension-derived-reduction).
Kernel and quotient objects are specified by their short exact sequences, including
existence of their residue-coefficient structures. The normalized identifications are
unique, so the definition of the reduced boundary makes no arbitrary choice of map.
The normalized sheaf scalar adjunction is an item helper; the general internal-module
derived extension of scalars remains the recorded dependency interface.
-/

@[expose] public section
set_option autoImplicit false
universe u v r wZ wR u' v' wZ' wR'
open CategoryTheory CategoryTheory.Limits

section GeneralBoundaryNaturality
variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]
  (res : B ⥤ A) [res.Additive]
  [PreservesFiniteLimits res] [PreservesFiniteColimits res]
  (L : DerivedCategory A ⥤ DerivedCategory B) [L.CommShift ℤ]
  (ad : L ⊣ res.mapDerivedCategory) (n : ℕ)

end GeneralBoundaryNaturality

section AbstractCokernel
set_option backward.isDefEq.respectTransparency false
variable {A₀ B₀ : Type*} [Category A₀] [Category B₀] [Abelian A₀]
  (E : A₀ ⥤ B₀) (R : B₀ ⥤ A₀) [R.Full] [R.Faithful]
  (a : E ⊣ R) (A : A₀) (g : A ⟶ A)
  (hz : g ≫ a.unit.app A = 0) (Q : B₀) (eQ : cokernel g ≅ R.obj Q)
end AbstractCokernel

section UnitTriangle
set_option backward.isDefEq.respectTransparency false
open CategoryTheory.Pretriangulated
variable {A B : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
  [Category* B] [Abelian B] [HasDerivedCategory B]
  (E : A ⥤ B) [E.Additive] (R : B ⥤ A) [R.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  (a : E ⊣ R) (L : DerivedCategory A ⥤ DerivedCategory B) (ad : L ⊣ R.mapDerivedCategory)
  (ε : DerivedCategory.Q ⋙ L ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (n : ℕ) (P K : CochainComplex A ℤ) (p : P ⟶ K) [QuasiIso p] [IsIso (ε.app P)]
  (hz : (n • 𝟙 P) ≫ (a.mapHomologicalComplex (.up ℤ)).unit.app P = 0)
  (hS : (ShortComplex.mk (n • 𝟙 P) ((a.mapHomologicalComplex (.up ℤ)).unit.app P)
    hz).ShortExact)
  (hnormal : ad.unit.app (DerivedCategory.Q.obj P) ≫ R.mapDerivedCategory.map (ε.app P) ≫
    R.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) =
    DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P))
end UnitTriangle

section Generic
universe a b c d e f
set_option backward.isDefEq.respectTransparency false
variable {A : Type a} [Category.{b} A] [Abelian A] [HasDerivedCategory.{c} A]
  {B : Type d} [Category.{e} B] [Abelian B] [HasDerivedCategory.{f} B]
  (R : B ⥤ A) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [R.Full] [R.Faithful]

end Generic

section DerivedSingle
set_option backward.isDefEq.respectTransparency false
variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
  {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
  (E : A ⥤ B) [E.Additive] (R : B ⥤ A) [R.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R] (a : E ⊣ R)
  (L : DerivedCategory A ⥤ DerivedCategory B) (ad : L ⊣ R.mapDerivedCategory)
  (ε : DerivedCategory.Q ⋙ L ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (X : A) (Y : B) (b : E.obj X ⟶ Y) [IsIso b] (f : X ⟶ R.obj Y)
  (hb : a.unit.app X ≫ R.map b = f)
  (hε : IsIso (ε.app ((HomologicalComplex.single A (.up ℤ) 0).obj X)))
  (hu : ad.unit.app ((DerivedCategory.singleFunctor A 0).obj X) ≫
    R.mapDerivedCategory.map (ε.app ((HomologicalComplex.single A (.up ℤ) 0).obj X)) ≫
      R.mapDerivedCategoryFactors.hom.app
        ((E.mapHomologicalComplex (.up ℤ)).obj
          ((HomologicalComplex.single A (.up ℤ) 0).obj X)) =
    DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app
      ((HomologicalComplex.single A (.up ℤ) 0).obj X)))
end DerivedSingle

section ShiftedComposition
variable {A : Type*} [Category* A] [HasShift A ℤ] {X Y Z : A}
end ShiftedComposition

section ShiftedAdjunct
set_option backward.isDefEq.respectTransparency false
variable {A B : Type*} [Category* A] [Category* B]
  [HasShift A ℤ] [HasShift B ℤ] (L : A ⥤ B) (R : B ⥤ A)
  [L.CommShift ℤ] [R.CommShift ℤ] (ad : L ⊣ R) [ad.CommShift ℤ]
  {X Y : A} {H : B} (f : X ⟶ Y⟦(1 : ℤ)⟧)
  (a : L.obj Y ⟶ H⟦(1 : ℤ)⟧) (k : Y ⟶ R.obj (H⟦(1 : ℤ)⟧))
  (ha : ad.unit.app Y ≫ R.map a = k)
end ShiftedAdjunct

namespace SheafOfModules

section UnitKFlat
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  (R : Sheaf J CommRingCat.{r})
private theorem unit_kflat : CochainComplex.IsKFlatIndependentCoefficients (R := R)
    ((HomologicalComplex.single _ (.up ℤ) 0).obj
      (unit (derivedChangeRingIndependentCoefficients J R))) := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := symmetricCategory R
  let := preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  intro F hF
  exact hF.of_iso (HomologicalComplex.rightUnitor F).symm
end UnitKFlat

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  {Z R : Sheaf J CommRingCat.{r}} (q : Z ⟶ R)

set_option linter.unusedSectionVars false in
private noncomputable abbrev sr {D : Type u} [Category.{v} D] (K : GrothendieckTopology D)
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    (A : Sheaf K CommRingCat.{r}) := derivedChangeRingIndependentCoefficients K A

private noncomputable abbrev scalarRes
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S) :=
  restrictScalars.{r} ((sheafCompose K (forget₂ CommRingCat RingCat)).map c)

open scoped ChangeOfRings
set_option backward.isDefEq.respectTransparency false

private local instance tensorRestrictionTargetModule
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    {A : Sheaf K CommRingCat.{r}} (M : SheafOfModules.{r} (sr K A))
    {X Y : Dᵒᵖ} (i : X ⟶ Y) :
    Module (A.obj.obj Y)
      ((ModuleCat.restrictScalars ((sr K A).obj.map i).hom).obj (M.val.obj Y)) :=
  inferInstanceAs (Module (A.obj.obj Y) (M.val.obj Y))

private theorem tensorRestriction_tmul
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify K AddCommGrpCat.{r}]
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S) (M : SheafOfModules.{r} (sr K A))
    {X Y : Dᵒᵖ} (i : X ⟶ Y) (s : S.obj.obj X) (m : M.val.obj X) :
    (changeOfRingsPresheaf.{v, u, r} c M).map i (s ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m) =
      S.obj.map i s ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom] M.val.map i m :=
  Classical.choose_spec (exists_changeOfRingsMap.{v, u, r} c M i) s m

private noncomputable def tensorPresheafFunctor
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify K AddCommGrpCat.{r}]
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S) :
    SheafOfModules.{r} (sr K A) ⥤ PresheafOfModules.{r} (sr K S).obj where
  obj M := changeOfRingsPresheaf.{v, u, r} c M
  map {M N} f :=
    show changeOfRingsPresheaf.{v, u, r} c M ⟶
      changeOfRingsPresheaf.{v, u, r} c N from
    { app := fun W ↦ (ModuleCat.extendScalars (c.hom.app W).hom).map (f.val.app W)
      naturality := changeOfRingsHom_naturality.{v, u, r} c _ f }
  map_id M := by
    ext W : 1
    change (ModuleCat.extendScalars (c.hom.app W).hom).map (𝟙 _) = _
    exact (ModuleCat.extendScalars (c.hom.app W).hom).map_id _
  map_comp f g := by
    ext W : 1
    exact (ModuleCat.extendScalars (c.hom.app W).hom).map_comp _ _

private noncomputable def tensorFunctor
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify K AddCommGrpCat.{r}]
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S) :
    SheafOfModules.{r} (sr K A) ⥤ SheafOfModules.{r} (sr K S) :=
  tensorPresheafFunctor c ⋙ PresheafOfModules.sheafification (𝟙 (sr K S).obj)

private noncomputable def tensorToRestriction
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify K AddCommGrpCat.{r}]
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S)
    (M : SheafOfModules.{r} (sr K A)) (H : SheafOfModules.{r} (sr K S))
    (f : changeOfRingsPresheaf.{v, u, r} c M ⟶ H.val) : M ⟶ (scalarRes c).obj H where
  val :=
    { app := fun W ↦ ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars
        (c.hom.app W).hom (f.app W)
      naturality := by
        intro X Y i
        ext m
        change f.app Y ((1 : S.obj.obj Y) ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom]
          M.val.map i m) = H.val.map i (f.app X
            ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m))
        have h := PresheafOfModules.naturality_apply f i
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m)
        rw [tensorRestriction_tmul, map_one] at h
        exact h }

private noncomputable def restrictionToTensor
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify K AddCommGrpCat.{r}]
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S)
    (M : SheafOfModules.{r} (sr K A)) (H : SheafOfModules.{r} (sr K S))
    (g : M ⟶ (scalarRes c).obj H) : changeOfRingsPresheaf.{v, u, r} c M ⟶ H.val where
  app W := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (c.hom.app W).hom (g.val.app W)
  naturality := by
    intro X Y i
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    have h := PresheafOfModules.naturality_apply g.val i m
    change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
      (c.hom.app Y).hom (g.val.app Y)
        ((changeOfRingsPresheaf.{v, u, r} c M).map i
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m)) =
      H.val.map i (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
        (c.hom.app X).hom (g.val.app X)
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m))
    rw [tensorRestriction_tmul, map_one]
    have atOne (W : Dᵒᵖ) (n : M.val.obj W) :
        ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
          (c.hom.app W).hom (g.val.app W)
            ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] n) = g.val.app W n := by
      exact congrArg (fun f : M.val.obj W ⟶
        (ModuleCat.restrictScalars (c.hom.app W).hom).obj (H.val.obj W) ↦ f n)
        ((ModuleCat.ExtendRestrictScalarsAdj.homEquiv (c.hom.app W).hom).apply_symm_apply
          (g.val.app W))
    rw [atOne, atOne]
    exact h

private noncomputable def tensorPresheafHomEquiv
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify K AddCommGrpCat.{r}]
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S)
    (M : SheafOfModules.{r} (sr K A)) (H : SheafOfModules.{r} (sr K S)) :
    (changeOfRingsPresheaf.{v, u, r} c M ⟶ H.val) ≃ (M ⟶ (scalarRes c).obj H) where
  toFun := tensorToRestriction c M H
  invFun := restrictionToTensor c M H
  left_inv f := by
    ext W : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (c.hom.app W).hom).symm_apply_apply
      (f.app W)
  right_inv g := by
    apply SheafOfModules.hom_ext
    ext W : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (c.hom.app W).hom).apply_symm_apply
      (g.val.app W)

private noncomputable def tensorHomEquiv
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify K AddCommGrpCat.{r}]
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S)
    (M : SheafOfModules.{r} (sr K A)) (H : SheafOfModules.{r} (sr K S)) :
    ((tensorFunctor c).obj M ⟶ H) ≃ (M ⟶ (scalarRes c).obj H) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (sr K S).obj)).homEquiv _ _).trans
    (tensorPresheafHomEquiv c M H)

private theorem tensorHomEquiv_naturality_left
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify K AddCommGrpCat.{r}]
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S)
    {M N : SheafOfModules.{r} (sr K A)} (a : M ⟶ N)
    (H : SheafOfModules.{r} (sr K S)) (f : (tensorFunctor c).obj N ⟶ H) :
    tensorHomEquiv c M H ((tensorFunctor c).map a ≫ f) =
      a ≫ tensorHomEquiv c N H f := by
  change tensorPresheafHomEquiv c M H
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (sr K S).obj)).homEquiv _ _
        ((PresheafOfModules.sheafification (𝟙 (sr K S).obj)).map
          ((tensorPresheafFunctor c).map a) ≫ f)) = _
  rw [Adjunction.homEquiv_naturality_left]
  ext W m
  change ((PresheafOfModules.sheafificationAdjunction (𝟙 (sr K S).obj)).homEquiv
    (changeOfRingsPresheaf.{v, u, r} c N) H f).app W
      ((ModuleCat.extendScalars (c.hom.app W).hom).map (a.val.app W)
        ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m)) = _
  rw [ModuleCat.ExtendScalars.map_tmul]
  rfl

private theorem tensorHomEquiv_naturality_right
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify K AddCommGrpCat.{r}]
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S)
    (M : SheafOfModules.{r} (sr K A))
    {H H' : SheafOfModules.{r} (sr K S)}
    (f : (tensorFunctor c).obj M ⟶ H) (b : H ⟶ H') :
    tensorHomEquiv c M H' (f ≫ b) =
      tensorHomEquiv c M H f ≫ (scalarRes c).map b := by
  change tensorPresheafHomEquiv c M H'
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (sr K S).obj)).homEquiv _ _
        (f ≫ b)) = _
  rw [Adjunction.homEquiv_naturality_right]
  rfl

private noncomputable def tensorAdjunction
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify K AddCommGrpCat.{r}]
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S) : tensorFunctor c ⊣
      scalarRes c :=
  Adjunction.mkOfHomEquiv
    { homEquiv := tensorHomEquiv c
      homEquiv_naturality_left_symm := by
        intro M N H a g
        apply (tensorHomEquiv c M H).injective
        rw [Equiv.apply_symm_apply, tensorHomEquiv_naturality_left,
          Equiv.apply_symm_apply]
      homEquiv_naturality_right := fun f b ↦ tensorHomEquiv_naturality_right c _ f b }

attribute [irreducible] tensorAdjunction

-- The induced functor on structured arrows is also full and essentially
-- surjective, so restricting the defining limit cone preserves its limit.
-- Transport the defining limit cone through an equivalence of structured
-- arrow categories and the prescribed isomorphism of diagram functors.
-- Bound unfolding while checking the denominator cone.
variable [HasDerivedCategory.{wZ} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J Z))]
  [HasDerivedCategory.{wR} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J R))]
  (D : DerivedChangeOfRingsCochainModel q)

-- Keep normalization comparisons from unfolding the sheafification implementation.
set_option backward.isDefEq.respectTransparency true in
/-- The canonical shift comparison, induced from exact restriction by the normalized
adjunction. This fixes compatibility with its unit, instead of choosing an unrelated
triangulated shift structure. Source: Stacks 06YY and 09T5
(blueprint: lem-sfb-divisible-extension-derived-reduction). -/
noncomputable instance sheafScalarModelCommShift : D.T.CommShift ℤ :=
  (sheafScalarDerivedAdjunction q D).leftAdjointCommShift ℤ

set_option backward.isDefEq.respectTransparency true

end SheafOfModules

namespace SheafOfModules
namespace DivisibleReduction

attribute [local irreducible] sheafScalarOrdinaryAdjunction sheafScalarDerivedAdjunction

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  (J : GrothendieckTopology C)
  [HasSheafify J CommRingCat.{r}]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]

variable {J} (n : ℕ)

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] coefficientUnit

section PresentationConstruction

open CategoryTheory.Functor

private instance ringLocallyBijective : J.WEqualsLocallyBijective CommRingCat.{r} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v, r, u, r+1, r, r, r} J

private noncomputable def ringUnit (A : CommRingCat.{r}) :
    (Functor.const Cᵒᵖ).obj (RingCat.of A) ⟶
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        ((constantSheaf J CommRingCat).obj A)).obj :=
  whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj A)) (forget₂ CommRingCat RingCat)

private instance ringUnit_ls (A : CommRingCat.{r}) :
    Presheaf.IsLocallySurjective J (ringUnit (J := J) A) :=
  ⟨fun x ↦ Presheaf.imageSieve_mem J
    (toSheafify J ((Functor.const Cᵒᵖ).obj A)) x⟩

private instance ringUnit_li (A : CommRingCat.{r}) :
    Presheaf.IsLocallyInjective J (ringUnit (J := J) A) :=
  ⟨fun x y h ↦ Presheaf.equalizerSieve_mem J
    (toSheafify J ((Functor.const Cᵒᵖ).obj A)) x y h⟩

private instance integerForget_full :
    (toSheaf (derivedChangeRingIndependentCoefficients J (integers J))).Full where
  map_surjective {M N} f := by
    let α := ringUnit (J := J) (CommRingCat.of (ULift.{r} ℤ))
    let g : (PresheafOfModules.restrictScalars α).obj M.val ⟶
        (PresheafOfModules.restrictScalars α).obj N.val :=
      PresheafOfModules.homMk f.hom (by
        intro U z x
        obtain ⟨z⟩ := z
        change f.hom.app U ((α.app U).hom (z : ULift.{r} ℤ) • (show M.val.obj U from x)) =
          (α.app U).hom (z : ULift.{r} ℤ) • (show N.val.obj U from f.hom.app U x)
        rw [map_intCast, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
        exact map_zsmul (f.hom.app U).hom z x)
    let g' := (PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      α N.isSheaf).symm g
    refine ⟨⟨g'⟩, ?_⟩
    have h := (PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      α N.isSheaf).apply_symm_apply g
    ext U x
    exact congrArg (fun k ↦ k.app U x) h

private noncomputable def liftTorsion (n : ℕ) (M : Integral J)
    (hM : ∀ (U : Cᵒᵖ) (x : M.val.obj U), n • x = 0) : Residue J n :=
  PresheafOfModules.sheafify (ringUnit (J := J) (CommRingCat.of (ULift.{r} (ZMod n))))
    (M₀ := CategoryTheory.Sheaf.presheafOfModulesOfNsmul M.val.presheaf hM)
    (A := (toSheaf _).obj M) (𝟙 _)

private noncomputable def liftTorsionIso (n : ℕ) (M : Integral J)
    (hM : ∀ (U : Cᵒᵖ) (x : M.val.obj U), n • x = 0) :
    M ≅ (restriction J n).obj (liftTorsion n M hM) :=
  (toSheaf (derivedChangeRingIndependentCoefficients J (integers J))).preimageIso (Iso.refl _)
attribute [irreducible] liftTorsion liftTorsionIso

private instance restriction_faithful (n : ℕ) : (restriction J n).Faithful := by
  refine ⟨fun {M N} f g h ↦ ?_⟩
  ext U x
  exact congrArg (fun k ↦ k.val.app U x) h

private instance restriction_full (n : ℕ) [NeZero n] : (restriction J n).Full where
  map_surjective {M N} f := by
    let α := ringUnit (J := J) (CommRingCat.of (ULift.{r} (ZMod n)))
    let g : (PresheafOfModules.restrictScalars α).obj M.val ⟶
        (PresheafOfModules.restrictScalars α).obj N.val :=
      PresheafOfModules.homMk
        ((toSheaf (derivedChangeRingIndependentCoefficients J (integers J))).map f).hom (by
        intro U z x
        obtain ⟨z⟩ := z
        have hz : (⟨z⟩ : ULift.{r} (ZMod n)) = (z.val : ULift.{r} (ZMod n)) :=
          ULift.ext (by rw [ULift.down_natCast, ZMod.natCast_zmod_val])
        change f.val.app U ((α.app U).hom (⟨z⟩ : ULift.{r} (ZMod n)) •
          (show M.val.obj U from x)) =
          (α.app U).hom (⟨z⟩ : ULift.{r} (ZMod n)) •
            (show N.val.obj U from f.val.app U x)
        rw [hz, map_natCast, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
        exact map_nsmul (f.val.app U).hom z.val x)
    let g' := (PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      α N.isSheaf).symm g
    refine ⟨⟨g'⟩, ?_⟩
    have h := (PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      α N.isSheaf).apply_symm_apply g
    ext U x
    exact congrArg (fun k ↦ k.app U x) h

end PresentationConstruction

variable [HasDerivedCategory.{wZ} (Integral J)]
  [HasDerivedCategory.{wR} (Residue J n)]
  (D : DerivedChangeOfRingsCochainModel (projection J n))

open CategoryTheory.Pretriangulated

set_option backward.isDefEq.respectTransparency true in
attribute [local irreducible] identifications

section InverseImage

variable {C' : Type u'} [Category.{v'} C'] [EssentiallySmall.{r} C']
  {K : GrothendieckTopology C'}
  [HasSheafify K CommRingCat.{r}]
  [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify K AddCommGrpCat.{r}]
  [HasDerivedCategory.{wZ'} (Integral K)] [HasDerivedCategory.{wR'} (Residue K n)]
  (D' : DerivedChangeOfRingsCochainModel (projection K n))
  (UZ : Integral J ⥤ Integral K) (UR : Residue J n ⥤ Residue K n)
  [UZ.Additive] [PreservesFiniteLimits UZ] [PreservesFiniteColimits UZ]
  [UR.Additive] [PreservesFiniteLimits UR] [PreservesFiniteColimits UR]

end InverseImage

end DivisibleReduction
end SheafOfModules
