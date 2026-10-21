/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor


public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.CategoryTheory.Localization.Prod
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Algebra.Homology.ChangeOfRingsTensorCancellationIndependentCoefficients
-- r4: side KFlat instances (global there), as local instances of the live theorems
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

/-!
# Derived tensor with scalar restriction on a ringed site

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/
sk-lem-sf-kunneth-star/lem-trf-ordinary-kunneth.proof.md, Step 2;
Stacks Project, Tags 03EK, 06YS, 06YU, 06YY
(blueprint: lem-trf-site-derived-tensor-restriction).

The comparison on one K-flat factor is normalized by the recorded two-factor descent
comparison. The representative formula uses this comparison, the change-of-rings counit,
and the exact restriction factorization. A single family `e` occurs in both the naturality
and representative clauses. Local pure tensors specify both directions of the chain map.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048
set_option backward.defeqAttrib.useBackward true

universe u v r w a b va vb wa wb

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ChangeOfRings

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}}

/-- The ordinary total tensor bifunctor, using the recorded monoidal sheaf tensor.
Source: Stacks, Tag 06YU (blueprint: lem-trf-site-derived-tensor-restriction). -/
def SiteTensorComplexFunctor (A : Sheaf J CommRingCat.{r}) :
    CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A)) ℤ ⥤ CochainComplex
          (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A)) ℤ ⥤ CochainComplex
          (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A)) ℤ := by
  letI := SheafOfModules.monoidalCategory A
  exact (MonoidalCategory.curriedTensor (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A))).map₂HomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)

/-- A local tensor in the monoidal tensor, through the sheafification-unit pure tensor.
Source: Stacks, Tag 03EK (blueprint: lem-trf-site-derived-tensor-restriction). -/
def siteMonoidalTmul (M N : (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))) (U : Cᵒᵖ) (x : M.val.obj U)
          (y : N.val.obj U) :
    ((SheafOfModules.monoidalCategory R).tensorObj M N).val.obj U := by
  letI := SheafOfModules.monoidalCategory R
  exact (SheafOfModules.tensorObjIsoSheafification M N).inv.val.app U
    (SheafOfModules.siteSheafTensorTmul M N U x y)

/-- Include a local pure tensor in bidegree `(i,j)` of the total tensor complex.
Source: Stacks, Tag 06YU (blueprint: lem-trf-site-derived-tensor-restriction). -/
def siteTotalTmul (P Q : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (i j : ℤ)
    (U : Cᵒᵖ) (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U) :
    ((((SiteTensorComplexFunctor R).obj P).obj Q).X (i + j)).val.obj U := by
  letI := SheafOfModules.monoidalCategory R
  exact (HomologicalComplex.ιMapBifunctor P Q
    (MonoidalCategory.curriedTensor (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))) (ComplexShape.up ℤ) i j
          (i + j) rfl).val.app U
      (siteMonoidalTmul (R := R) (P.X i) (Q.X j) U x y)

/-- Degree-zero sheaf as a complex.
Source: blueprint Step 2 (blueprint: lem-trf-site-derived-tensor-restriction). -/
abbrev siteTensorSingle (N : (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))) :=
  (HomologicalComplex.single (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (ComplexShape.up ℤ) 0).obj N

/-- The resolving class selected by the recorded independent-coefficient descent theorem.
Source: Stacks, Tags 06YS, 06YU (blueprint: lem-trf-site-derived-tensor-restriction). -/
def tensorDescentClass [HasDerivedCategory.{w} (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))] :=
  (SheafOfModules.site_derived_tensor_descent_independentCoefficients.{u, v, r, w, 0, 0} J R).choose

/-- Its specified comparison with the total tensor on complexes.
Source: Stacks, Tag 06YU (blueprint: lem-trf-site-derived-tensor-restriction). -/
def tensorDescentComplexIso [HasDerivedCategory.{w} (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))] :=
  (SheafOfModules.siteHomotopyTensorExistsIndependentCoefficients.{u, v, r, w}
    J R).choose_spec.1.some

/-- Its specified comparison with the recorded derived tensor on the resolving class.
Source: Stacks, Tag 06YU (blueprint: lem-trf-site-derived-tensor-restriction). -/
def tensorDescentDerivedIso [HasDerivedCategory.{w} (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))] :=
  (SheafOfModules.siteDerivedTensorExistsIndependentCoefficients.{u, v, r, w} J R).choose_spec.some

/-- K-flatness with flat terms, using exactly the two recorded predicates.
Source: Stacks, Tags 06YN, 06YS (blueprint: lem-trf-site-derived-tensor-restriction). -/
def TensorFlatRepresentative (P : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) : Prop :=
  CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P ∧
    ∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X i)

/-- The recorded derived tensor, curried without constructing a second tensor product.
Source: Stacks, Tag 06YU (blueprint: lem-trf-site-derived-tensor-restriction). -/
abbrev siteRestrictionDerivedTensor [HasDerivedCategory.{w} (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))] :=
  Functor.curry.obj (SheafOfModules.siteDerivedTensorIndependentCoefficients J R)

/-- Canonical two-sided computation: totalization, homotopy quotient, and descent.
Source: Stacks, Tag 06YU (blueprint: lem-trf-site-derived-tensor-restriction). -/
def tensorDescentPair [HasDerivedCategory.{w} (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))]
    (P Q : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
    (hP : TensorFlatRepresentative P) (hQ : TensorFlatRepresentative Q) :
    DerivedCategory.Q.obj (((SiteTensorComplexFunctor R).obj P).obj Q) ≅
      ((siteRestrictionDerivedTensor (R := R)).obj (DerivedCategory.Q.obj P)).obj
        (DerivedCategory.Q.obj Q) := by
  let d := SheafOfModules.site_derived_tensor_descent_independentCoefficients.{u, v, r, w, 0, 0} J R
  let p : (tensorDescentClass (R := R)).FullSubcategory :=
    ⟨(HomotopyCategory.quotient _ _).obj P, (d.choose_spec.1 _).2 hP⟩
  let q : (tensorDescentClass (R := R)).FullSubcategory :=
    ⟨(HomotopyCategory.quotient _ _).obj Q, (d.choose_spec.1 _).2 hQ⟩
  exact (DerivedCategory.quotientCompQhIso (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))).symm.app _ ≪≫
    DerivedCategory.Qh.mapIso ((tensorDescentComplexIso (R := R)).symm.app (P, Q)) ≪≫
    (tensorDescentDerivedIso (R := R)).app (p, q) ≪≫
    (SheafOfModules.siteDerivedTensorIndependentCoefficients J R).mapIso
      (Iso.prod ((DerivedCategory.quotientCompQhIso (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))).app P)
        ((DerivedCategory.quotientCompQhIso (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))).app Q))

/-- A one-sided computation family, from derived tensor to the ordinary total tensor.
Source: Stacks, Tag 06YU (blueprint: lem-trf-site-derived-tensor-restriction). -/
abbrev OneSidedTensorComparison [HasDerivedCategory.{w} (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))] :=
  ∀ (P : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
          (_ : TensorFlatRepresentative P)
    (Q : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ),
    ((siteRestrictionDerivedTensor (R := R)).obj (DerivedCategory.Q.obj P)).obj
      (DerivedCategory.Q.obj Q) ≅
      DerivedCategory.Q.obj (((SiteTensorComplexFunctor R).obj P).obj Q)

/-- Canonical means natural in the unresolved complex and equal to the recorded descent
comparison whenever that complex is also K-flat with flat terms. Localization and K-flat
resolutions determine every component from these equations, so an arbitrary isomorphism
cannot be substituted here.
Source: Stacks, Tag 06YU (blueprint: lem-trf-site-derived-tensor-restriction). -/
def CanonicalOneSidedTensorComparison [HasDerivedCategory.{w} (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))]
    (c : OneSidedTensorComparison (R := R)) : Prop :=
  (∀ (P : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
          (hP : TensorFlatRepresentative P)
    (Q Q' : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (f : Q ⟶ Q'),
    ((siteRestrictionDerivedTensor (R := R)).obj (DerivedCategory.Q.obj P)).map
        (DerivedCategory.Q.map f) ≫ (c P hP Q').hom =
      (c P hP Q).hom ≫
        DerivedCategory.Q.map (((SiteTensorComplexFunctor R).obj P).map f)) ∧
  (∀ (P Q : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
    (hP : TensorFlatRepresentative P) (hQ : TensorFlatRepresentative Q),
    c P hP Q = (tensorDescentPair P Q hP hQ).symm)

/-- Termwise restriction, exactly the recorded scalar restriction functor.
Source: Stacks, Tag 03DA (blueprint: lem-trf-site-derived-tensor-restriction). -/
abbrev siteTensorRestriction (φ : R ⟶ S) :=
  SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ)

/-- Local section of change of rings, through its actual module-sheafification unit.
The conventional order in `changeOfRings` is `s ⊗ x`, representing `x ⊗ s` in the paper.
Source: Stacks, Tag 03EK (blueprint: lem-trf-site-derived-tensor-restriction). -/
def siteExtensionTmul (φ : R ⟶ S) (M : (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)))
    (E₀ : (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ⥤ (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S)))
          (hobj : ∀ M, E₀.obj M = SheafOfModules.changeOfRings φ M)
    (U : Cᵒᵖ) (x : M.val.obj U) (s : S.obj.obj U) : (E₀.obj M).val.obj U :=
  (eqToHom (hobj M).symm).val.app U
    (((PresheafOfModules.sheafificationAdjunction
      (𝟙 ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S).obj)).unit.app
        (SheafOfModules.changeOfRingsPresheaf φ M)).app U
          (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))

/-- The change-of-rings counit, including the canonical complex/homotopy factorizations.
Source: Stacks, Tag 06YY (blueprint: lem-trf-site-derived-tensor-restriction). -/
def siteExtensionComparison
    [HasDerivedCategory.{w} (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))] [HasDerivedCategory.{w}
          (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S))]
    (E₀ : (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ⥤ (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S))) [E₀.Additive]
    (E : DerivedCategory (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ⥤ DerivedCategory
          (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S)))
    (ε : DerivedCategory.Qh ⋙ E ⟶ E₀.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
    (P : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
    (hiso : IsIso (ε.app ((HomotopyCategory.quotient _ _).obj P))) :
    E.obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj ((E₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) := by
  letI := hiso
  exact (E.mapIso ((DerivedCategory.quotientCompQhIso (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))).app P)).symm ≪≫
    asIso (ε.app ((HomotopyCategory.quotient _ _).obj P)) ≪≫
    DerivedCategory.Qh.mapIso ((E₀.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app P) ≪≫
    (DerivedCategory.quotientCompQhIso (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S))).app _

/-- Naturality of the same displayed family in the derived object and degree-zero sheaf.
Source: blueprint Step 2 (blueprint: lem-trf-site-derived-tensor-restriction). -/
def ProjectionFormulaFamily
    {A : Type a} {B : Type b} [Category.{va} A] [Category.{vb} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wa} A] [HasDerivedCategory.{wb} B]
    (TR : DerivedCategory A ⥤ DerivedCategory A ⥤ DerivedCategory A)
    (TS : DerivedCategory B ⥤ DerivedCategory B ⥤ DerivedCategory B)
    (E : DerivedCategory A ⥤ DerivedCategory B)
    (Res : DerivedCategory B ⥤ DerivedCategory A)
    (e : ∀ X (N : B), (TR.obj X).obj
      (Res.obj (DerivedCategory.Q.obj
        ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj N))) ≅
      Res.obj ((TS.obj (E.obj X)).obj
        (DerivedCategory.Q.obj ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj N)))) :
    Prop :=
  (∀ X X' (N : B) (f : X ⟶ X'),
    (TR.map f).app (Res.obj (DerivedCategory.Q.obj
      ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj N))) ≫ (e X' N).hom =
    (e X N).hom ≫ Res.map ((TS.map (E.map f)).app
      (DerivedCategory.Q.obj ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj N)))) ∧
  (∀ X (N N' : B) (g : N ⟶ N'),
    (TR.obj X).map (Res.map (DerivedCategory.Q.map
      ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).map g))) ≫ (e X N').hom =
    (e X N).hom ≫ Res.map ((TS.obj (E.obj X)).map
      (DerivedCategory.Q.map ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).map g))))

set_option hygiene false in
local notation "𝓜" A:arg => ringedSiteModules.{r}
  ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A)

set_option backward.isDefEq.respectTransparency true

section TensorProof

set_option backward.isDefEq.respectTransparency false in
private abbrev siteSectionModule (A : Sheaf J CommRingCat.{r}) (M : 𝓜 A) (V : Cᵒᵖ) :
    Module (A.obj.obj V) (M.val.obj V) :=
  ModuleCat.isModule (M.val.obj V)

attribute [local instance] siteSectionModule

/-- The recorded tensor on homotopy categories, with its type made explicit.
Source: Stacks, Tag 06YU (blueprint: lem-trf-site-derived-tensor-restriction). -/
private abbrev tensorDescentHomotopyFunctor [HasDerivedCategory.{w} (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))] :
    HomotopyCategory (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (.up ℤ) ×
    HomotopyCategory (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (.up ℤ) ⥤
    HomotopyCategory (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (.up ℤ) :=
  (SheafOfModules.siteHomotopyTensorExistsIndependentCoefficients.{u, v, r, w} J R).choose

private theorem tensorDescentClass_spec
    [HasDerivedCategory.{w} (𝓜 R)]
    (X : HomotopyCategory (𝓜 R) (.up ℤ)) :
    tensorDescentClass.{u, v, r, w} (R := R) X ↔
      TensorFlatRepresentative (J := J) (R := R) X.as :=
  (SheafOfModules.site_derived_tensor_descent_independentCoefficients.{u, v, r, w, 0, 0}
    J R).choose_spec.1 X

private theorem tensorSheafificationNaturality
    (A : Sheaf J CommRingCat.{r})
    {M M' N N' : 𝓜 A} (f : M ⟶ M') (g : N ⟶ N') :
    letI := SheafOfModules.monoidalCategory A
    tensorHom f g ≫ (SheafOfModules.tensorObjIsoSheafification M' N').hom =
      (SheafOfModules.tensorObjIsoSheafification M N).hom ≫
        (PresheafOfModules.sheafification (𝟙 ((sheafCompose J
          (forget₂ CommRingCat.{r} RingCat.{r})).obj A).obj)).map (tensorHom f.val g.val) := by
  exact SheafOfModules.changeOfRingsTensorIso_naturality_independentCoefficients A f g

private def tensorSwap (A : Sheaf J CommRingCat.{r}) (M N : 𝓜 A) :
    (SheafOfModules.monoidalCategory A).tensorObj M N ≅
      (SheafOfModules.monoidalCategory A).tensorObj N M :=
  SheafOfModules.tensorObjIsoSheafification M N ≪≫
    (PresheafOfModules.sheafification (𝟙 ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj A).obj)).mapIso (β_ M.val N.val) ≪≫
    (SheafOfModules.tensorObjIsoSheafification N M).symm

private theorem tensorSwap_tmul (M N : 𝓜 R) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) :
    (tensorSwap R M N).hom.val.app U (siteMonoidalTmul M N U x y) =
      siteMonoidalTmul N M U y x := by
  let O := (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R
  let a := PresheafOfModules.sheafification (𝟙 O.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 O.obj)
  let e := SheafOfModules.tensorObjIsoSheafification M N
  let e' := SheafOfModules.tensorObjIsoSheafification N M
  let t := (adj.unit.app (tensorObj M.val N.val)).app U (x ⊗ₜ[R.obj.obj U] y)
  have hi : e.hom.val.app U (e.inv.val.app U t) = t :=
    congrArg (fun f ↦ f.val.app U t) e.inv_hom_id
  have hn := congrArg (fun f ↦ (f.app U) (x ⊗ₜ[R.obj.obj U] y))
    (adj.unit.naturality (β_ M.val N.val).hom)
  change (adj.unit.app (tensorObj N.val M.val)).app U (y ⊗ₜ[R.obj.obj U] x) =
    (a.map (β_ M.val N.val).hom).val.app U t at hn
  change e'.inv.val.app U
    ((a.map (β_ M.val N.val).hom).val.app U (e.hom.val.app U (e.inv.val.app U t))) = _
  rw [hi, ← hn]
  rfl

private theorem tensorSwap_inv_tmul (M N : 𝓜 R) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) :
    (tensorSwap R M N).inv.val.app U (siteMonoidalTmul N M U y x) =
      siteMonoidalTmul M N U x y := by
  rw [← tensorSwap_tmul M N U x y]
  exact congrArg (fun f ↦ f.val.app U (siteMonoidalTmul M N U x y))
    (tensorSwap R M N).hom_inv_id

private theorem tensorSwap_naturality
    (A : Sheaf J CommRingCat.{r}) {M M' N N' : 𝓜 A} (f : M ⟶ M') (g : N ⟶ N') :
    (SheafOfModules.monoidalCategory A).tensorHom f g ≫ (tensorSwap A M' N').hom =
      (tensorSwap A M N).hom ≫ (SheafOfModules.monoidalCategory A).tensorHom g f := by
  let := SheafOfModules.monoidalCategory A
  let a := PresheafOfModules.sheafification (𝟙 ((sheafCompose J
    (forget₂ CommRingCat.{r} RingCat.{r})).obj A).obj)
  apply (cancel_mono (SheafOfModules.tensorObjIsoSheafification N' M').hom).mp
  simp only [tensorSwap, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [reassoc_of% (tensorSheafificationNaturality A f g),
    tensorSheafificationNaturality A g f]
  simp only [Iso.inv_hom_id_assoc]
  rw [← a.map_comp, ← a.map_comp]
  congr 2
  exact BraidedCategory.braiding_naturality f.val g.val

private theorem tensorMap_tmul {M M' N N' : 𝓜 R} (f : M ⟶ M') (g : N ⟶ N')
    (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    ((SheafOfModules.monoidalCategory R).tensorHom f g).val.app U
      (siteMonoidalTmul M N U x y) =
    siteMonoidalTmul M' N' U (f.val.app U x) (g.val.app U y) := by
  let O := (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 O.obj)
  let e := SheafOfModules.tensorObjIsoSheafification M N
  let e' := SheafOfModules.tensorObjIsoSheafification M' N'
  let t := (adj.unit.app (tensorObj M.val N.val)).app U (x ⊗ₜ[R.obj.obj U] y)
  have h := tensorSheafificationNaturality R f g
  have h' : e.inv ≫ (SheafOfModules.monoidalCategory R).tensorHom f g =
      (PresheafOfModules.sheafification (𝟙 O.obj)).map (tensorHom f.val g.val) ≫ e'.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hn := congrArg (fun k ↦ (k.app U) (x ⊗ₜ[R.obj.obj U] y))
    (adj.unit.naturality (tensorHom f.val g.val))
  change (adj.unit.app (tensorObj M'.val N'.val)).app U
      ((f.val.app U x) ⊗ₜ[R.obj.obj U] (g.val.app U y)) =
    ((PresheafOfModules.sheafification (𝟙 O.obj)).map (tensorHom f.val g.val)).val.app U t at hn
  change ((e.inv ≫ (SheafOfModules.monoidalCategory R).tensorHom f g).val.app U) t = _
  rw [h']
  change e'.inv.val.app U
    (((PresheafOfModules.sheafification (𝟙 O.obj)).map (tensorHom f.val g.val)).val.app U t) = _
  rw [← hn]
  rfl

-- The two coefficient actions require explicit tensor comparison equations.
private theorem ordinaryTensorCancellation (φ : R ⟶ S)
    (E₀ : 𝓜 R ⥤ 𝓜 S)
    (hobj : ∀ M, E₀.obj M = SheafOfModules.changeOfRings φ M)
    (hmap : ∀ {M M' : 𝓜 R} (f : M ⟶ M'),
      E₀.map f = eqToHom (hobj M) ≫ SheafOfModules.changeOfRingsHom φ M f ≫
        eqToHom (hobj M').symm) :
    ∃ e : ∀ (M : 𝓜 R) (N : 𝓜 S),
      (SheafOfModules.monoidalCategory R).tensorObj M ((siteTensorRestriction φ).obj N) ≅
      (siteTensorRestriction φ).obj ((SheafOfModules.monoidalCategory S).tensorObj (E₀.obj M) N),
      (∀ {M M' : 𝓜 R} {N N' : 𝓜 S} (f : M ⟶ M') (g : N ⟶ N'),
        (SheafOfModules.monoidalCategory R).tensorHom f ((siteTensorRestriction φ).map g) ≫
          (e M' N').hom = (e M N).hom ≫ (siteTensorRestriction φ).map
            ((SheafOfModules.monoidalCategory S).tensorHom (E₀.map f) g)) ∧
      (∀ (M : 𝓜 R) (N : 𝓜 S) (U : Cᵒᵖ) (x : M.val.obj U)
        (s : S.obj.obj U) (n : N.val.obj U),
        (e M N).inv.val.app U
          (siteMonoidalTmul (E₀.obj M) N U (siteExtensionTmul φ M E₀ hobj U x s) n) =
        siteMonoidalTmul M ((siteTensorRestriction φ).obj N) U x (s • n)) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  let U : 𝓜 S ⥤ 𝓜 R := siteTensorRestriction φ
  obtain ⟨k, hk, hksec⟩ := SheafOfModules.exists_changeOfRings_tensorCancellation_sections φ
  let k' (N : 𝓜 S) (M : 𝓜 R) :
      U.obj (tensorObj N (E₀.obj M)) ≅ tensorObj (U.obj N) M :=
    U.mapIso (((curriedTensor _).obj N).mapIso (eqToIso (hobj M))) ≪≫ k N M
  have hknat {N N' : 𝓜 S} {M M' : 𝓜 R} (g : N ⟶ N') (f : M ⟶ M') :
      U.map (tensorHom g (E₀.map f)) ≫ (k' N' M').hom =
        (k' N M).hom ≫ tensorHom (U.map g) f := by
    have hs : tensorHom g (E₀.map f) ≫ (N' ◁ eqToHom (hobj M')) =
        (N ◁ eqToHom (hobj M)) ≫ tensorHom g (SheafOfModules.changeOfRingsHom φ M f) := by
      rw [← id_tensorHom, ← id_tensorHom, tensorHom_comp_tensorHom,
        tensorHom_comp_tensorHom]
      simp only [Category.comp_id, Category.id_comp, hmap, Category.assoc,
        eqToHom_trans, eqToHom_refl]
    change U.map (tensorHom g (E₀.map f)) ≫ U.map (N' ◁ eqToHom (hobj M')) ≫
        (k N' M').hom = U.map (N ◁ eqToHom (hobj M)) ≫ (k N M).hom ≫ tensorHom (U.map g) f
    rw [← U.map_comp_assoc, hs, U.map_comp, Category.assoc, hk g f]
  have hkinv {N N' : 𝓜 S} {M M' : 𝓜 R} (g : N ⟶ N') (f : M ⟶ M') :
      tensorHom (U.map g) f ≫ (k' N' M').inv =
        (k' N M).inv ≫ U.map (tensorHom g (E₀.map f)) := by
    apply (cancel_epi (k' N M).hom).mp
    rw [← Category.assoc, ← hknat g f]
    simp
  let e (M : 𝓜 R) (N : 𝓜 S) := tensorSwap R M (U.obj N) ≪≫
    (k' N M).symm ≪≫ U.mapIso (tensorSwap S N (E₀.obj M))
  refine ⟨e, ?_, ?_⟩
  · intro M M' N N' f g
    change tensorHom f (U.map g) ≫ (tensorSwap R M' (U.obj N')).hom ≫
        (k' N' M').inv ≫ U.map (tensorSwap S N' (E₀.obj M')).hom =
      (tensorSwap R M (U.obj N)).hom ≫ (k' N M).inv ≫
        U.map (tensorSwap S N (E₀.obj M)).hom ≫ U.map (tensorHom (E₀.map f) g)
    rw [reassoc_of% (tensorSwap_naturality R f (U.map g)), reassoc_of% (hkinv g f)]
    rw [← U.map_comp, ← U.map_comp, tensorSwap_naturality S g (E₀.map f)]
  · intro M N V x s n
    have ht : (eqToHom (hobj M)).val.app V (siteExtensionTmul φ M E₀ hobj V x s) =
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S).obj)).unit.app
          (SheafOfModules.changeOfRingsPresheaf φ M)).app V)
            (s ⊗ₜ[R.obj.obj V,(φ.hom.app V).hom] x) := by
      unfold siteExtensionTmul
      change (((eqToHom (hobj M).symm ≫ eqToHom (hobj M)).val.app V) _) = _
      rw [eqToHom_trans, eqToHom_refl]
      rfl
    change (tensorSwap R M (U.obj N)).inv.val.app V
      ((k N M).hom.val.app V
        ((N ◁ eqToHom (hobj M)).val.app V
          ((tensorSwap S N (E₀.obj M)).inv.val.app V
            (siteMonoidalTmul (E₀.obj M) N V (siteExtensionTmul φ M E₀ hobj V x s) n)))) = _
    rw [tensorSwap_inv_tmul, ← id_tensorHom, tensorMap_tmul, ht]
    change (tensorSwap R M (U.obj N)).inv.val.app V
      ((k N M).hom.val.app V
        (siteMonoidalTmul N (SheafOfModules.changeOfRings φ M) V n _)) = _
    rw [show (k N M).hom.val.app V
        (siteMonoidalTmul N (SheafOfModules.changeOfRings φ M) V n _) =
        siteMonoidalTmul (U.obj N) M V (s • n) x from hksec N M V n s x]
    exact tensorSwap_inv_tmul M (U.obj N) V x (s • n)

private theorem tensorLeftQuasiIsoAux
    {A : Type*} [Category* A] [Abelian A] [MonoidalCategory A] [SymmetricCategory A]
    [MonoidalPreadditive A] [Limits.HasColimitsOfSize.{0, 0} A]
    {K E E' : CochainComplex A ℤ} (α : E ⟶ E') (hα : QuasiIso α)
    (hK : ∀ F : CochainComplex A ℤ, F.Acyclic →
      (CochainComplex.mapBifunctor F K (MonoidalCategory.curriedTensor A)).Acyclic) :
    QuasiIso (HomologicalComplex.mapBifunctorMap (𝟙 K) α
      (MonoidalCategory.curriedTensor A) (.up ℤ)) := by
  have hc := (CochainComplex.mappingCone.quasiIso_iff_acyclic α).1 hα
  have ht := hK (CochainComplex.mappingCone α) hc
  let F := MonoidalCategory.curriedTensor A
  let e : (((F.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
      (CochainComplex.mappingCone α)).obj K) ≅
      (((F.flip.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
      (CochainComplex.mappingCone α)).obj K) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun p ↦ HomologicalComplex.Hom.isoOfComponents
        (fun q ↦ β_ ((CochainComplex.mappingCone α).X p) (K.X q)) (by
          intro q q' hqq'
          exact (BraidedCategory.braiding_naturality_right
            ((CochainComplex.mappingCone α).X p) (K.d q q')).symm)) (by
        intro p p' hpp'
        ext q : 1
        exact (BraidedCategory.braiding_naturality_left
          ((CochainComplex.mappingCone α).d p p') (K.X q)).symm)
  have ht' : (CochainComplex.mapBifunctor K (CochainComplex.mappingCone α) F).Acyclic := by
    intro i
    exact (ht i).of_iso (HomologicalComplex₂.total.mapIso e (.up ℤ) ≪≫
      HomologicalComplex.mapBifunctorFlipIso K (CochainComplex.mappingCone α) F (.up ℤ))
  apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
  intro i
  exact (ht' i).of_iso (CochainComplex.mapBifunctorMappingCone₂Iso K α F)


private theorem tensorLeftQuasiIso
    {K X Y : CochainComplex (𝓜 R) ℤ} (f : X ⟶ Y)
    (hf : QuasiIso f) (hK : CochainComplex.IsKFlatIndependentCoefficients K) :
    QuasiIso (((SiteTensorComplexFunctor R).obj K).map f) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.cochainModulesPreadditive R
  exact tensorLeftQuasiIsoAux f hf hK

private theorem extendTensorComparison
    {A B D F : Type*} [Category* A] [Category* B] [Category* D] [Category* F]
    (i : A ⥤ B) (Q : B ⥤ D) (V : MorphismProperty A) (W : MorphismProperty B)
    [Q.IsLocalization W] [(i ⋙ Q).IsLocalization V]
    (T : B ⥤ F) (hT : W.IsInvertedBy T) (G : D ⥤ F)
    (e : (i ⋙ Q) ⋙ G ≅ i ⋙ T) :
    ∃ c : Q ⋙ G ≅ T, ∀ X, c.hom.app (i.obj X) = e.hom.app X := by
  let H := Localization.lift T hT Q
  let q : Q ⋙ H ≅ T := Localization.fac T hT Q
  let f := Localization.fullyFaithfulWhiskeringLeft (i ⋙ Q) V F
  let t : G ≅ H := f.preimageIso (e ≪≫ (Functor.isoWhiskerLeft i q).symm)
  refine ⟨Functor.isoWhiskerLeft Q t ≪≫ q, ?_⟩
  intro X
  have ht := congr_app (f.map_preimage (e ≪≫ (Functor.isoWhiskerLeft i q).symm).hom) X
  change t.hom.app (Q.obj (i.obj X)) = e.hom.app X ≫ q.inv.app (i.obj X) at ht
  change t.hom.app (Q.obj (i.obj X)) ≫ q.hom.app (i.obj X) = _
  rw [ht]
  simp

private theorem tensorResolvingLocalization
    [HasDerivedCategory.{w} (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))] :
    ((tensorDescentClass.{u, v, r, w} (R := R)).ι ⋙ DerivedCategory.Qh).IsLocalization
      ((HomotopyCategory.quasiIso _ (.up ℤ)).inverseImage
        (tensorDescentClass.{u, v, r, w} (R := R)).ι) := by
  unfold tensorDescentClass
  let d := SheafOfModules.site_derived_tensor_descent_independentCoefficients.{u, v, r, w, 0, 0}
    J R
  let V := (HomotopyCategory.quasiIso _ (.up ℤ)).inverseImage d.choose.ι
  let F := d.choose_spec.2.1.choose
  have : F.IsEquivalence := d.choose_spec.2.1.choose_spec.1
  have : (V.Q ⋙ F).IsLocalization V := inferInstance
  exact Functor.IsLocalization.of_iso V d.choose_spec.2.1.choose_spec.2.some

private theorem isIso_of_comp_equation
    {A : Type*} [Category* A] {X Y Z W : A}
    (f : X ⟶ Y) (b : Y ⟶ Z) (a : X ⟶ W) (c : W ⟶ Z)
    (h : f ≫ b = a ≫ c) (ha : IsIso a) (hb : IsIso b) (hc : IsIso c) : IsIso f := by
  have : IsIso (f ≫ b) := by rw [h]; infer_instance
  exact IsIso.of_isIso_comp_right f b

private theorem tensorMixedComparison
    [HasDerivedCategory.{w} (𝓜 R)] :
    let P := tensorDescentClass.{u, v, r, w} (R := R)
    let B := tensorDescentHomotopyFunctor.{u, v, r, w} (R := R)
    let L := P.ι ⋙ (DerivedCategory.Qh : HomotopyCategory (𝓜 R) (.up ℤ) ⥤ _)
    ∃ c : ((𝟭 P.FullSubcategory).prod DerivedCategory.Qh) ⋙
        (L.prod (𝟭 _)) ⋙ SheafOfModules.siteDerivedTensorIndependentCoefficients.{u, v, r, w} J R ≅
        (P.ι.prod (𝟭 _)) ⋙ B ⋙ DerivedCategory.Qh,
      ∀ p q, c.hom.app (p, q.obj) =
        (tensorDescentDerivedIso.{u, v, r, w} (R := R)).inv.app (p, q) := by
  dsimp only
  let P := tensorDescentClass.{u, v, r, w} (R := R)
  let B := tensorDescentHomotopyFunctor.{u, v, r, w} (R := R)
  let H := HomotopyCategory.quotient (𝓜 R) (.up ℤ)
  let Q := DerivedCategory.Qh (C := 𝓜 R)
  let L := P.ι ⋙ Q
  let V := (HomotopyCategory.quasiIso (𝓜 R) (.up ℤ)).inverseImage P.ι
  let W := HomotopyCategory.quasiIso (𝓜 R) (.up ℤ)
  have : L.IsLocalization V := tensorResolvingLocalization (J := J) (R := R)
  let F := (P.ι.prod (𝟭 _)) ⋙ B ⋙ Q
  have hinv (p : P.FullSubcategory) {X Y : HomotopyCategory (𝓜 R) (.up ℤ)}
      (f : X ⟶ Y) (hf : W f) :
      IsIso (Q.map (B.map (X := (p.obj, X)) (Y := (p.obj, Y)) (𝟙 p.obj, f))) := by
    let K := p.obj.as
    let g := f.out
    have hg : QuasiIso g := by
      apply (HomotopyCategory.quotient_map_mem_quasiIso_iff g).1
      change W ((HomotopyCategory.quotient (𝓜 R) (.up ℤ)).map f.out)
      rw [HomotopyCategory.quotient_map_out]
      exact hf
    have hK : CochainComplex.IsKFlatIndependentCoefficients K :=
      ((tensorDescentClass_spec (J := J) (R := R) p.obj).1 p.property).1
    have ht := tensorLeftQuasiIso (J := J) (R := R) g hg hK
    let t := ((SiteTensorComplexFunctor R).obj K).map g
    have hQt : IsIso (Q.map (H.map t)) := Localization.inverts Q W _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff t).2 ht)
    let e := tensorDescentComplexIso.{u, v, r, w} (R := R)
    have hQeX : IsIso (Q.map (e.hom.app (K, X.as))) :=
      inferInstanceAs (IsIso (Q.mapIso (e.app (K, X.as))).hom)
    have hQeY : IsIso (Q.map (e.hom.app (K, Y.as))) :=
      inferInstanceAs (IsIso (Q.mapIso (e.app (K, Y.as))).hom)
    have he := congrArg Q.map (e.hom.naturality (X := (K, X.as)) (Y := (K, Y.as)) (𝟙 K, g))
    simp only [Functor.map_comp, Functor.comp_map, Functor.prod_map] at he
    simp only [Functor.map_id, g, HomotopyCategory.quotient_map_out,
      Functor.uncurry_obj_map, NatTrans.id_app, Category.id_comp] at he
    change Q.map (B.map (X := (p.obj, X)) (Y := (p.obj, Y)) (𝟙 p.obj, f)) ≫
        Q.map (e.hom.app (K, Y.as)) =
      Q.map (e.hom.app (K, X.as)) ≫ Q.map (H.map t) at he
    exact isIso_of_comp_equation _ _ _ _ he hQeX hQeY hQt
  have hF : ((MorphismProperty.isomorphisms P.FullSubcategory).prod W).IsInvertedBy F := by
    intro X Y f hf
    have : IsIso f.1 := hf.1
    have hh : f = ((f.1, 𝟙 X.2) : X ⟶ (Y.1, X.2)) ≫
        ((𝟙 Y.1, f.2) : (Y.1, X.2) ⟶ Y) := by ext <;> simp
    rw [hh, F.map_comp]
    have : IsIso (Prod.mkHom f.1 (𝟙 X.2)) := (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
    have : IsIso (F.map (Prod.mkHom f.1 (𝟙 X.2))) := inferInstance
    have : IsIso (F.map (X := (Y.1, X.2)) (Y := Y) (𝟙 Y.1, f.2)) := hinv Y.1 f.2 hf.2
    infer_instance
  have : (((𝟭 P.FullSubcategory).prod P.ι) ⋙
      ((𝟭 P.FullSubcategory).prod Q)).IsLocalization
      ((MorphismProperty.isomorphisms P.FullSubcategory).prod V) :=
    inferInstanceAs (((𝟭 P.FullSubcategory).prod L).IsLocalization _)
  obtain ⟨c, hc⟩ := extendTensorComparison ((𝟭 P.FullSubcategory).prod P.ι)
    ((𝟭 P.FullSubcategory).prod Q)
    ((MorphismProperty.isomorphisms P.FullSubcategory).prod V)
    ((MorphismProperty.isomorphisms P.FullSubcategory).prod W) F hF
    ((L.prod (𝟭 _)) ⋙ SheafOfModules.siteDerivedTensorIndependentCoefficients.{u, v, r, w} J R)
    (tensorDescentDerivedIso.{u, v, r, w} (R := R)).symm
  exact ⟨c, fun p q ↦ hc (p, q)⟩

private theorem tensorOneSidedComparison
    [HasDerivedCategory.{w} (𝓜 R)] :
    ∃ c : OneSidedTensorComparison (J := J) (R := R),
      CanonicalOneSidedTensorComparison (J := J) (R := R) c ∧
      ∀ (P P' : CochainComplex (𝓜 R) ℤ) (hP : TensorFlatRepresentative (J := J) (R := R) P)
        (hP' : TensorFlatRepresentative (J := J) (R := R) P') (f : P ⟶ P')
        (Q : CochainComplex (𝓜 R) ℤ),
        ((siteRestrictionDerivedTensor (R := R)).map (DerivedCategory.Q.map f)).app
            (DerivedCategory.Q.obj Q) ≫ (c P' hP' Q).hom =
          (c P hP Q).hom ≫
            DerivedCategory.Q.map (((SiteTensorComplexFunctor R).map f).app Q) := by
  let A := 𝓜 R
  let P := tensorDescentClass.{u, v, r, w} (R := R)
  let H := HomotopyCategory.quotient A (.up ℤ)
  let Q := DerivedCategory.Q (C := A)
  let Qh := DerivedCategory.Qh (C := A)
  let T := SheafOfModules.siteDerivedTensorIndependentCoefficients.{u, v, r, w} J R
  let PC : ObjectProperty (CochainComplex A ℤ) := TensorFlatRepresentative (J := J) (R := R)
  let I : PC.FullSubcategory ⥤ P.FullSubcategory :=
    { obj := fun p ↦ ⟨H.obj p.obj, (tensorDescentClass_spec (J := J) (R := R) _).2 p.property⟩
      map := fun f ↦ ObjectProperty.homMk (H.map f.hom)
      map_id := by intro p; ext; exact H.map_id p.obj
      map_comp := by intro p q r f g; ext; exact H.map_comp f.hom g.hom }
  obtain ⟨cm, hcm⟩ := tensorMixedComparison (R := R)
  let a := DerivedCategory.quotientCompQhIso A
  let b : (PC.ι.prod (𝟭 _)) ⋙ (Q.prod Q) ⋙ T ≅
      (PC.ι.prod (𝟭 _)) ⋙ Functor.uncurry.obj (SiteTensorComplexFunctor R) ⋙ Q :=
    Functor.isoWhiskerLeft (PC.ι.prod (𝟭 _))
      (Functor.isoWhiskerRight (NatIso.prod a.symm a.symm) T) ≪≫
    Functor.isoWhiskerLeft (I.prod H) cm ≪≫
    Functor.isoWhiskerLeft (PC.ι.prod (𝟭 _))
      (Functor.isoWhiskerRight (tensorDescentComplexIso.{u, v, r, w} (R := R)) Qh) ≪≫
    Functor.isoWhiskerLeft
      ((PC.ι.prod (𝟭 _)) ⋙ Functor.uncurry.obj (SiteTensorComplexFunctor R)) a
  let c : OneSidedTensorComparison (J := J) (R := R) := fun X hX Y ↦ b.app (⟨X, hX⟩, Y)
  refine ⟨c, ⟨?_, ?_⟩, ?_⟩
  · intro X hX Y Y' f
    have h := b.hom.naturality (Prod.mkHom (𝟙 (⟨X, hX⟩ : PC.FullSubcategory)) f)
    change T.map (Prod.mkHom (Q.map (𝟙 X)) (Q.map f)) ≫
        (c X hX Y').hom = (c X hX Y).hom ≫
        Q.map (((SiteTensorComplexFunctor R).map (𝟙 X)).app Y ≫
          ((SiteTensorComplexFunctor R).obj X).map f) at h
    change T.map (Prod.mkHom (𝟙 (Q.obj X)) (Q.map f)) ≫ _ = _
    simpa only [Functor.map_id, NatTrans.id_app, Category.id_comp] using h
  · intro X Y hX hY
    apply Iso.ext
    change (b.app (⟨X, hX⟩, Y)).hom = (tensorDescentPair X Y hX hY).inv
    change T.map (Prod.mkHom (a.inv.app X) (a.inv.app Y)) ≫
        cm.hom.app (I.obj ⟨X, hX⟩, H.obj Y) ≫
        Qh.map ((tensorDescentComplexIso.{u, v, r, w} (R := R)).hom.app (X, Y)) ≫
        a.hom.app (((SiteTensorComplexFunctor R).obj X).obj Y) = _
    rw [hcm (I.obj ⟨X, hX⟩) ⟨H.obj Y, (tensorDescentClass_spec (J := J) (R := R) _).2 hY⟩]
    dsimp only [tensorDescentPair, Iso.trans, Iso.symm, Functor.mapIso, Iso.app, Iso.prod]
    set_option backward.isDefEq.respectTransparency false in
      simp only [Category.assoc]
    set_option backward.isDefEq.respectTransparency false in
      rfl
  · intro X X'   hX hX' f Y
    have h := b.hom.naturality
      (Prod.mkHom (ObjectProperty.homMk f :
        (⟨X, hX⟩ : PC.FullSubcategory) ⟶ ⟨X', hX'⟩) (𝟙 Y))
    change T.map (Prod.mkHom (Q.map f) (Q.map (𝟙 Y))) ≫
        (c X' hX' Y).hom = (c X hX Y).hom ≫
        Q.map (((SiteTensorComplexFunctor R).map f).app Y ≫
          ((SiteTensorComplexFunctor R).obj X').map (𝟙 Y)) at h
    change T.map (Prod.mkHom (Q.map f) (𝟙 (Q.obj Y))) ≫ _ = _
    simpa only [Functor.map_id, Category.comp_id] using h

private def flatComplexProperty : ObjectProperty (CochainComplex (𝓜 R) ℤ) :=
  TensorFlatRepresentative (J := J) (R := R)

private def tensorComparisonBifunctorIso
    [HasDerivedCategory.{w} (𝓜 R)]
    {A B : Type*} [Category* A] [Category* B]
    (F : A ⥤ CochainComplex (𝓜 R) ℤ)
    (hF : ∀ X, TensorFlatRepresentative (J := J) (R := R) (F.obj X))
    (G : B ⥤ CochainComplex (𝓜 R) ℤ)
    (c : OneSidedTensorComparison (J := J) (R := R))
    (hc : CanonicalOneSidedTensorComparison (J := J) (R := R) c)
    (hn : ∀ (P P' : CochainComplex (𝓜 R) ℤ)
      (hP : TensorFlatRepresentative (J := J) (R := R) P)
      (hP' : TensorFlatRepresentative (J := J) (R := R) P')
      (f : P ⟶ P') (Q : CochainComplex (𝓜 R) ℤ),
      ((siteRestrictionDerivedTensor (R := R)).map (DerivedCategory.Q.map f)).app
          (DerivedCategory.Q.obj Q) ≫ (c P' hP' Q).hom =
        (c P hP Q).hom ≫
          DerivedCategory.Q.map (((SiteTensorComplexFunctor R).map f).app Q)) :
    ((F ⋙ DerivedCategory.Q).prod (G ⋙ DerivedCategory.Q)) ⋙
        SheafOfModules.siteDerivedTensorIndependentCoefficients.{u, v, r, w} J R ≅
      (F.prod G) ⋙ Functor.uncurry.obj (SiteTensorComplexFunctor R) ⋙ DerivedCategory.Q := by
  let T := siteRestrictionDerivedTensor (R := R)
  let Q := DerivedCategory.Q (C := 𝓜 R)
  refine NatIso.ofComponents (fun X ↦ c (F.obj X.1) (hF X.1) (G.obj X.2)) ?_
  intro X Y f
  change (SheafOfModules.siteDerivedTensorIndependentCoefficients.{u, v, r, w} J R).map
      (Prod.mkHom (Q.map (F.map f.1)) (Q.map (G.map f.2))) ≫ _ = _
  have ht : (SheafOfModules.siteDerivedTensorIndependentCoefficients.{u, v, r, w} J R).map
      (Prod.mkHom (Q.map (F.map f.1)) (Q.map (G.map f.2))) =
      (T.map (Q.map (F.map f.1))).app (Q.obj (G.obj X.2)) ≫
        (T.obj (Q.obj (F.obj Y.1))).map (Q.map (G.map f.2)) := by
    change (SheafOfModules.siteDerivedTensorIndependentCoefficients.{u, v, r, w} J R).map _ =
      (SheafOfModules.siteDerivedTensorIndependentCoefficients.{u, v, r, w} J R).map
          (Prod.mkHom (Q.map (F.map f.1)) (𝟙 (Q.obj (G.obj X.2)))) ≫
        (SheafOfModules.siteDerivedTensorIndependentCoefficients.{u, v, r, w} J R).map
          (Prod.mkHom (𝟙 (Q.obj (F.obj Y.1))) (Q.map (G.map f.2)))
    rw [← Functor.map_comp]
    congr 1
    ext <;> simp
  rw [ht, Category.assoc, hc.1, ← Category.assoc, hn, Category.assoc, ← Q.map_comp]
  rfl

private def tensorFlatWhiskeringAux
    {A₀ : Type*} [Category* A₀] [Abelian A₀] [HasDerivedCategory A₀]
    (PC : ObjectProperty (CochainComplex A₀ ℤ))
    (P : ObjectProperty (HomotopyCategory A₀ (.up ℤ)))
    (hP : ∀ X, P X ↔ PC X.as)
    (hL : (P.ι ⋙ (DerivedCategory.Qh : HomotopyCategory A₀ (.up ℤ) ⥤ _)).IsLocalization
      ((HomotopyCategory.quasiIso A₀ (.up ℤ)).inverseImage P.ι))
    (A D : Type*) [Category* A] [Category* D] :
    ((Functor.whiskeringLeft _ _ D).obj
      ((PC.ι ⋙ DerivedCategory.Q).prod (𝟭 A))).FullyFaithful := by
  let H := HomotopyCategory.quotient (A₀) (.up ℤ)
  let Qh := DerivedCategory.Qh (C := A₀)
  let I : PC.FullSubcategory ⥤ P.FullSubcategory :=
    { obj := fun p ↦ ⟨H.obj p.obj, (hP _).2 p.property⟩
      map := fun f ↦ ObjectProperty.homMk (H.map f.hom)
      map_id := by intro p; ext; exact H.map_id p.obj
      map_comp := by intro p q r f g; ext; exact H.map_comp f.hom g.hom }
  let L := P.ι ⋙ Qh
  let V := (HomotopyCategory.quasiIso (A₀) (.up ℤ)).inverseImage P.ι
  have : L.IsLocalization V := hL
  let ffI : ((Functor.whiskeringLeft _ _ D).obj (I.prod (𝟭 A))).FullyFaithful :=
    { preimage := fun {F G} τ ↦
        { app := fun X ↦ τ.app (⟨X.1.obj.as, (hP _).1 X.1.property⟩, X.2)
          naturality := by
            intro X Y f
            let Xc : PC.FullSubcategory :=
              ⟨X.1.obj.as, (hP _).1 X.1.property⟩
            let Yc : PC.FullSubcategory :=
              ⟨Y.1.obj.as, (hP _).1 Y.1.property⟩
            let f' : Xc ⟶ Yc := ObjectProperty.homMk f.1.hom.out
            have hm : I.map f' = f.1 := by
              apply ObjectProperty.hom_ext
              exact HomotopyCategory.quotient_map_out _
            have h := τ.naturality (Prod.mkHom f' f.2)
            change F.map (Prod.mkHom (I.map f') f.2) ≫ τ.app (Yc, Y.2) =
              τ.app (Xc, X.2) ≫ G.map (Prod.mkHom (I.map f') f.2) at h
            rw [hm] at h
            exact h }
      map_preimage := by intros; ext X; rfl
      preimage_map := by intros; ext X; rfl }
  let ffL := Localization.fullyFaithfulWhiskeringLeft (L.prod (𝟭 A))
    (V.prod (MorphismProperty.isomorphisms A)) D
  let ff := ffL.comp ffI
  let a : I ⋙ L ≅ PC.ι ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerLeft PC.ι (DerivedCategory.quotientCompQhIso (A₀))
  exact ff.ofIso ((Functor.whiskeringLeft _ _ D).mapIso
    (NatIso.prod a (Iso.refl (𝟭 A))))


private def tensorFlatWhiskering
    [HasDerivedCategory.{w} (𝓜 R)]
    (A D : Type*) [Category* A] [Category* D] :
    ((Functor.whiskeringLeft _ _ D).obj
      (((flatComplexProperty (R := R)).ι ⋙ DerivedCategory.Q).prod (𝟭 A))).FullyFaithful :=
  tensorFlatWhiskeringAux (flatComplexProperty (R := R))
    (tensorDescentClass.{u, v, r, w} (R := R))
    (tensorDescentClass_spec (J := J) (R := R))
    (tensorResolvingLocalization (J := J) (R := R)) A D

private theorem tensorComparison_naturality
    {B : Type*} [Category* B]
    {D₁ D₂ : Type*} [Category* D₁] [Category* D₂]
    (TR : D₁ × D₁ ⥤ D₁) (TS : D₂ × D₂ ⥤ D₂)
    (E : D₁ ⥤ D₂) (U : D₂ ⥤ D₁) (Z : B ⥤ D₂)
    (ei : ((𝟭 D₁).prod (Z ⋙ U)) ⋙ TR ≅ (E.prod Z) ⋙ TS ⋙ U) :
    (∀ (H H' : D₁) (N : B) (f : H ⟶ H'),
      ((Functor.curry.obj TR).map f).app (U.obj (Z.obj N)) ≫
        (ei.app (H', N)).hom =
      (ei.app (H, N)).hom ≫ U.map
        (((Functor.curry.obj TS).map (E.map f)).app (Z.obj N))) ∧
    (∀ (H : D₁) (N N' : B) (f : N ⟶ N'),
      ((Functor.curry.obj TR).obj H).map (U.map (Z.map f)) ≫
        (ei.app (H, N')).hom =
      (ei.app (H, N)).hom ≫ U.map
        (((Functor.curry.obj TS).obj (E.obj H)).map (Z.map f))) := by
  constructor
  · intro H H' N f
    simpa only [Functor.comp_map, Functor.prod_map, Functor.id_map, Functor.map_id,
      Iso.app_hom, Functor.curry_obj_obj_obj, Functor.curry_obj_map_app,
      Functor.comp_obj, Functor.prod_obj, Functor.id_obj]
      using ei.hom.naturality (Prod.mkHom f (𝟙 N))
  · intro H N N' f
    simpa only [Functor.comp_map, Functor.prod_map, Functor.id_map, Functor.map_id,
      Iso.app_hom, Functor.curry_obj_obj_obj, Functor.curry_obj_obj_map,
      Functor.comp_obj, Functor.prod_obj, Functor.id_obj]
      using ei.hom.naturality (Prod.mkHom (𝟙 H) f)

private theorem descendTensorComparison
    {A B D : Type*} [Category* A] [Category* B] [Category* D]
    (q : A ⥤ B) (ff : ((Functor.whiskeringLeft A B D).obj q).FullyFaithful)
    (F G : B ⥤ D) (c : q ⋙ F ≅ q ⋙ G) :
    ∃ e : F ≅ G, ∀ X, e.hom.app (q.obj X) = c.hom.app X := by
  refine ⟨ff.preimageIso c, ?_⟩
  intro X
  exact congr_app (ff.map_preimage c.hom) X

omit [EssentiallySmall.{r} C] in
private theorem restrictionColimits (φ : R ⟶ S) :
    PreservesColimitsOfSize.{0, 0} (siteTensorRestriction φ : 𝓜 S ⥤ 𝓜 R) := by
  let U : 𝓜 S ⥤ 𝓜 R := siteTensorRestriction φ
  have hcolim (D : Type) [Category.{0} D] : PreservesColimitsOfShape D U := by
    have : PreservesColimitsOfShape D (U ⋙ SheafOfModules.toSheaf.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :=
      inferInstanceAs (PreservesColimitsOfShape D (SheafOfModules.toSheaf.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S)))
    have : ReflectsColimitsOfShape D (SheafOfModules.toSheaf.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :=
      reflectsColimitsOfShape_of_reflectsIsomorphisms
    exact preservesColimitsOfShape_of_reflects_of_preserves U (SheafOfModules.toSheaf.{r} _)
  exact ⟨fun {D} instD ↦ @hcolim D instD⟩

private theorem tensorTotal_mapAux
    {A B D : Type*} [Category* A] [Category* B] [Category* D]
    [HasZeroMorphisms A] [HasZeroMorphisms B] [Preadditive D]
    (F : A ⥤ B ⥤ D) [F.PreservesZeroMorphisms]
    [∀ X, (F.obj X).PreservesZeroMorphisms]
    [∀ (P : CochainComplex A ℤ) (Q : CochainComplex B ℤ),
      HomologicalComplex.HasMapBifunctor P Q F (.up ℤ)]
    {P P' : CochainComplex A ℤ} {Q Q' : CochainComplex B ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    let T := F.map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)
    (T.map f).app Q ≫ (T.obj P').map g =
      HomologicalComplex.mapBifunctorMap f g F (.up ℤ) := by
  simp only [Functor.map₂HomologicalComplex, HomologicalComplex.mapBifunctorMap,
    Functor.map_id, NatTrans.id_app, Category.id_comp, Category.comp_id,
    ← HomologicalComplex₂.total.map_comp]

private theorem tensorTotal_map
    (A : Sheaf J CommRingCat.{r})
    {P P' Q Q' : CochainComplex (𝓜 A) ℤ} (f : P ⟶ P') (g : Q ⟶ Q') :
    letI := SheafOfModules.monoidalCategory A
    ((SiteTensorComplexFunctor A).map f).app Q ≫
        ((SiteTensorComplexFunctor A).obj P').map g =
      HomologicalComplex.mapBifunctorMap f g (curriedTensor (𝓜 A)) (.up ℤ) := by
  let := SheafOfModules.monoidalCategory A
  let := SheafOfModules.cochainModulesPreadditive A
  exact tensorTotal_mapAux (curriedTensor (𝓜 A)) f g

private def tensorCancellationBicomplexIso
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    [MonoidalCategory A] [MonoidalCategory B]
    [MonoidalPreadditive A] [MonoidalPreadditive B]
    (E₀ : A ⥤ B) [E₀.Additive] (U : B ⥤ A) [U.Additive]
    (a : ∀ (M : A) (N : B), M ⊗ U.obj N ≅ U.obj (E₀.obj M ⊗ N))
    (ha : ∀ {M M' : A} {N N' : B} (f : M ⟶ M') (g : N ⟶ N'),
      tensorHom f (U.map g) ≫ (a M' N').hom =
        (a M N).hom ≫ U.map (tensorHom (E₀.map f) g))
    (P : CochainComplex A ℤ) (Q : CochainComplex B ℤ) :
    let EC := E₀.mapHomologicalComplex (.up ℤ)
    let UC := U.mapHomologicalComplex (.up ℤ)
    let TR := (curriedTensor A).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)
    let TS := (curriedTensor B).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)
    (TR.obj P).obj (UC.obj Q) ≅
      (U.mapHomologicalComplex₂ (.up ℤ) (.up ℤ)).obj ((TS.obj (EC.obj P)).obj Q) := by
  exact HomologicalComplex.Hom.isoOfComponents
      (fun i ↦ HomologicalComplex.Hom.isoOfComponents
        (fun j ↦ a (P.X i) (Q.X j)) (by
          intro j j' hj
          change (a (P.X i) (Q.X j)).hom ≫
              U.map ((E₀.obj (P.X i)) ◁ Q.d j j') =
            (P.X i) ◁ U.map (Q.d j j') ≫ (a (P.X i) (Q.X j')).hom
          have h := ha (𝟙 (P.X i)) (Q.d j j')
          simpa only [E₀.map_id, id_tensorHom] using h.symm)) (by
        intro i i' hi
        ext j : 1
        change (a (P.X i) (Q.X j)).hom ≫
            U.map ((E₀.map (P.d i i')) ▷ (Q.X j)) =
          (P.d i i') ▷ U.obj (Q.X j) ≫ (a (P.X i') (Q.X j)).hom
        have h := ha (P.d i i') (𝟙 (Q.X j))
        simpa only [Functor.map_id, tensorHom_id] using h.symm)

private def tensorCancellationComplexIso
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    [MonoidalCategory A] [MonoidalCategory B]
    [MonoidalPreadditive A] [MonoidalPreadditive B]
    [HasColimitsOfSize.{0, 0} A] [HasColimitsOfSize.{0, 0} B]
    (E₀ : A ⥤ B) [E₀.Additive] (U : B ⥤ A) [U.Additive]
    [PreservesColimitsOfSize.{0, 0} U] (a : ∀ (M : A) (N : B), M ⊗ U.obj N ≅ U.obj (E₀.obj M ⊗ N))
    (ha : ∀ {M M' : A} {N N' : B} (f : M ⟶ M') (g : N ⟶ N'),
      tensorHom f (U.map g) ≫ (a M' N').hom =
        (a M N).hom ≫ U.map (tensorHom (E₀.map f) g))
    (P : CochainComplex A ℤ) (Q : CochainComplex B ℤ) :
    let EC := E₀.mapHomologicalComplex (.up ℤ)
    let UC := U.mapHomologicalComplex (.up ℤ)
    let TR := (curriedTensor A).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)
    let TS := (curriedTensor B).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)
    (TR.obj P).obj (UC.obj Q) ≅ UC.obj ((TS.obj (EC.obj P)).obj Q) := by
  exact HomologicalComplex₂.total.mapIso
    (tensorCancellationBicomplexIso E₀ U a ha P Q) (.up ℤ) ≪≫
    HomologicalComplex₂.mapTotalIso U
      ((((curriedTensor B).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
        ((E₀.mapHomologicalComplex (.up ℤ)).obj P)).obj Q) (.up ℤ)

private theorem tensorCancellationComplexIso_naturality
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    [MonoidalCategory A] [MonoidalCategory B]
    [MonoidalPreadditive A] [MonoidalPreadditive B]
    [HasColimitsOfSize.{0, 0} A] [HasColimitsOfSize.{0, 0} B]
    (E₀ : A ⥤ B) [E₀.Additive] (U : B ⥤ A) [U.Additive]
    [PreservesColimitsOfSize.{0, 0} U] (a : ∀ (M : A) (N : B), M ⊗ U.obj N ≅ U.obj (E₀.obj M ⊗ N))
    (ha : ∀ {M M' : A} {N N' : B} (f : M ⟶ M') (g : N ⟶ N'),
      tensorHom f (U.map g) ≫ (a M' N').hom =
        (a M N).hom ≫ U.map (tensorHom (E₀.map f) g))
    {P P' : CochainComplex A ℤ} {Q Q' : CochainComplex B ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    HomologicalComplex.mapBifunctorMap f
        ((U.mapHomologicalComplex (.up ℤ)).map g) (curriedTensor A) (.up ℤ) ≫
      (tensorCancellationComplexIso E₀ U a ha P' Q').hom =
    (tensorCancellationComplexIso E₀ U a ha P Q).hom ≫
      (U.mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.mapBifunctorMap
          ((E₀.mapHomologicalComplex (.up ℤ)).map f) g (curriedTensor B) (.up ℤ)) := by
  let TR := (curriedTensor A).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)
  let TS := (curriedTensor B).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)
  let UC := U.mapHomologicalComplex (.up ℤ)
  let EC := E₀.mapHomologicalComplex (.up ℤ)
  let UU := U.mapHomologicalComplex₂ (.up ℤ) (.up ℤ)
  let bd := tensorCancellationBicomplexIso E₀ U a ha
  let dr := (TR.map f).app (UC.obj Q) ≫ (TR.obj P').map (UC.map g)
  let ds := (TS.map (EC.map f)).app Q ≫ (TS.obj (EC.obj P')).map g
  have hn : dr ≫ (bd P' Q').hom = (bd P Q).hom ≫ UU.map ds := by
    ext i j : 2
    change (((f.f i) ▷ U.obj (Q.X j)) ≫ (P'.X i) ◁ U.map (g.f j)) ≫
        (a (P'.X i) (Q'.X j)).hom =
      (a (P.X i) (Q.X j)).hom ≫
        U.map ((E₀.map (f.f i)) ▷ (Q.X j) ≫ E₀.obj (P'.X i) ◁ g.f j)
    simpa only [tensorHom_def] using ha (f.f i) (g.f j)
  change HomologicalComplex₂.total.map dr (.up ℤ) ≫
      HomologicalComplex₂.total.map (bd P' Q').hom (.up ℤ) ≫ _ =
    (HomologicalComplex₂.total.map (bd P Q).hom (.up ℤ) ≫ _) ≫ _
  rw [← HomologicalComplex₂.total.map_comp_assoc, hn,
    HomologicalComplex₂.total.map_comp, Category.assoc]
  have ht := HomologicalComplex₂.mapTotalIso_hom_naturality U ds (.up ℤ)
  set_option backward.isDefEq.respectTransparency false in
    simpa only [HomologicalComplex.mapBifunctorMap, Category.assoc] using
      congrArg (fun t ↦ HomologicalComplex₂.total.map (bd P Q).hom (.up ℤ) ≫ t) ht

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorCancellationComplexIso_ι_inv
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    [MonoidalCategory A] [MonoidalCategory B]
    [MonoidalPreadditive A] [MonoidalPreadditive B]
    [HasColimitsOfSize.{0, 0} A] [HasColimitsOfSize.{0, 0} B]
    (E₀ : A ⥤ B) [E₀.Additive] (U : B ⥤ A) [U.Additive]
    [PreservesColimitsOfSize.{0, 0} U] (a : ∀ (M : A) (N : B), M ⊗ U.obj N ≅ U.obj (E₀.obj M ⊗ N))
    (ha : ∀ {M M' : A} {N N' : B} (f : M ⟶ M') (g : N ⟶ N'),
      tensorHom f (U.map g) ≫ (a M' N').hom =
        (a M N).hom ≫ U.map (tensorHom (E₀.map f) g))
    (P : CochainComplex A ℤ) (Q : CochainComplex B ℤ) (i j : ℤ) :
    let EC := E₀.mapHomologicalComplex (.up ℤ)
    let UC := U.mapHomologicalComplex (.up ℤ)
    let TR := (curriedTensor A).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)
    let TS := (curriedTensor B).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)
    U.map (((TS.obj (EC.obj P)).obj Q).ιTotal (.up ℤ) i j (i+j) rfl) ≫
        (tensorCancellationComplexIso E₀ U a ha P Q).inv.f (i+j) =
      (a (P.X i) (Q.X j)).inv ≫
        ((TR.obj P).obj (UC.obj Q)).ιTotal (.up ℤ) i j (i+j) rfl := by
  dsimp only
  let TR := (curriedTensor A).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)
  let TS := (curriedTensor B).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)
  let UC := U.mapHomologicalComplex (.up ℤ)
  let EC := E₀.mapHomologicalComplex (.up ℤ)
  let DS := (TS.obj (EC.obj P)).obj Q
  let bd := tensorCancellationBicomplexIso E₀ U a ha P Q
  change U.map (DS.ιTotal (.up ℤ) i j (i+j) rfl) ≫
      (HomologicalComplex₂.mapTotalXIso U DS (.up ℤ) (i+j)).inv ≫
        (HomologicalComplex₂.total.map bd.inv (.up ℤ)).f (i+j) = _
  rw [HomologicalComplex₂.map_ι_mapTotalXIso_inv_assoc]
  exact HomologicalComplex₂.ιTotal_map
    (K := (U.mapHomologicalComplex₂ (.up ℤ) (.up ℤ)).obj DS)
    (L := (TR.obj P).obj (UC.obj Q)) (φ := bd.inv) (c₁₂ := (.up ℤ))
    (i₁ := i) (i₂ := j) (i₁₂ := i+j) (h := rfl)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorComplexCancellation
    (φ : R ⟶ S) (E₀ : 𝓜 R ⥤ 𝓜 S) [E₀.Additive]
    (hobj : ∀ M, E₀.obj M = SheafOfModules.changeOfRings φ M)
    (hmap : ∀ {M M' : 𝓜 R} (f : M ⟶ M'),
      E₀.map f = eqToHom (hobj M) ≫ SheafOfModules.changeOfRingsHom φ M f ≫
        eqToHom (hobj M').symm)
    [(siteTensorRestriction φ).Additive] :
    let U : 𝓜 S ⥤ 𝓜 R := siteTensorRestriction φ
    let UC := U.mapHomologicalComplex (.up ℤ)
    let EC := E₀.mapHomologicalComplex (.up ℤ)
    ∃ b : ∀ (P : CochainComplex (𝓜 R) ℤ) (Q : CochainComplex (𝓜 S) ℤ),
      ((SiteTensorComplexFunctor R).obj P).obj (UC.obj Q) ≅
        UC.obj (((SiteTensorComplexFunctor S).obj (EC.obj P)).obj Q),
      (∀ {P P' : CochainComplex (𝓜 R) ℤ} {Q Q' : CochainComplex (𝓜 S) ℤ}
        (f : P ⟶ P') (g : Q ⟶ Q'),
        (((SiteTensorComplexFunctor R).map f).app (UC.obj Q) ≫
          ((SiteTensorComplexFunctor R).obj P').map (UC.map g)) ≫ (b P' Q').hom =
        (b P Q).hom ≫ UC.map
          (((SiteTensorComplexFunctor S).map (EC.map f)).app Q ≫
            ((SiteTensorComplexFunctor S).obj (EC.obj P')).map g)) ∧
      (∀ (P : CochainComplex (𝓜 R) ℤ) (Q : CochainComplex (𝓜 S) ℤ)
        (i j : ℤ) (V : Cᵒᵖ) (x : (P.X i).val.obj V)
        (s : S.obj.obj V) (n : (Q.X j).val.obj V),
        ((b P Q).inv.f (i + j)).val.app V
          (siteTotalTmul (EC.obj P) Q i j V
            (siteExtensionTmul φ (P.X i) E₀ hobj V x s) n) =
        siteTotalTmul P (UC.obj Q) i j V x (s • n)) := by
  dsimp only
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  let := SheafOfModules.cochainModulesPreadditive R
  let := SheafOfModules.cochainModulesPreadditive S
  let U : 𝓜 S ⥤ 𝓜 R := siteTensorRestriction φ
  let UC := U.mapHomologicalComplex (.up ℤ)
  let EC := E₀.mapHomologicalComplex (.up ℤ)
  have : PreservesColimitsOfSize.{0, 0} U := restrictionColimits φ
  let TR := (curriedTensor (𝓜 R)).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)
  let TS := (curriedTensor (𝓜 S)).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)
  let UU := U.mapHomologicalComplex₂ (.up ℤ) (.up ℤ)
  obtain ⟨a, ha, hasec⟩ := ordinaryTensorCancellation φ E₀ hobj hmap
  let b := tensorCancellationComplexIso E₀ U a ha
  refine ⟨b, ?_, ?_⟩
  · intro P P' Q Q' f g
    rw [tensorTotal_map R f (UC.map g), tensorTotal_map S (EC.map f) g]
    exact tensorCancellationComplexIso_naturality E₀ U a ha f g
  · intro P Q i j V x s n
    let DR := (TR.obj P).obj (UC.obj Q)
    let DS := (TS.obj (EC.obj P)).obj Q
    have hi := tensorCancellationComplexIso_ι_inv E₀ U a ha P Q i j
    have hh := congrArg (fun f ↦ f.val.app V
      (siteMonoidalTmul (E₀.obj (P.X i)) (Q.X j) V
        (siteExtensionTmul φ (P.X i) E₀ hobj V x s) n)) hi
    change ((b P Q).inv.f (i+j)).val.app V
        (siteTotalTmul (EC.obj P) Q i j V
          (siteExtensionTmul φ (P.X i) E₀ hobj V x s) n) =
      (DR.ιTotal (.up ℤ) i j (i+j) rfl).val.app V
        ((a (P.X i) (Q.X j)).inv.val.app V
          (siteMonoidalTmul (E₀.obj (P.X i)) (Q.X j) V
            (siteExtensionTmul φ (P.X i) E₀ hobj V x s) n)) at hh
    have hs := hasec (P.X i) (Q.X j) V x s n
    have hs' := congrArg
      (fun z ↦ (DR.ιTotal (.up ℤ) i j (i+j) rfl).val.app V z) hs
    exact hh.trans hs'

private theorem tensorFlat_changeOfRings
    (φ : R ⟶ S) (E₀ : 𝓜 R ⥤ 𝓜 S) [E₀.Additive]
    (hobj : ∀ M, E₀.obj M = SheafOfModules.changeOfRings φ M)
    (hmap : ∀ {M N : 𝓜 R} (f : M ⟶ N),
      E₀.map f = eqToHom (hobj M) ≫ SheafOfModules.changeOfRingsHom φ M f ≫
        eqToHom (hobj N).symm)
    (P : CochainComplex (𝓜 R) ℤ) (hP : TensorFlatRepresentative (J := J) (R := R) P) :
    TensorFlatRepresentative (J := J) (R := S)
      ((E₀.mapHomologicalComplex (.up ℤ)).obj P) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  have hflat (i : ℤ) : exactFunctor _ _ (tensorRight (P.X i)) :=
    (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R (P.X i)) (hP.2 i)
  obtain ⟨hK, hf⟩ :=
    SheafOfModules.changeOfRings_isKFlat_of_flat_terms_independentCoefficients
      φ P E₀ hobj hmap hP.1 hflat
  exact ⟨hK, fun i ↦ (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso S
      (((E₀.mapHomologicalComplex (.up ℤ)).obj P).X i)).symm (hf i)⟩

end TensorProof

attribute [local instance] siteSectionModule

set_option backward.isDefEq.respectTransparency.types false in
/-- Derived tensor commutes with restriction after extension of scalars, with the
specified balanced chain representative and the canonical computation comparisons.

Source: blueprint Step 2; Stacks, Tags 03EK, 06YS, 06YU, 06YY
(blueprint: lem-trf-site-derived-tensor-restriction).

Proof plan:
1. Restriction changes only actions. Kernels, cokernels and sums have the same underlying
abelian sheaves, so it is exact and descends through quasi-isomorphisms.
2. Sheafify the balanced inverse maps `x ⊗ n ↦ (x ⊗ 1) ⊗ n` and
`(x ⊗ s) ⊗ n ↦ x ⊗ s n`. The tensor and module-sheafification universal properties
prove well-definedness and both inverse identities on local tensor generators.
3. Apply these maps degreewise to a K-flat flat-term complex and degree-zero `N`.
Naturality in the differential gives the chain isomorphism, natural in both variables.
4. Change of rings preserves K-flatness and flat terms. Its derived universal counit
computes the extension on such a representative (lem-pur-derived-change-of-rings).
5. Tensoring with a K-flat complex preserves quasi-isomorphisms, by the acyclic-cone
criterion and the tensor/cone comparison. Symmetry gives the other tensor order.
6. Resolve the unresolved second factor. Extend the two-sided descent comparison uniquely
along its localization; its naturality and normalization give `cR` and `cS` below.
7. Localize the natural balanced chain isomorphism in the first factor, with values in
functors of degree-zero sheaves. The localization universal property gives `e` and its
naturality. The equation below identifies its component on every K-flat representative
using exactly `cR`, the derived-change-of-rings counit, `cS` and restriction's factorization.
Naturality along an arbitrary representing isomorphism gives the formula for `P → H`;
uniqueness of descent gives independence of that representative. No flatness of the
coefficient map, boundedness or finite Tor amplitude is used.
-/
theorem siteDerivedTensorRestriction
    [HasDerivedCategory.{w} (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))] [HasDerivedCategory.{w}
          (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S))]
    (φ : R ⟶ S)
    (E₀ : (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ⥤ (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S))) [E₀.Additive]
    (hobj : ∀ M, E₀.obj M = SheafOfModules.changeOfRings φ M)
    (hmap : ∀ {M N : (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))} (f : M ⟶ N),
      E₀.map f = eqToHom (hobj M) ≫ SheafOfModules.changeOfRingsHom φ M f ≫
        eqToHom (hobj N).symm)
    (E : DerivedCategory (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ⥤ DerivedCategory
          (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S)))
    (ε : DerivedCategory.Qh ⋙ E ⟶ E₀.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
    (hE : E.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (ComplexShape.up ℤ)))
    (hε : ∀ P : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
        IsIso (ε.app ((HomotopyCategory.quotient _ _).obj P)))
    [(siteTensorRestriction φ).Additive]
    [PreservesFiniteLimits (siteTensorRestriction φ)]
    [PreservesFiniteColimits (siteTensorRestriction φ)] :
    ∃ (cR : OneSidedTensorComparison (R := R)) (cS : OneSidedTensorComparison (R := S)),
      CanonicalOneSidedTensorComparison cR ∧ CanonicalOneSidedTensorComparison cS ∧
      ∃ e : ∀ (H : DerivedCategory (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))) (N : (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S))),
        ((siteRestrictionDerivedTensor (R := R)).obj H).obj
          ((siteTensorRestriction φ).mapDerivedCategory.obj
            (DerivedCategory.Q.obj (siteTensorSingle N))) ≅
        (siteTensorRestriction φ).mapDerivedCategory.obj
          (((siteRestrictionDerivedTensor (R := S)).obj (E.obj H)).obj
            (DerivedCategory.Q.obj (siteTensorSingle N))),
        ProjectionFormulaFamily (siteRestrictionDerivedTensor (R := R))
          (siteRestrictionDerivedTensor (R := S)) E
          (siteTensorRestriction φ).mapDerivedCategory e ∧
        ∀ (P : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
          (hP : TensorFlatRepresentative P) (N : (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S))),
        ∃ hEP : TensorFlatRepresentative
            ((E₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj P),
        ∃ b :
          ((SiteTensorComplexFunctor R).obj P).obj
            (((siteTensorRestriction φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              (siteTensorSingle N)) ≅
          ((siteTensorRestriction φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((SiteTensorComplexFunctor S).obj
              ((E₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)).obj (siteTensorSingle N)),
          (∀ (i : ℤ) (U : Cᵒᵖ) (x : (P.X i).val.obj U) (n : N.val.obj U),
            (b.hom.f (i + 0)).val.app U
              (siteTotalTmul P
                (((siteTensorRestriction φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                  (siteTensorSingle N)) i 0 U x
                (((siteTensorRestriction φ).map
                  (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 N).inv).val.app U n)) =
            siteTotalTmul ((E₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
              (siteTensorSingle N) i 0 U
              (siteExtensionTmul φ (P.X i) E₀ hobj U x 1)
              ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 N).inv.val.app U n)) ∧
          (∀ (i : ℤ) (U : Cᵒᵖ) (x : (P.X i).val.obj U)
            (s : S.obj.obj U) (n : N.val.obj U),
            (b.inv.f (i + 0)).val.app U
              (siteTotalTmul ((E₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
                (siteTensorSingle N) i 0 U
                (siteExtensionTmul φ (P.X i) E₀ hobj U x s)
                ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 N).inv.val.app U n)) =
            siteTotalTmul P
              (((siteTensorRestriction φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                (siteTensorSingle N)) i 0 U x
              (((siteTensorRestriction φ).map
                (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 N).inv).val.app U
                  (s • n))) ∧
          (e (DerivedCategory.Q.obj P) N).hom =
            ((siteRestrictionDerivedTensor (R := R)).obj (DerivedCategory.Q.obj P)).map
              ((siteTensorRestriction φ).mapDerivedCategoryFactors.hom.app (siteTensorSingle N)) ≫
            (cR P hP _).hom ≫ DerivedCategory.Q.map b.hom ≫
            (siteTensorRestriction φ).mapDerivedCategoryFactors.inv.app _ ≫
            (siteTensorRestriction φ).mapDerivedCategory.map
              ((cS _ hEP (siteTensorSingle N)).inv) ≫
            (siteTensorRestriction φ).mapDerivedCategory.map
              (((siteRestrictionDerivedTensor (R := S)).map
                (siteExtensionComparison E₀ E ε P (hε P hP.1)).inv).app
                  (DerivedCategory.Q.obj (siteTensorSingle N))) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  have _ := hE
  let PC := flatComplexProperty (R := R)
  let U : 𝓜 S ⥤ 𝓜 R := siteTensorRestriction φ
  let UC := U.mapHomologicalComplex (.up ℤ)
  let UD := U.mapDerivedCategory
  let EC := E₀.mapHomologicalComplex (.up ℤ)
  let QR := DerivedCategory.Q (C := 𝓜 R)
  let QS := DerivedCategory.Q (C := 𝓜 S)
  let TR := SheafOfModules.siteDerivedTensorIndependentCoefficients.{u, v, r, w} J R
  let TS := SheafOfModules.siteDerivedTensorIndependentCoefficients.{u, v, r, w} J S
  let Z := HomologicalComplex.single (𝓜 S) (.up ℤ) 0
  let TCR := Functor.uncurry.obj (SiteTensorComplexFunctor R)
  let TCS := Functor.uncurry.obj (SiteTensorComplexFunctor S)
  let dR := tensorOneSidedComparison (J := J) (R := R)
  let cR := dR.choose
  have hcR := dR.choose_spec.1
  have hnR := dR.choose_spec.2
  let dS := tensorOneSidedComparison (J := J) (R := S)
  let cS := dS.choose
  have hcS := dS.choose_spec.1
  have hnS := dS.choose_spec.2
  let db := tensorComplexCancellation φ E₀ hobj hmap
  let b := db.choose
  have hbspec := Exists.choose_spec db
  rcases hbspec with ⟨hb, hbsec⟩
  have hEP (P : PC.FullSubcategory) :
      TensorFlatRepresentative (J := J) (R := S) (EC.obj P.obj) :=
    tensorFlat_changeOfRings (J := J) (R := R) (S := S) φ E₀ hobj hmap P.obj P.property
  let cRi := tensorComparisonBifunctorIso (J := J) (R := R)
    PC.ι (fun P ↦ P.property) (Z ⋙ UC) cR hcR hnR
  let cSi := tensorComparisonBifunctorIso (J := J) (R := S)
    (PC.ι ⋙ EC) hEP Z cS hcS hnS
  let bi : (PC.ι.prod (Z ⋙ UC)) ⋙ TCR ≅
      ((PC.ι ⋙ EC).prod Z) ⋙ TCS ⋙ UC :=
    NatIso.ofComponents (fun X ↦ b X.1.obj (Z.obj X.2)) (by
      intro X Y f
      exact hb f.1.hom (Z.map f.2))
  let HR := HomotopyCategory.quotient (𝓜 R) (.up ℤ)
  let QhR := DerivedCategory.Qh (C := 𝓜 R)
  let QhS := DerivedCategory.Qh (C := 𝓜 S)
  have heps (P : PC.FullSubcategory) : IsIso ((Functor.whiskerLeft (PC.ι ⋙ HR) ε).app P) :=
    hε P.obj P.property.1
  have : IsIso (Functor.whiskerLeft (PC.ι ⋙ HR) ε) := NatIso.isIso_of_isIso_app _
  let ex₀ : PC.ι ⋙ QR ⋙ E ≅ PC.ι ⋙ EC ⋙ QS :=
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft PC.ι (DerivedCategory.quotientCompQhIso (𝓜 R)).symm) E ≪≫
    asIso (Functor.whiskerLeft (PC.ι ⋙ HR) ε) ≪≫
    Functor.isoWhiskerLeft PC.ι
      (Functor.isoWhiskerRight (E₀.mapHomotopyCategoryFactors (.up ℤ)) QhS) ≪≫
    Functor.isoWhiskerLeft (PC.ι ⋙ EC) (DerivedCategory.quotientCompQhIso (𝓜 S))
  have hex (P : PC.FullSubcategory) :
      ex₀.app P = siteExtensionComparison E₀ E ε P.obj (hε P.obj P.property.1) := by
    apply Iso.ext
    rfl
  let ex : PC.ι ⋙ QR ⋙ E ≅ PC.ι ⋙ EC ⋙ QS :=
    NatIso.ofComponents
      (fun P ↦ siteExtensionComparison E₀ E ε P.obj (hε P.obj P.property.1)) (by
        intro P Q f
        have h := ex₀.hom.naturality f
        change _ ≫ (ex₀.app Q).hom = (ex₀.app P).hom ≫ _ at h
        rw [hex, hex] at h
        exact h)
  let F : DerivedCategory (𝓜 R) × 𝓜 S ⥤ DerivedCategory (𝓜 R) :=
    ((𝟭 _).prod (Z ⋙ QS ⋙ UD)) ⋙ TR
  let G : DerivedCategory (𝓜 R) × 𝓜 S ⥤ DerivedCategory (𝓜 R) :=
    (E.prod (Z ⋙ QS)) ⋙ TS ⋙ UD
  let q := (PC.ι ⋙ QR).prod (𝟭 (𝓜 S))
  let a₁ := Functor.isoWhiskerRight
    (NatIso.prod (Iso.refl (PC.ι ⋙ QR))
      (Functor.isoWhiskerLeft Z U.mapDerivedCategoryFactors)) TR
  let a₃ := Functor.isoWhiskerRight bi QR
  let a₄ := Functor.isoWhiskerLeft (((PC.ι ⋙ EC).prod Z) ⋙ TCS)
    U.mapDerivedCategoryFactors.symm
  let a₅ := Functor.isoWhiskerRight cSi.symm UD
  let a₆ := Functor.isoWhiskerRight
    (Functor.isoWhiskerRight (NatIso.prod ex.symm (Iso.refl (Z ⋙ QS))) TS) UD
  let raw : q ⋙ F ≅ q ⋙ G := a₁ ≪≫ cRi ≪≫ a₃ ≪≫ a₄ ≪≫ a₅ ≪≫ a₆
  let ff := tensorFlatWhiskering (R := R) (𝓜 S) (DerivedCategory (𝓜 R))
  obtain ⟨ei, hei⟩ := descendTensorComparison q ff F G raw
  let e := fun H N ↦ ei.app (H, N)
  refine ⟨cR, cS, hcR, hcS, e, ?_, ?_⟩
  · exact tensorComparison_naturality TR TS E UD (Z ⋙ QS) ei
  · intro P hP N
    refine ⟨hEP ⟨P, hP⟩, b P (Z.obj N), ?_, ?_, ?_⟩
    · intro i V x n
      let t := (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv.val.app V n
      have hh := hbsec P (Z.obj N) i 0 V x 1 t
      have hh' := congrArg (fun y ↦ ((b P (Z.obj N)).hom.f (i+0)).val.app V y) hh
      let y := siteTotalTmul (EC.obj P) (Z.obj N) i 0 V
        (siteExtensionTmul φ (P.X i) E₀ hobj V x 1) t
      have hbi : ((b P (Z.obj N)).hom.f (i+0)).val.app V
          (((b P (Z.obj N)).inv.f (i+0)).val.app V y) = y := by
        change (((b P (Z.obj N)).inv ≫ (b P (Z.obj N)).hom).f (i+0)).val.app V y = y
        rw [(b P (Z.obj N)).inv_hom_id]
        rfl
      rw [hbi] at hh'
      change ((b P (Z.obj N)).hom.f (i+0)).val.app V
          (siteTotalTmul P (UC.obj (Z.obj N)) i 0 V x t) = y
      simpa only [y, t, one_smul] using hh'.symm
    · intro i V x s n
      have hh := hbsec P (Z.obj N) i 0 V x s
        ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv.val.app V n)
      change _ = siteTotalTmul P (UC.obj (Z.obj N)) i 0 V x
        ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv.val.app V (s • n))
      simpa only [map_smul] using hh
    · have h := hei (⟨P, hP⟩, N)
      change (e (QR.obj P) N).hom = raw.hom.app (⟨P, hP⟩, N) at h
      rw [h]
      rfl

end CategoryTheory
