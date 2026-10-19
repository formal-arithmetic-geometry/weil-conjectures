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
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
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

universe u v r w a b va vb wa wb

open CategoryTheory CategoryTheory.Limits
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
  (SheafOfModules.site_derived_tensor_descent_independentCoefficients.{u, v, r, w, 0, 0}
      J R).choose_spec.2.2.1
    |>.choose_spec.1.some

/-- Its specified comparison with the recorded derived tensor on the resolving class.
Source: Stacks, Tag 06YU (blueprint: lem-trf-site-derived-tensor-restriction). -/
def tensorDescentDerivedIso [HasDerivedCategory.{w} (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))] :=
  (SheafOfModules.site_derived_tensor_descent_independentCoefficients.{u, v, r, w, 0, 0}
      J R).choose_spec.2.2.1
    |>.choose_spec.2.choose_spec.some

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
  sorry

end CategoryTheory
