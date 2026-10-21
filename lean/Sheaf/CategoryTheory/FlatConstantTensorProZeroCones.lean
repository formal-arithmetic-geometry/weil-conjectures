/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.BifunctorShift
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import Sheaf.AlgebraicGeometry.DerivedChangeOfRingsModel
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.FromJoel.Algebra.Homology.HomologicalComplexFunctorEquiv
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import Mathlib.RingTheory.Noetherian.Defs
import Sheaf.CategoryTheory.FiniteTypeConstantExact
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-! # Flat constant extension and tensor of pro-zero cone towers

Source: Stacks Project, proetale.tex, Tag 099M, transport of the Koszul pro-isomorphism;
sites-cohomology.tex, Tags 06YN and 0941.
(blueprint: lem-weil-pbc-flat-constant-tensor-pro-zero-cones).

## Main declarations

- `flatConstantTensorFunctor`: termwise flat constant extension and total tensor.
- `flatConstantUnitLimitMap`: the specified strict coaugmentation map to Rlim.
- `flatConstantTensorProZeroCones`: pro-zero transport and unit compatibility.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u v wA wO a b d
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped ChangeOfRings
attribute [local instance] Functor.preservesZeroMorphisms_of_additive

namespace CategoryTheory

/-- The existing equivalence writes a strict tower of complexes as a complex of towers.
Source: Stacks 0941 (blueprint: lem-weil-pbc-flat-constant-tensor-pro-zero-cones). -/
abbrev flatConstantTowerComplex {B : Type a} [Category.{b} B] [HasZeroMorphisms B] :=
  (HomologicalComplex.functorEquivalence B (.up ℤ) ℕᵒᵖ).inverse

/-- The canonical map from a strict cone to the total derived inverse limit. It is the
ordinary constant/limit adjunction unit, followed by the strict cone and the derived
comparison η. On a K-injective replacement j it is Q(lim(jα)), as in Stacks 0941.
Source: Stacks 0940--0941
(blueprint: lem-weil-pbc-flat-constant-tensor-pro-zero-cones). -/
def flatConstantStrictConeMap {B : Type a} [Category.{b} B] [Abelian B]
    [HasLimitsOfShape ℕᵒᵖ B] [HasDerivedCategory.{d} B]
    [HasDerivedCategory.{d} (ℕᵒᵖ ⥤ B)]
    (RF : DerivedCategory (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory B)
    (η : (lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (U : CochainComplex B ℤ) (Z : ℕᵒᵖ ⥤ CochainComplex B ℤ)
    (α : (Functor.const ℕᵒᵖ).obj U ⟶ Z) :
    DerivedCategory.Q.obj U ⟶ RF.obj (DerivedCategory.Q.obj (flatConstantTowerComplex.obj Z)) :=
  DerivedCategory.Q.map
    ((NatTrans.mapHomologicalComplex (constLimAdj (J := ℕᵒᵖ) (C := B)).unit (.up ℤ)).app U ≫
      ((lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (.up ℤ)).map
        (flatConstantTowerComplex.map α)) ≫ η.app (flatConstantTowerComplex.obj Z)

/-- The pointed version of the canonical strict-cone comparison, for any strict functor.
The map is the localization of the chosen strict point followed by the constant/limit
adjunction and the derived comparison, with no choice of a derived-category map.
Source: Stacks 0941 (blueprint: lem-weil-pbc-flat-constant-tensor-pro-zero-cones). -/
def flatConstantPointedLimitMap
    {T : Type u} [Category.{v} T] {B : Type a} [Category.{b} B] [Abelian B]
    [HasLimitsOfShape ℕᵒᵖ B] [HasDerivedCategory.{d} B]
    [HasDerivedCategory.{d} (ℕᵒᵖ ⥤ B)]
    (RF : DerivedCategory (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory B)
    (η : (lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (F : T ⥤ CochainComplex B ℤ) (U : T) (P : CochainComplex B ℤ)
    (ι : P ⟶ F.obj U) (X : ℕᵒᵖ ⥤ T) (α : (Functor.const ℕᵒᵖ).obj U ⟶ X) :
    DerivedCategory.Q.obj P ⟶ RF.obj (DerivedCategory.Q.obj
      (flatConstantTowerComplex.obj (X ⋙ F))) :=
  DerivedCategory.Q.map ι ≫
    flatConstantStrictConeMap RF η (F.obj U) (X ⋙ F)
      ((Functor.constComp ℕᵒᵖ U F).inv ≫ Functor.whiskerRight α F)

/-- A strict cone tower is pro-zero after localization exactly when each level is hit
by a transition that is zero in the derived category. The cone is formed in the
abelian category of towers, retaining all strict transition maps.
Source: Stacks 014E--014F and 0941
(blueprint: lem-weil-pbc-flat-constant-tensor-pro-zero-cones). -/
def FlatConstantConeProZero {B : Type a} [Category.{b} B] [Abelian B]
    [HasDerivedCategory.{d} B] {X Y : ℕᵒᵖ ⥤ CochainComplex B ℤ} (v : X ⟶ Y) : Prop :=
  ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m),
    DerivedCategory.Q.map
      ((CochainComplex.mappingCone (flatConstantTowerComplex.map v)).asFunctor.map
        (homOfLE h).op) = 0

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{max u v} C]
  (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- Reuse the existing coefficient-forgetful sheaf-composition instance.
Source: Stacks 03CY (blueprint: lem-weil-pbc-flat-constant-tensor-pro-zero-cones). -/
instance flatConstantHasSheafCompose :
    J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v}) :=
  inferInstance

attribute [-instance] flatConstantHasSheafCompose
attribute [local instance] flatConstantHasSheafCompose

variable (A : Type (max u v)) [CommRing A]
  {O : Sheaf J CommRingCat.{max u v}} (φ : realizationRing J A ⟶ O)

/-- Reuse the existing abelian structure of the module-sheaf category.
Source: Stacks 03DA (blueprint: lem-weil-pbc-flat-constant-tensor-pro-zero-cones). -/
instance flatConstantModulesAbelian :
    Abelian (SheafOfModules.{max u v}
      (SheafOfModules.derivedChangeRingIndependentCoefficients.{max u v, u, v} J O)) :=
  inferInstance

attribute [-instance] flatConstantModulesAbelian
attribute [local instance] flatConstantModulesAbelian

/-- Reuse ordinary strict inverse limits in the module-sheaf category.
Source: Stacks 0940 (blueprint: lem-weil-pbc-flat-constant-tensor-pro-zero-cones). -/
instance flatConstantModulesLimits :
    HasLimitsOfShape ℕᵒᵖ (SheafOfModules.{max u v}
      (SheafOfModules.derivedChangeRingIndependentCoefficients.{max u v, u, v} J O)) :=
  inferInstance

attribute [-instance] flatConstantModulesLimits
attribute [local instance] flatConstantModulesLimits

variable
  [HasDerivedCategory.{wO} (SheafOfModules.{max u v}
    (SheafOfModules.derivedChangeRingIndependentCoefficients.{max u v, u, v} J O))]

/-- Specialize the existing canonical scalar-extension model to the constant ring sheaf,
using the standard source localization. No source localization is additional input.
Source: Stacks 06YY (blueprint: lem-weil-pbc-flat-constant-tensor-pro-zero-cones). -/
noncomputable instance flatConstantSourceHasDerivedCategory :
    HasDerivedCategory
      (SheafOfModules (SheafOfModules.derivedChangeRingIndependentCoefficients J
        (realizationRing J A))) :=
  HasDerivedCategory.standard (realizationModules J A)

/-- The recorded canonical extension model, at the standard source localization.
Source: Stacks 06YY (blueprint: lem-weil-pbc-flat-constant-tensor-pro-zero-cones). -/
noncomputable def flatConstantExtensionModel
    (φ : realizationRing J A ⟶ O) :
    SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, max u v,
      (max u v) + 1, wO} φ :=
  SheafOfModules.canonicalDerivedChangeOfRingsModel.{u, v, max u v, (max u v) + 1, wO} φ

/-- Ordinary E(M) = O ⊗_R underline M, with its prescribed O-action. The existing
canonical model fixes objects and maps to sheafified scalar tensor by obj_eq and map_eq.
Source: Stacks 03EK and 099M
(blueprint: lem-weil-pbc-flat-constant-tensor-pro-zero-cones). -/
abbrev flatConstantExtension
    (φ : realizationRing J A ⟶ O) :
    ModuleCat.{max u v} A ⥤ SheafOfModules.{max u v}
      (SheafOfModules.derivedChangeRingIndependentCoefficients.{max u v, u, v} J O) :=
  commutativeSiteConstantModuleFunctor J A ⋙ (flatConstantExtensionModel J A φ).E

/-- Reuse the existing monoidal structure on total cochain tensor.
Source: Stacks 06YN (blueprint: lem-weil-pbc-flat-constant-tensor-pro-zero-cones). -/
instance flatConstantCochainMonoidal :
    MonoidalCategory (CochainComplex (SheafOfModules.{max u v}
      (SheafOfModules.derivedChangeRingIndependentCoefficients.{max u v, u, v} J O)) ℤ) :=
  inferInstance

attribute [-instance] flatConstantCochainMonoidal
attribute [local instance] flatConstantCochainMonoidal

/-- Use the same cochain tensor data for whiskering and the unitors.
Source: Stacks 06YN (blueprint: lem-weil-pbc-flat-constant-tensor-pro-zero-cones). -/
instance flatConstantCochainMonoidalStruct :
    MonoidalCategoryStruct (CochainComplex (SheafOfModules.{max u v}
      (SheafOfModules.derivedChangeRingIndependentCoefficients.{max u v, u, v} J O)) ℤ) :=
  (flatConstantCochainMonoidal (J := J) (O := O)).toMonoidalCategoryStruct

attribute [-instance] flatConstantCochainMonoidalStruct
attribute [local instance] flatConstantCochainMonoidalStruct

/-- Reuse the existing additivity witness for ordinary constant extension.
Source: Stacks 03EK (blueprint: lem-weil-pbc-flat-constant-tensor-pro-zero-cones). -/
instance flatConstantExtensionAdditive (φ : realizationRing J A ⟶ O) :
    (flatConstantExtension J A φ).Additive :=
  inferInstance

attribute [-instance] flatConstantExtensionAdditive
attribute [local instance] flatConstantExtensionAdditive

/-- Termwise constant extension followed by the direct-sum total tensor with P.
Source: Stacks 06YN and 099M
(blueprint: lem-weil-pbc-flat-constant-tensor-pro-zero-cones). -/
def flatConstantTensorFunctor
    (φ : realizationRing J A ⟶ O)
    (P : CochainComplex (SheafOfModules.{max u v}
      (SheafOfModules.derivedChangeRingIndependentCoefficients.{max u v, u, v} J O)) ℤ) :
    CochainComplex (ModuleCat.{max u v} A) ℤ ⥤
      CochainComplex (SheafOfModules.{max u v}
        (SheafOfModules.derivedChangeRingIndependentCoefficients.{max u v, u, v} J O)) ℤ :=
  (flatConstantExtension J A φ).mapHomologicalComplex (.up ℤ) ⋙ tensorLeft P

/-- The actual constant section of the constant module A.
Source: Stacks 03CY (blueprint: lem-weil-pbc-flat-constant-tensor-pro-zero-cones). -/
def flatConstantRegularSection (U : Cᵒᵖ) (x : A) :
    ((commutativeSiteConstantModuleFunctor J A).obj (ModuleCat.of A A)).val.obj U :=
  (toSheafify J ((siteConstantModulePresheafGeneral (C := C) A).obj
    (ModuleCat.of A A)).presheaf).app U x

/-- The normalization of the canonical coefficient-unit isomorphism: multiplication
s ⊗ underline a ↦ s φ(a). Thus the unit used below is determined on local pure tensors.
Source: Stacks 03EK (blueprint: lem-weil-pbc-flat-constant-tensor-pro-zero-cones). -/
def FlatConstantUnitNormalized
    (φ : realizationRing J A ⟶ O)
    (i : (flatConstantExtension J A φ).obj (ModuleCat.of A A) ≅
      SheafOfModules.unit
        (SheafOfModules.derivedChangeRingIndependentCoefficients.{max u v, u, v} J O)) : Prop :=
  ∀ (U : Cᵒᵖ) (s : O.obj.obj U) (x : A),
    ((eqToHom ((flatConstantExtensionModel J A φ).obj_eq
      ((commutativeSiteConstantModuleFunctor J A).obj (ModuleCat.of A A))).symm ≫ i.hom).val.app U)
        ((toSheafify J (SheafOfModules.changeOfRingsPresheaf φ
          ((commutativeSiteConstantModuleFunctor J A).obj (ModuleCat.of A A))).presheaf).app U
            (s ⊗ₜ[(realizationRing J A).obj.obj U, (φ.hom.app U).hom]
              flatConstantRegularSection J A U x)) =
      s * (φ.hom.app U) ((realizationRingUnit J A).app U x)

/-- P → P ⊗ E(A[0]) is the inverse ordinary tensor unitor and the inverse coefficient
multiplication isomorphism, extended as a degree-zero complex. This is a strict chain map.
Source: Stacks 03EK and 099M
(blueprint: lem-weil-pbc-flat-constant-tensor-pro-zero-cones). -/
def flatConstantTensorUnit
    (φ : realizationRing J A ⟶ O)
    (P : CochainComplex (SheafOfModules.{max u v}
      (SheafOfModules.derivedChangeRingIndependentCoefficients.{max u v, u, v} J O)) ℤ)
    (i : (flatConstantExtension J A φ).obj (ModuleCat.of A A) ≅
      SheafOfModules.unit
        (SheafOfModules.derivedChangeRingIndependentCoefficients.{max u v, u, v} J O)) :
    P ⟶ (flatConstantTensorFunctor J A φ P).obj
      ((HomologicalComplex.single (ModuleCat.{max u v} A) (.up ℤ) 0).obj
        (ModuleCat.of A A)) :=
  (ρ_ P).inv ≫ P ◁
    (((HomologicalComplex.singleMapHomologicalComplex
      (flatConstantExtension J A φ) (.up ℤ) 0).app (ModuleCat.of A A)) ≪≫
        (HomologicalComplex.single _ (.up ℤ) 0).mapIso i).inv

/-- Apply the tensor functor to a strict coaugmentation, including the canonical
comparison between the image of a constant tower and the constant image tower.
Source: Stacks 0941 (blueprint: lem-weil-pbc-flat-constant-tensor-pro-zero-cones). -/
def flatConstantTensorCoaugmentation
    (φ : realizationRing J A ⟶ O)
    (P : CochainComplex (SheafOfModules.{max u v}
      (SheafOfModules.derivedChangeRingIndependentCoefficients.{max u v, u, v} J O)) ℤ)
    {X : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{max u v} A) ℤ}
    (α : (Functor.const ℕᵒᵖ).obj
      ((HomologicalComplex.single (ModuleCat.{max u v} A) (.up ℤ) 0).obj
        (ModuleCat.of A A)) ⟶ X) :
    (Functor.const ℕᵒᵖ).obj ((flatConstantTensorFunctor J A φ P).obj
      ((HomologicalComplex.single (ModuleCat.{max u v} A) (.up ℤ) 0).obj
        (ModuleCat.of A A))) ⟶ X ⋙ flatConstantTensorFunctor J A φ P :=
  (Functor.constComp ℕᵒᵖ _ (flatConstantTensorFunctor J A φ P)).inv ≫
    Functor.whiskerRight α (flatConstantTensorFunctor J A φ P)

/-- The specified map from P to the total derived limit of a strictly coaugmented
constant-extension tensor tower. All comparisons in the composite are fixed above.
Source: Stacks 0941 and 099M
(blueprint: lem-weil-pbc-flat-constant-tensor-pro-zero-cones). -/
def flatConstantUnitLimitMap
    (φ : realizationRing J A ⟶ O)
    [HasDerivedCategory.{wO} (ℕᵒᵖ ⥤ SheafOfModules.{max u v}
      (SheafOfModules.derivedChangeRingIndependentCoefficients.{max u v, u, v} J O))]
    (RF : DerivedCategory (ℕᵒᵖ ⥤ SheafOfModules.{max u v}
          (SheafOfModules.derivedChangeRingIndependentCoefficients.{max u v, u, v} J O)) ⥤
        DerivedCategory (SheafOfModules.{max u v}
          (SheafOfModules.derivedChangeRingIndependentCoefficients.{max u v, u, v} J O)))
    (η : Functor.mapHomologicalComplex
          (lim : (ℕᵒᵖ ⥤ SheafOfModules.{max u v}
          (SheafOfModules.derivedChangeRingIndependentCoefficients.{max u v, u, v} J O)) ⥤
        SheafOfModules.{max u v}
          (SheafOfModules.derivedChangeRingIndependentCoefficients.{max u v, u, v} J O))
            (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (P : CochainComplex (SheafOfModules.{max u v}
      (SheafOfModules.derivedChangeRingIndependentCoefficients.{max u v, u, v} J O)) ℤ)
    (i : (flatConstantExtension J A φ).obj (ModuleCat.of A A) ≅
      SheafOfModules.unit
        (SheafOfModules.derivedChangeRingIndependentCoefficients.{max u v, u, v} J O))
    {X : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{max u v} A) ℤ}
    (α : (Functor.const ℕᵒᵖ).obj
      ((HomologicalComplex.single (ModuleCat.{max u v} A) (.up ℤ) 0).obj
        (ModuleCat.of A A)) ⟶ X) :
    DerivedCategory.Q.obj P ⟶ RF.obj (DerivedCategory.Q.obj
      (flatConstantTowerComplex.obj (X ⋙ flatConstantTensorFunctor J A φ P))) :=
  flatConstantPointedLimitMap RF η (flatConstantTensorFunctor J A φ P)
    ((HomologicalComplex.single (ModuleCat.{max u v} A) (.up ℤ) 0).obj
      (ModuleCat.of A A)) P (flatConstantTensorUnit J A φ P i) X α

/-- Flat constant extension and tensoring by an arbitrary K-flat complex preserve
pro-zero strict cone towers, their total derived limits, and the specified strict units.

Source: Stacks Project, proetale.tex, Tag 099M (lemma-naive-completion), transport
of its Koszul pro-isomorphism; sites-cohomology.tex, Tags 06YN and 0941.
(blueprint: lem-weil-pbc-flat-constant-tensor-pro-zero-cones).

The existing canonical scalar-extension model fixes ordinary objects and maps; its
source localization is standard and its derived functor is unused. RF and η range over
total right-derived pairs of the strict inverse-limit functor. The normalized i is
ordinary multiplication, so the maps from P below use the inverse tensor unitor and
the strict coaugmentations.

Proof:
1. Constant module sheafification is exact by
lem-weil-pbc-finite-type-constant-exact. Flatness makes tensor with O exact over R;
lem-weil-pbc-module-sheaves-colimits-forgetful reflects exactness in Mod(O). Thus E is exact.
2. lem-weil-pbc-exact-functor-derived-factorization gives its unbounded derived functor,
with the natural comparison with termwise E; it preserves zero maps.
3. By lem-pur-quasi-iso-cone-acyclic, a quasi-isomorphism has acyclic cone. K-flatness
makes its tensor with P acyclic. The signed symmetry p tensor c ↦ (-1)^(ij) c tensor p
and lem-pc-tensor-mapping-cone-iso identify this with the cone of left tensor by P.
The differential signs agree because (i+1)j = ij+j and i(j+1) = ij+i.
Thus left tensor by P preserves quasi-isomorphisms, even without flat terms in P.
4. lem-weil-pbc-localization-universal-property localizes this tensor functor and its
natural comparison; it preserves the zero object and zero maps.
5. The additive comparison E(Cone v) ≅ Cone(Ev) has the usual two-summand matrix;
it commutes with every strict square. Compose with the natural tensor-cone comparison
of lem-pc-tensor-mapping-cone-iso. This identifies the entire strict cone towers.
6. Choose a zero localized transition at level n. Both localized functors preserve it,
and the natural comparison in step 5 identifies it with the transformed cone transition.
The same m works, including m = n.
7. lem-weil-pbc-ringed-strict-tower-homotopy-limit gives invertibility of Rlim(v) for
these pro-zero cones. Its universal comparison identifies any pair (RF,η) with that pair.
8. Ordinary constant extension sends A to O by s tensor underline a ↦ s φ(a).
This multiplication isomorphism is uniquely determined on local pure tensors. Its
single-complex extension and the tensor unitor give flatConstantTensorUnit. Applying
the strict functor to α,β therefore gives strict cones with wα = β. Their limit maps
are exactly flatConstantStrictConeMap; on K-injective replacements j they are Q(lim(jα)).
9. By lem-weil-pbc-kinjective-hom-derived, represent the map between K-injective tower
resolutions by a chain map h. Its composites with the two resolutions are homotopic;
compose that tower homotopy with α. The additive inverse-limit functor preserves the
homotopy, giving Q(lim h) Q(lim(jα)) = Q(lim(jβ)). Under the derived comparisons this is
the unit equality below. No independent triangulated-category map has been selected. -/
theorem flatConstantTensorProZeroCones [IsNoetherianRing A]
    [HasDerivedCategory.{wA} (ModuleCat.{max u v} A)]
    [HasDerivedCategory.{wO} (ℕᵒᵖ ⥤ SheafOfModules.{max u v}
      (SheafOfModules.derivedChangeRingIndependentCoefficients.{max u v, u, v} J O))]
    (hflat : SheafOfModules.IsFlatOnSite.{u, v, max u v, max u v}
      (C := C) (J := J) (R := realizationRing J A)
      ((SheafOfModules.restrictScalars.{max u v, v, max u v, u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
          (SheafOfModules.unit.{v, u, max u v}
            (SheafOfModules.derivedChangeRingIndependentCoefficients.{max u v, u, v} J O))))
    (X Y : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{max u v} A) ℤ) (v : X ⟶ Y)
    (hv : FlatConstantConeProZero.{(max u v) + 1, max u v, wA} v)
    (P : CochainComplex (SheafOfModules.{max u v}
      (SheafOfModules.derivedChangeRingIndependentCoefficients.{max u v, u, v} J O)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{u, v, max u v}
      (C := C) (J := J) (R := O) P) :
    FlatConstantConeProZero.{(max u v) + 1, max u v, wO}
      (Functor.whiskerRight v (flatConstantTensorFunctor J A φ P)) ∧
    ∃ i : (flatConstantExtension J A φ).obj (ModuleCat.of A A) ≅
        SheafOfModules.unit
          (SheafOfModules.derivedChangeRingIndependentCoefficients.{max u v, u, v} J O),
      FlatConstantUnitNormalized J A φ i ∧
      ∀ (RF : DerivedCategory (ℕᵒᵖ ⥤ SheafOfModules.{max u v}
            (SheafOfModules.derivedChangeRingIndependentCoefficients.{max u v, u, v} J O)) ⥤
          DerivedCategory (SheafOfModules.{max u v}
            (SheafOfModules.derivedChangeRingIndependentCoefficients.{max u v, u, v} J O)))
        (η : Functor.mapHomologicalComplex
          (lim : (ℕᵒᵖ ⥤ SheafOfModules.{max u v}
              (SheafOfModules.derivedChangeRingIndependentCoefficients.{max u v, u, v} J O)) ⥤
            SheafOfModules.{max u v}
              (SheafOfModules.derivedChangeRingIndependentCoefficients.{max u v, u, v} J O))
                    (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF),
        RF.IsRightDerivedFunctor η (HomologicalComplex.quasiIso _ (.up ℤ)) →
        IsIso (RF.map (DerivedCategory.Q.map (flatConstantTowerComplex.map
          (Functor.whiskerRight v (flatConstantTensorFunctor J A φ P))))) ∧
        ∀ (α : (Functor.const ℕᵒᵖ).obj
              ((HomologicalComplex.single (ModuleCat.{max u v} A) (.up ℤ) 0).obj
                (ModuleCat.of A A)) ⟶ X)
          (β : (Functor.const ℕᵒᵖ).obj
              ((HomologicalComplex.single (ModuleCat.{max u v} A) (.up ℤ) 0).obj
                (ModuleCat.of A A)) ⟶ Y),
          α ≫ v = β →
          flatConstantUnitLimitMap J A φ RF η P i α ≫
            RF.map (DerivedCategory.Q.map (flatConstantTowerComplex.map
              (Functor.whiskerRight v (flatConstantTensorFunctor J A φ P)))) =
          flatConstantUnitLimitMap J A φ RF η P i β := sorry

end CategoryTheory
