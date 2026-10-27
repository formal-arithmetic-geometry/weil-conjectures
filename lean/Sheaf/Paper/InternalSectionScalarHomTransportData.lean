/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q127
-/
module

public import Sheaf.Paper.InternalSectionHomComparisonData
public import Sheaf.Paper.InternalScalarTensorComparison
public import Sheaf.Paper.InternalSectionDerivedTensorComparison
public import Sheaf.CategoryTheory.InternalSectionScalarAdjunction
public import Sheaf.Algebra.Homology.ScalarInternalHomData
public import Sheaf.Paper.DerivedInternalHomFilteredColimitData
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
public import Sheaf.Paper.InternalSectionTotalComparison

/-! # Normalized internal-to-section Hom comparison data

Source: Stacks Project, Tags 08J9, 0A95, 03EK, 07A4 and 07A6; the agent
presentation-transport argument in the DAG
(blueprint: def-sfb-internal-section-scalar-hom-transport-data).

The continuity arrows below are termwise colimit arrows of whole functorial
representative systems. They are not colimits formed in a derived category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- Avoid unresolved maximum universes in unrelated imported coefficient instances.
attribute [-instance] WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify
  WeilConjectures.integralReductionSiteEssentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale WeilConjectures
open scoped CategoryTheory.Obj
open CategoryTheory.InternalAbelianSheafModule

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory
attribute [local irreducible] Sheaf.monoidalCategory

attribute [local irreducible] CondensedRing.derivedHom CondensedRing.derivedTensor
  CondensedRing.internalScalarTensorIso
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor

namespace AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison

attribute [local instance] isCommMonObj_condensedRingObj

private instance nativeComm
    (R : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj R] [IsCommMonObj R] (Y : Scheme.{u}) :
    IsCommMonObj (condensedRingObj.{u} R Y) :=
  isCommMonObj_condensedRingObj R Y

private instance comparisonAdditive
    (R : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj R] [IsCommMonObj R] (Y : Scheme.{u}) :
    (equivalence.{u} R Y).functor.Additive :=
  comparison_additive (Scheme.ProEt.topology Y) (condensedRingObj.{u} R Y)

universe a₀ b₀ a₁ b₁


/-- The evaluation transpose under a tensor comparison, with abstract category endpoints.
Keeping this construction abstract avoids unfolding the native derived closed structure.
Source: Stacks 07A4, 08J9
(blueprint: def-sfb-internal-section-scalar-hom-transport-data). -/
def scalarHomMate
    {C : Type a₀} [Category.{b₀} C] {D : Type a₁} [Category.{b₁} D]
    (T : C ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ C)
    (S : D ⥤ D ⥤ D) (J : Dᵒᵖ ⥤ D ⥤ D)
    (adj : T ⊣₂ H) (adj' : S ⊣₂ J) (F : C ⥤ D)
    (μ : (Functor.postcompose₂.obj F).obj T ≅
      (((Functor.whiskeringLeft₂ _).obj F).obj F).obj S) (K L : C) :
    F.obj ((H.obj (op K)).obj L) ⟶ (J.obj (op (F.obj K))).obj (F.obj L) :=
  adj'.homEquiv ((μ.inv.app K).app ((H.obj (op K)).obj L) ≫
    F.map ((adj.adj K).counit.app L))

variable (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})

section Scalar
variable {X}
variable {Λ}
variable {Γ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}}
  [MonObj Γ] [IsCommMonObj Γ] (a : Λ ⟶ Γ) [IsMonHom a]
  [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap.{u} a Z))]

/-- The evaluation-transpose scalar comparison in the native internal category.
This is a map, without any assertion of invertibility.
Source: Stacks 07A4, 08J9
(blueprint: def-sfb-internal-section-scalar-hom-transport-data). -/
def internalScalarHom (K L : DerivedCategory.{u + 1} (Internal.{u} Λ X)) :
    (CondensedRing.internalScalarExtension.{u} a X).obj
      (((CondensedRing.derivedHom.{u} Λ X).obj (op K)).obj L) ⟶
    ((CondensedRing.derivedHom.{u} Γ X).obj
      (op ((CondensedRing.internalScalarExtension.{u} a X).obj K))).obj
        ((CondensedRing.internalScalarExtension.{u} a X).obj L) :=
  (CondensedRing.derivedTensorHomAdjunction.{u} Γ
    ((CondensedRing.internalScalarExtension.{u} a X).obj K)).homEquiv _ _
    (((CondensedRing.internalScalarTensorIso.{u} a X).inv.app K).app
        (((CondensedRing.derivedHom.{u} Λ X).obj (op K)).obj L) ≫
      (CondensedRing.internalScalarExtension.{u} a X).map
        ((CondensedRing.derivedTensorHomAdjunction.{u} Λ K).counit.app L))

/-- The internal restricted comparison is the five normalized adjunction bijections
at the identity, using the native closed adjunction and scalar tensor comparison.
Source: Stacks 07A6, 08J9
(blueprint: def-sfb-internal-section-scalar-hom-transport-data). -/
def internalRestrictedHom (K : DerivedCategory.{u + 1} (Internal.{u} Λ X))
    (N : DerivedCategory.{u + 1} (Internal.{u} Γ X)) :
    (Mod.comap (coefficientMap.{u} a X)).mapDerivedCategory.obj
        (((CondensedRing.derivedHom.{u} Γ X).obj
          (op ((CondensedRing.internalScalarExtension.{u} a X).obj K))).obj N) ⟶
      ((CondensedRing.derivedHom.{u} Λ X).obj (op K)).obj
        ((Mod.comap (coefficientMap.{u} a X)).mapDerivedCategory.obj N) :=
  (CondensedRing.derivedTensorHomAdjunction.{u} Λ K).homEquiv _ _
    ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap.{u} a X)).homEquiv _ _
      (((CondensedRing.internalScalarTensorIso.{u} a X).hom.app K).app _ ≫
        ((CondensedRing.derivedTensorHomAdjunction.{u} Γ
          ((CondensedRing.internalScalarExtension.{u} a X).obj K)).homEquiv _ _).symm
          (((Mod.derivedExtendMapDerivedCategoryAdjunction
            (coefficientMap.{u} a X)).homEquiv _ _).symm (𝟙 _))))

variable (X)
  (M : ScalarHomModels.{u + 1, u, u, u + 1} (Scheme.ProEt.topology X))
  (μ : ∀ {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (f : R ⟶ S),
    ScalarHomTensorComparison.{u + 1, u, u, u + 1} M f)
  (PΛ : HomPresentation.{u} Λ X (M.closed (ring.{u} Λ X)) (M.model (ring.{u} Λ X)))
  (PΓ : HomPresentation.{u} Γ X (M.closed (ring.{u} Γ X)) (M.model (ring.{u} Γ X)))

/-- The scalar tensor square as a named predicate, to keep transport data compact.
Source: Stacks 07A4 (blueprint: def-sfb-internal-section-scalar-hom-transport-data). -/
def ScalarTransportTensor
    (extension : CondensedRing.internalScalarExtension.{u} a X ⋙ forward.{u} Γ X ≅
      forward.{u} Λ X ⋙ (M.scalar (sectionCoefficientMap.{u} a)).derived) : Prop :=
  ∀ K L : DerivedCategory.{u + 1} (Internal.{u} Λ X),
    (forward.{u} Γ X).map (((CondensedRing.internalScalarTensorIso.{u} a X).hom.app K).app L) ≫
        PΓ.tensor.iso.hom.app
          ((CondensedRing.internalScalarExtension.{u} a X).obj K,
            (CondensedRing.internalScalarExtension.{u} a X).obj L) ≫
        (M.closed (ring.{u} Γ X)).tensor.map
          (X := ((forward.{u} Γ X).obj ((CondensedRing.internalScalarExtension.{u} a X).obj K),
            (forward.{u} Γ X).obj ((CondensedRing.internalScalarExtension.{u} a X).obj L)))
          (Y := ((M.scalar (sectionCoefficientMap.{u} a)).derived.obj
              ((forward.{u} Λ X).obj K),
            (M.scalar (sectionCoefficientMap.{u} a)).derived.obj
              ((forward.{u} Λ X).obj L)))
          (extension.hom.app K, extension.hom.app L) =
      extension.hom.app (((CondensedRing.derivedTensor.{u} Λ X).obj K).obj L) ≫
        (M.scalar (sectionCoefficientMap.{u} a)).derived.map (PΛ.tensor.iso.hom.app (K, L)) ≫
        (μ (sectionCoefficientMap.{u} a)).iso.hom.app
          ((forward.{u} Λ X).obj K, (forward.{u} Λ X).obj L)

/-- The scalar Hom square as a named predicate, retaining its actual evaluation map.
Source: Stacks 08J9 (blueprint: def-sfb-internal-section-scalar-hom-transport-data). -/
def ScalarTransportHom
    (extension : CondensedRing.internalScalarExtension.{u} a X ⋙ forward.{u} Γ X ≅
      forward.{u} Λ X ⋙ (M.scalar (sectionCoefficientMap.{u} a)).derived) : Prop :=
  ∀ K L : DerivedCategory.{u + 1} (Internal.{u} Λ X),
    (forward.{u} Γ X).map (internalScalarHom.{u} a K L) ≫
        PΓ.homIso.hom.app (op ((CondensedRing.internalScalarExtension.{u} a X).obj K),
          (CondensedRing.internalScalarExtension.{u} a X).obj L) ≫
        (ModuleObjectRingedComparison.hom.{u} Γ X).map
          (X := (op ((forward.{u} Γ X).obj
              ((CondensedRing.internalScalarExtension.{u} a X).obj K)),
            (forward.{u} Γ X).obj ((CondensedRing.internalScalarExtension.{u} a X).obj L)))
          (Y := (op ((M.scalar (sectionCoefficientMap.{u} a)).derived.obj
              ((forward.{u} Λ X).obj K)),
            (M.scalar (sectionCoefficientMap.{u} a)).derived.obj
              ((forward.{u} Λ X).obj L)))
          ((extension.inv.app K).op, extension.hom.app L) =
      extension.hom.app (((CondensedRing.derivedHom.{u} Λ X).obj (op K)).obj L) ≫
        (M.scalar (sectionCoefficientMap.{u} a)).derived.map (PΛ.homIso.hom.app (op K, L)) ≫
        coefficientBaseChangeHom (M.closed (ring.{u} Λ X)) (M.closed (ring.{u} Γ X))
          (M.scalar (sectionCoefficientMap.{u} a)).derived (μ (sectionCoefficientMap.{u} a)).iso
          ((forward.{u} Λ X).obj K) ((forward.{u} Λ X).obj L)

/-- The canonical scalar identifications, pinned by the unchanged section maps,
the localized restriction comparison and the normalized scalar Hom transposes.
Source: Stacks 03EK, 07A4, 07A6, 08J9
(blueprint: def-sfb-internal-section-scalar-hom-transport-data). -/
structure ScalarTransport where
  /-- Ordinary restriction fixes underlying sections. -/
  restriction : Mod.comap (coefficientMap.{u} a X) ⋙ (equivalence.{u} Λ X).functor ≅
    (equivalence.{u} Γ X).functor ⋙
      SheafOfModules.scalarRestriction.{u + 1, u, u + 1} (sectionCoefficientMap.{u} a)
  /-- No change of section maps is allowed. -/
  sections : ∀ (N : Internal.{u} Γ X) (U : X.ProEtᵒᵖ) (x : N.X.obj.obj U),
    (restriction.hom.app N).val.app U x = x
  /-- The actual localized restriction square. -/
  derivedRestriction : (Mod.comap (coefficientMap.{u} a X)).mapDerivedCategory ⋙ forward.{u} Λ X ≅
    forward.{u} Γ X ⋙
      SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
        (sectionCoefficientMap.{u} a)
  /-- Restriction is derived from the section identity just specified. -/
  restrictionNormalization : derivedRestriction =
    (Functor.mapDerivedCategoryCompIso (Mod.comap (coefficientMap.{u} a X))
      (sectionForward.{u} Λ X)).symm ≪≫
      Functor.mapDerivedCategoryNatIso restriction ≪≫
      Functor.mapDerivedCategoryCompIso (sectionForward.{u} Γ X)
        (SheafOfModules.scalarRestriction.{u + 1, u, u + 1} (sectionCoefficientMap.{u} a))
  /-- The scalar-extension comparison. -/
  extension : CondensedRing.internalScalarExtension.{u} a X ⋙ forward.{u} Γ X ≅
    forward.{u} Λ X ⋙ (M.scalar (sectionCoefficientMap.{u} a)).derived
  /-- Compatibility with actual normalized adjunction transposes fixes extension. -/
  adjunction : ∀ (K : DerivedCategory.{u + 1} (Internal.{u} Λ X))
    (N : DerivedCategory.{u + 1} (Internal.{u} Γ X))
    (f : (CondensedRing.internalScalarExtension.{u} a X).obj K ⟶ N),
    (forward.{u} Λ X).map
        ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap.{u} a X)).homEquiv K N f)
        ≫ derivedRestriction.hom.app N =
      (M.scalar (sectionCoefficientMap.{u} a)).adjunction.homEquiv _ _
        (extension.inv.app K ≫ (forward.{u} Γ X).map f)
  /-- The normalized scalar tensor maps agree. -/
  tensor : ScalarTransportTensor.{u} (a := a) (X := X) (M := M)
    (μ := μ) (PΛ := PΛ) (PΓ := PΓ) extension
  /-- Equality of the actual evaluation-transpose scalar Hom maps. -/
  hom : ScalarTransportHom.{u} (a := a) (X := X) (M := M)
    (μ := μ) (PΛ := PΛ) (PΓ := PΓ) extension


end Scalar

end AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison
