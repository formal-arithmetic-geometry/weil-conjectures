/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q127
-/
module

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
(blueprint: def-sfb-internal-section-hom-comparison-data).

The continuity arrows below are termwise colimit arrows of whole functorial
representative systems. They are not colimits formed in a derived category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
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

attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor

namespace AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison

universe a₀ b₀ a₁ b₁

attribute [local irreducible] CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence

/-- The localization/evaluation square with its endpoints abstracted, to keep
concrete sheafification and derived-category constructions opaque during elaboration.
Source: Stacks 08J9, 0A95
(blueprint: def-sfb-internal-section-hom-comparison-data). -/
def homRepresentativeSquare
    {C : Type a₀} [Category.{b₀} C] {D : Type a₁} [Category.{b₁} D]
    (F : C ⥤ D) (H : Cᵒᵖ × C ⥤ C) (H' : Dᵒᵖ × D ⥤ D)
    (θ : H ⋙ F ≅ F.op.prod F ⋙ H')
    (P N : C) (P' N' : D) (p : F.obj P ≅ P') (n : F.obj N ≅ N')
    {V : C} {W W' : D} (j : V ⟶ H.obj (op P, N))
    (l : F.obj V ≅ W) (r : W ≅ W') (h : H'.obj (op P', N') ≅ W') : Prop :=
  F.map j ≫ θ.hom.app (op P, N) ≫
      H'.map (X := (op (F.obj P), F.obj N)) (Y := (op P', N'))
        (p.inv.op, n.hom) ≫ h.hom = l.hom ≫ r.hom

universe i

/-- The comparison square of post-colimit arrows under a functor.
Source: Categories Tag 002F
(blueprint: def-sfb-internal-section-hom-comparison-data). -/
def PostComparisonSquare
    {C : Type a₀} [Category.{b₀} C] {E : Type a₁} [Category.{b₁} E]
    {I : Type*} [Category I] [HasColimitsOfShape I C] [HasColimitsOfShape I E]
    (F : C ⥤ E) [PreservesColimitsOfShape I F]
    (G : C ⥤ C) (H : E ⥤ E) (σ : G ⋙ F ≅ F ⋙ H) (D : I ⥤ C) : Prop :=
  F.map (colimit.post D G) ≫ σ.hom.app (colimit D) ≫
      H.map (preservesColimitIso F D).hom =
    (preservesColimitIso F (D ⋙ G)).hom ≫
      colimMap (Functor.isoWhiskerLeft D σ).hom ≫ colimit.post (D ⋙ F) H

/-- Continuity on all small filtered diagrams with a common termwise lower bound.
Source: Stacks 0A95, 03DB
(blueprint: def-sfb-internal-section-hom-comparison-data). -/
def BoundedFilteredContinuity
    {C : Type a₀} [Category.{b₀} C] [Abelian C] [HasColimitsOfSize.{i, i} C]
    (G : CochainComplex C ℤ ⥤ CochainComplex C ℤ) : Prop :=
  ∀ (I : Type i) [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CochainComplex C ℤ) (b : ℤ),
    (∀ (j : I) (n : ℤ), n < b → IsZero ((D.obj j).X n)) →
      QuasiIso (colimit.post D G)

/-- The comparison square of induced colimit maps under a functor.
Source: Categories Tag 002F
(blueprint: def-sfb-internal-section-hom-comparison-data). -/
def ColimitMapSquare
    {C : Type a₀} [Category.{b₀} C] {E : Type a₁} [Category.{b₁} E]
    {I : Type*} [Category I] [HasColimitsOfShape I C] [HasColimitsOfShape I E]
    (F : C ⥤ E) [PreservesColimitsOfShape I F]
    (D E₀ : I ⥤ C) (D' E' : I ⥤ E)
    (d : D ⋙ F ≅ D') (e : E₀ ⋙ F ≅ E') (f : D ⟶ E₀) (g : D' ⟶ E') : Prop :=
  F.map (colimMap f) ≫ (preservesColimitIso F E₀).hom ≫ colimMap e.hom =
    (preservesColimitIso F D).hom ≫ colimMap d.hom ≫ colimMap g

variable (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})

/-- Right evaluation in the native unbounded internal-module derived category.
Source: Stacks 08J9 (blueprint: def-sfb-internal-section-hom-comparison-data). -/
def internalEvaluation (K L : DerivedCategory.{u + 1} (Internal.{u} Λ X)) :
    ((CondensedRing.derivedTensor.{u} Λ X).obj
      (((CondensedRing.derivedHom.{u} Λ X).obj (op K)).obj L)).obj K ⟶ L :=
  (@BraidedCategory.braiding _ _ _ (internalBraiding.{u} Λ X)
      (((CondensedRing.derivedHom.{u} Λ X).obj (op K)).obj L) K).hom ≫
    (CondensedRing.derivedTensorHomAdjunction.{u} Λ K).counit.app L

/-- The normalized Hom identification for specified K-flat tensor models.
Its evaluation equation determines the Hom isomorphism, rather than allowing
an arbitrary isomorphism between the same objects.
Source: Stacks 08J9, 0A95
(blueprint: def-sfb-internal-section-hom-comparison-data). -/
structure HomPresentation
    (S : CoefficientClosedStructure (hom.{u} Λ X))
    (T : CoefficientTensorModels.{u, u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (ring.{u} Λ X) S) where
  /-- The K-flat-normalized tensor comparison of the dependency. -/
  tensor : TensorComparison.{u} Λ X S T
  /-- The natural comparison on both Hom inputs. -/
  homIso : Functor.uncurry.obj (CondensedRing.derivedHom.{u} Λ X) ⋙ forward.{u} Λ X ≅
    ((forward.{u} Λ X).op.prod (forward.{u} Λ X)) ⋙ hom.{u} Λ X
  /-- Evaluation fixes the comparison. -/
  evaluation : ∀ K L : DerivedCategory.{u + 1} (Internal.{u} Λ X),
    (forward.{u} Λ X).map (internalEvaluation.{u} Λ X K L) =
      tensor.iso.hom.app ((((CondensedRing.derivedHom.{u} Λ X).obj (op K)).obj L), K) ≫
        S.tensor.map
          (X := ((forward.{u} Λ X).obj (((CondensedRing.derivedHom.{u} Λ X).obj (op K)).obj L),
            (forward.{u} Λ X).obj K))
          (Y := ((hom.{u} Λ X).obj (op ((forward.{u} Λ X).obj K), (forward.{u} Λ X).obj L),
            (forward.{u} Λ X).obj K))
          (homIso.hom.app (op K, L), 𝟙 _) ≫
        S.evaluation ((forward.{u} Λ X).obj K) ((forward.{u} Λ X).obj L)

/-- Transport the entire functorial section-Hom representative system, including
its morphisms, through the fixed inverse equivalence.
Source: Stacks 0A95 (blueprint: def-sfb-internal-section-hom-comparison-data). -/
def internalHomRepresentative (P : CochainComplex (Internal.{u} Λ X) ℤ) :
    CochainComplex (Internal.{u} Λ X) ℤ ⥤ CochainComplex (Internal.{u} Λ X) ℤ :=
  complexForward.{u} Λ X ⋙
    SfbHomFilteredColimit.homFixed.{u + 1, u, u} (Scheme.ProEt.topology X) (ring.{u} Λ X)
      ((complexForward.{u} Λ X).obj P) ⋙
    (equivalence.{u} Λ X).inverse.mapHomologicalComplex (.up ℤ)

/-- Whiskering the actual counit, with abstract category endpoints kept explicit.
Source: Stacks 0A95
(blueprint: def-sfb-internal-section-hom-comparison-data). -/
def representativeCounit
    {C : Type a₀} [Category.{b₀} C] {D : Type a₁} [Category.{b₁} D]
    (e : C ≌ D) (H : D ⥤ D) :
    (e.functor ⋙ H ⋙ e.inverse) ⋙ e.functor ≅ e.functor ⋙ H :=
  Functor.isoWhiskerLeft (e.functor ⋙ H) e.counitIso

/-- The comparison on functorial representatives is the actual equivalence counit.
Source: Stacks 0A95 (blueprint: def-sfb-internal-section-hom-comparison-data). -/
def homRepresentativeIso (P : CochainComplex (Internal.{u} Λ X) ℤ) :
    internalHomRepresentative.{u} Λ X P ⋙ complexForward.{u} Λ X ≅
      complexForward.{u} Λ X ⋙
        SfbHomFilteredColimit.homFixed.{u + 1, u, u}
          (Scheme.ProEt.topology X) (ring.{u} Λ X) ((complexForward.{u} Λ X).obj P) :=
  by
    simpa only [internalHomRepresentative, complexForward, sectionForward_eq,
      Equivalence.mapHomologicalComplex] using
      representativeCounit ((equivalence.{u} Λ X).mapHomologicalComplex (.up ℤ))
      (SfbHomFilteredColimit.homFixed.{u + 1, u, u}
        (Scheme.ProEt.topology X) (ring.{u} Λ X)
        (((equivalence.{u} Λ X).functor.mapHomologicalComplex (.up ℤ)).obj P))

/-- The complete normalized localization square for the functorial Hom representatives.
This is the defining formula of `internalHomRepresentative_computes`, kept folded
when its concrete derived categories are checked by consumers.
Source: Stacks 08J9, 0A95
(blueprint: def-sfb-internal-section-hom-comparison-data). -/
def RepresentativeComputes
    (S : CoefficientClosedStructure (hom.{u} Λ X))
    (T : CoefficientTensorModels.{u, u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (ring.{u} Λ X) S)
    (H : HomPresentation.{u} Λ X S T)
    (P : CochainComplex (Internal.{u} Λ X) ℤ) : Prop :=
    ∃ j : internalHomRepresentative.{u} Λ X P ⋙ DerivedCategory.Q ≅
      DerivedCategory.Q ⋙
        (CondensedRing.derivedHom.{u} Λ X).obj (op (DerivedCategory.Q.obj P)),
      ∀ N : CochainComplex (Internal.{u} Λ X) ℤ,
        homRepresentativeSquare (forward.{u} Λ X)
          (Functor.uncurry.obj (CondensedRing.derivedHom.{u} Λ X)) (hom.{u} Λ X) H.homIso
          (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N)
          ((DerivedCategory.Q (C := Modules.{u} Λ X)).obj ((complexForward.{u} Λ X).obj P))
          ((DerivedCategory.Q (C := Modules.{u} Λ X)).obj ((complexForward.{u} Λ X).obj N))
          ((localizationIso.{u} Λ X).app P) ((localizationIso.{u} Λ X).app N)
          (j.hom.app N)
          ((localizationIso.{u} Λ X).app ((internalHomRepresentative.{u} Λ X P).obj N))
          ((DerivedCategory.Q (C := Modules.{u} Λ X)).mapIso
            ((homRepresentativeIso.{u} Λ X P).app N))
          (coefficientHomResolutionIso.{u, u + 1, u, u + 1}
            (Scheme.ProEt.topology X) (ring.{u} Λ X)
            ((complexForward.{u} Λ X).obj P) ((complexForward.{u} Λ X).obj N))

/-- Termwise reconstruction is an equivalence on the actual complexes.
Source: Stacks 010N (blueprint: def-sfb-internal-section-hom-comparison-data). -/
instance complexForward_isEquivalence : (complexForward.{u} Λ X).IsEquivalence :=
  inferInstanceAs (((equivalence.{u} Λ X).mapHomologicalComplex (.up ℤ)).functor.IsEquivalence)

omit [MonObj Λ] [IsCommMonObj Λ] in
/-- Reconstruct every commutative internal ring and its actual section maps.
Source: Stacks 03EK (blueprint: def-sfb-internal-section-hom-comparison-data). -/
def sectionRingFunctor : CommMon (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) ⥤
    Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} where
  obj R := sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X) R.X
  map f := sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology X) f.hom.hom
  map_id R := by ext U x; rfl
  map_comp f g := by ext U x; rfl

/-- The commutativity structure on a bundled ring's monoid projection is its own.
Source: Stacks 03EK
(blueprint: def-sfb-internal-section-hom-comparison-data). -/
instance coefficientToMonComm
    (R : CommMon (Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})) :
    IsCommMonObj R.toMon.X := R.comm

/-- The actual coefficient functor, including its composition and identity laws.
Source: Stacks 03EK
(blueprint: def-sfb-internal-section-hom-comparison-data). -/
def sectionCoefficientFunctor :
    CommMon (Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}) ⥤
      Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  (upperStarFromPoint X).mapCommMon ⋙ sectionRingFunctor.{u} X

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual scalar adjunction, with its native functor endpoints explicit.
Source: Stacks 07A6
(blueprint: def-sfb-internal-section-hom-comparison-data). -/
def internalScalarAdjunction
    {Γ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}}
    [MonObj Γ] [IsCommMonObj Γ] (a : Λ ⟶ Γ) [IsMonHom a]
    [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap.{u} a Z))] :
    CondensedRing.internalScalarExtension.{u} a X ⊣
      (Mod.comap (coefficientMap.{u} a X)).mapDerivedCategory :=
  Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap.{u} a X)

section CoherenceData
variable {Λ X}
  {Γ Δ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}}
  [MonObj Γ] [IsCommMonObj Γ] [MonObj Δ] [IsCommMonObj Δ]
  (a : Λ ⟶ Γ) [IsMonHom a] (b : Γ ⟶ Δ) [IsMonHom b]
  [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap.{u} a Z))]
  [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap.{u} b Z))]
  [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap.{u} (a ≫ b) Z))]

/-- Canonical internal derived restriction compositor, fixing the underlying sections.
Source: Stacks 07A6
(blueprint: def-sfb-internal-section-hom-comparison-data). -/
def internalRestrictionComp :
    (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
      (coefficientMap.{u} (a ≫ b) X)).mapDerivedCategory ≅
      (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
      (coefficientMap.{u} b X)).mapDerivedCategory ⋙
        (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
      (coefficientMap.{u} a X)).mapDerivedCategory :=
  Functor.mapDerivedCategoryNatIso
    (Mod.comapCongr (C := Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
      (coefficientMap_comp a b X) ≪≫
      Mod.comapComp (coefficientMap.{u} a X) (coefficientMap.{u} b X)) ≪≫
    Functor.mapDerivedCategoryCompIso
      (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
      (coefficientMap.{u} b X))
      (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
      (coefficientMap.{u} a X))

/-- Internal scalar compositor fixed by the units of the actual derived adjunctions.
Source: Stacks 07A6, 0D6D
(blueprint: def-sfb-internal-section-hom-comparison-data). -/
def internalExtensionComp :
    CondensedRing.internalScalarExtension.{u} a X ⋙
      CondensedRing.internalScalarExtension.{u} b X ≅
        CondensedRing.internalScalarExtension.{u} (a ≫ b) X :=
  Adjunction.leftAdjointUniq
    ((internalScalarAdjunction.{u} Λ X a).comp
      (internalScalarAdjunction.{u} Γ X b))
    ((internalScalarAdjunction.{u} Λ X (a ≫ b)).ofNatIsoRight
      (internalRestrictionComp.{u} a b))

end CoherenceData

/-- Internal restriction unitor, with identity on underlying sections.
Source: Stacks 07A6
(blueprint: def-sfb-internal-section-hom-comparison-data). -/
def internalRestrictionId :
    (Mod.comap (coefficientMap.{u} (𝟙 Λ) X)).mapDerivedCategory ≅
      𝟭 (DerivedCategory.{u + 1} (Internal.{u} Λ X)) :=
  Functor.mapDerivedCategoryNatIso
    (Mod.comapCongr (C := Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
      (coefficientMap_id X) ≪≫ Mod.comapId (condensedRingObj.{u} Λ X)) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- Internal scalar unitor fixed by the unit of the actual derived scalar adjunction.
Source: Stacks 07A6
(blueprint: def-sfb-internal-section-hom-comparison-data). -/
def internalExtensionId
    [∀ Z : Scheme.{u}, PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap.{u} (𝟙 Λ) Z))] :
    CondensedRing.internalScalarExtension.{u} (𝟙 Λ) X ≅
      𝟭 (DerivedCategory.{u + 1} (Internal.{u} Λ X)) :=
  Adjunction.leftAdjointUniq
    ((internalScalarAdjunction.{u} Λ X (𝟙 Λ)).ofNatIsoRight
      (internalRestrictionId.{u} Λ X)) Adjunction.id

section ScalarCoherence
variable {Λ X}
  {Γ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}}
  [MonObj Γ] [IsCommMonObj Γ] (a : Λ ⟶ Γ) [IsMonHom a]
/-- Reconstruction of the actual pulled-back coefficient map.
Source: Stacks 03EK (blueprint: def-sfb-internal-section-hom-comparison-data). -/
abbrev sectionCoefficientMap : ring.{u} Λ X ⟶ ring.{u} Γ X :=
  sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology X) (coefficientMap.{u} a X)

/-- Package the given condensed ring map without changing its underlying arrow.
Source: Stacks 03EK
(blueprint: def-sfb-internal-section-hom-comparison-data). -/
def condensedCoefficientHom : CommMon.mk Λ ⟶ CommMon.mk Γ :=
  CommMon.homMk (Mon.Hom.mk' a (IsMonHom.one_hom a) (IsMonHom.mul_hom a))

/-- The section scalar compositor, including the actual coefficient-functor law.
Source: Stacks 07A6, 0D6D
(blueprint: def-sfb-internal-section-hom-comparison-data). -/
def sectionExtensionComp
    (M : ScalarHomModels.{u + 1, u, u, u + 1} (Scheme.ProEt.topology X))
    {Δ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}}
    [MonObj Δ] [IsCommMonObj Δ] (b : Γ ⟶ Δ) [IsMonHom b] :
    (M.scalar (sectionCoefficientMap.{u} a)).derived ⋙
      (M.scalar (sectionCoefficientMap.{u} b)).derived ≅
        (M.scalar (sectionCoefficientMap.{u} (a ≫ b))).derived :=
  scalarHomExtensionComp M (sectionCoefficientMap.{u} a) (sectionCoefficientMap.{u} b) ≪≫
    eqToIso (congrArg (fun f ↦ (M.scalar f).derived)
      ((sectionCoefficientFunctor.{u} X).map_comp
        (condensedCoefficientHom.{u} a) (condensedCoefficientHom.{u} b)).symm)

end ScalarCoherence

/-- The section scalar unitor, including the actual coefficient-functor identity law.
Source: Stacks 07A6
(blueprint: def-sfb-internal-section-hom-comparison-data). -/
def sectionExtensionId
    (M : ScalarHomModels.{u + 1, u, u, u + 1} (Scheme.ProEt.topology X)) :
    (M.scalar (sectionCoefficientMap.{u} (X := X) (𝟙 Λ))).derived ≅
      𝟭 (DerivedCategory.{u + 1} (Modules.{u} Λ X)) :=
  eqToIso (congrArg (fun f ↦ (M.scalar f).derived)
      ((sectionCoefficientFunctor.{u} X).map_id (CommMon.mk Λ))) ≪≫
    scalarHomExtensionId M (ring.{u} Λ X)

end AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison
