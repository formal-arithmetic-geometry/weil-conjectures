/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.AlgebraicGeometry.GlobalDerivedHom
public import Sheaf.AlgebraicGeometry.QCqsDerivedDirectImageRightAdjoint
public import Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison
public import Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHom
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.AlgebraicGeometry.DQCoheratorAdjunction
import Sheaf.AlgebraicGeometry.QCqsSheafRHomAdjunction
import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition

/-! # Canonical global Hom adjunction
Source: Stacks Project, duality.tex, Tag 0B6I (lemma-iso-global-hom).
(blueprint: lem-pc-global-hom-adjunction).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (R : Type u) [Ring R], HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- Exact restriction along the map on global functions.
Source: Stacks, Tag 0B6I (blueprint: lem-pc-global-hom-adjunction). -/
def schemeGlobalScalarRestriction {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (ModuleCat.restrictScalars.{u}
    (R := (moduleRings Y.toRingedSpace).obj.obj (op ⊤))
    (S := (moduleRings X.toRingedSpace).obj.obj (op ⊤)) f.appTop.hom).mapDerivedCategory

/-- The canonical Leray comparison is the identity on underived sections and is
compatible with the right-derived units.
Source: Stacks, Tags 0B6I and 0D5T (blueprint: lem-pc-global-hom-adjunction).
Proof: the underived comparison is the identity on sections over the whole space.
Resolve by K-injective complexes. Direct image of a K-injective is acyclic for
subsequent global sections, by the pullback/direct-image adjunction and derived
composition. The right-derived universal property extends the identity comparison
uniquely and gives the displayed unit equation. -/
theorem exists_schemeGlobalSectionsDirectImageIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ (c₀ : RingedSpace.moduleDirectImage f.toLRSHom.toShHom ⋙
        RingedSpace.globalSectionsFunctor Y.toRingedSpace ≅
      RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
        ModuleCat.restrictScalars.{u}
          (R := (moduleRings Y.toRingedSpace).obj.obj (op ⊤))
          (S := (moduleRings X.toRingedSpace).obj.obj (op ⊤)) f.appTop.hom)
      (c : schemeDerivedDirectImage f ⋙ schemeDerivedGlobalSections Y ≅
        schemeDerivedGlobalSections X ⋙ schemeGlobalScalarRestriction f),
      (∀ (F : SheafOfModules.{u} (moduleRings X.toRingedSpace))
        (x : (RingedSpace.moduleDirectImage f.toLRSHom.toShHom ⋙
          RingedSpace.globalSectionsFunctor Y.toRingedSpace).obj F),
        (c₀.hom.app F).hom x = x) ∧
      (∀ K : HomotopyCategory
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ),
        (RingedSpace.globalSectionsFunctor Y.toRingedSpace).rightDerivedFunctorUnit.app
            (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj K) ≫
          (schemeDerivedGlobalSections Y).map
            ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit.app K) ≫
          c.hom.app (DerivedCategory.Qh.obj K) =
        (DerivedCategory.Qh
          (C := ModuleCat.{u} ((moduleRings Y.toRingedSpace).obj.obj (op ⊤)))).map
          ((Functor.mapHomotopyCategoryCompIso
            (Iso.refl (RingedSpace.moduleDirectImage f.toLRSHom.toShHom ⋙
              RingedSpace.globalSectionsFunctor Y.toRingedSpace))
            (ComplexShape.up ℤ)).hom.app K ≫
            (Functor.mapHomotopyCategoryCompIso c₀.symm
              (ComplexShape.up ℤ)).inv.app K) ≫
          (ModuleCat.restrictScalars.{u}
            (R := (moduleRings Y.toRingedSpace).obj.obj (op ⊤))
            (S := (moduleRings X.toRingedSpace).obj.obj (op ⊤))
            f.appTop.hom).mapDerivedCategoryFactorsh.inv.app
              (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomotopyCategory
                (ComplexShape.up ℤ)).obj K) ≫
          (schemeGlobalScalarRestriction f).map
            ((RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctorUnit.app K))
      := by
  sorry

/-- The canonical derived Leray isomorphism, chosen with its unit compatibility.
Source: Stacks, Tags 0B6I and 0D5T (blueprint: lem-pc-global-hom-adjunction). -/
def schemeGlobalSectionsDirectImageIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    schemeDerivedDirectImage f ⋙ schemeDerivedGlobalSections Y ≅
      schemeDerivedGlobalSections X ⋙ schemeGlobalScalarRestriction f :=
  Classical.choose (Classical.choose_spec (exists_schemeGlobalSectionsDirectImageIso f))


/-- The same pinned derived adjunction as the canonical base-change map.
Source: Stacks, Tags 079W and 0B6I (blueprint: lem-pc-global-hom-adjunction). -/
def schemeHomPullbackAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    derivedPullback f ⊣ schemeDerivedDirectImage f :=
  Classical.choose (exists_schemeDerivedAdjunction f
    (hAdd := (Classical.choose exists_derivedPullbackComposition) f)
    ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) f)
    ((Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) f))

/-- The canonical comparison of def-pc-derived-pullback-tensor-comparison is an iso.
Source: Stacks, Tags 079U and 0B6I (blueprint: lem-pc-global-hom-adjunction).
Proof: choose K-flat representatives. The canonical module tensor comparison is
invertible on each summand. Pullback and tensor preserve K-flatness, so the
left-derived counits and localization tensor maps in the characterising equation
are invertible. Thus the comparison is invertible on representatives, and hence
on all objects by naturality and existence of K-flat resolutions. -/
theorem exists_schemeHomTensorPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ t : tensor (schemeDerivedCategory Y) ⋙ derivedPullback f ≅
      (derivedPullback f).prod (derivedPullback f) ⋙ tensor (schemeDerivedCategory X),
      IsCanonicalPullbackTensorComparison f (fun K L ↦ t.hom.app (K, L)) := by
  sorry

/-- The canonical derived pullback tensor iso, specified on K-flat representatives.
Source: Stacks, Tags 079U and 0B6I (blueprint: lem-pc-global-hom-adjunction). -/
def schemeHomTensorPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    tensor (schemeDerivedCategory Y) ⋙ derivedPullback f ≅
      (derivedPullback f).prod (derivedPullback f) ⋙ tensor (schemeDerivedCategory X) :=
  Classical.choose (exists_schemeHomTensorPullbackIso f)

/-- Existence of the evaluation-mate direct-image internal Hom comparison.
Fixed-data form of the landed `exists_derivedDirectImage_internalHom_comparison`,
using the pinned tensor-Hom family.
All adjunction and tensor data here are fixed, shared with the pullback comparison.
Source: Stacks, Tags 08I3 and 0B6I (blueprint: lem-pc-global-hom-adjunction).
Proof: for every test object A transpose a map into Rf_* internal Hom by the
pullback adjunction and tensor-Hom bijection. Pull back A tensor Rf_*L, apply the
counit at L, then evaluation. Transpose back. This is natural in A, so Yoneda
gives the specified map, and naturality in both Hom entries gives the transformation. -/
theorem exists_schemeHomDirectImageComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ c : derivedInternalHom (Opens.grothendieckTopology X) X.sheaf ⋙
        schemeDerivedDirectImage f ⟶
      (schemeDerivedDirectImage f).op.prod (schemeDerivedDirectImage f) ⋙
        derivedInternalHom (Opens.grothendieckTopology Y) Y.sheaf,
      ∀ (L M : schemeDerivedCategory X) (A : schemeDerivedCategory Y)
        (α : A ⟶ (schemeDerivedDirectImage f).obj
          ((derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).obj (op L, M))),
        (schemeDerivedTensorHomEquiv Y) A
          ((schemeDerivedDirectImage f).obj L) ((schemeDerivedDirectImage f).obj M)
            (α ≫ c.app (op L, M)) =
          (schemeHomPullbackAdjunction f).homEquiv (A ⊗ (schemeDerivedDirectImage f).obj L) M
            ((schemeHomTensorPullbackIso f).hom.app (A, (schemeDerivedDirectImage f).obj L) ≫
              (𝟙 ((derivedPullback f).obj A) ⊗ₘ
                (schemeHomPullbackAdjunction f).counit.app L) ≫
              (schemeDerivedTensorHomEquiv X)
                ((derivedPullback f).obj A) L M
                  (((schemeHomPullbackAdjunction f).homEquiv A
                    ((derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).obj
                      (op L, M))).symm α)) := by
  sorry

/-- The canonical global direct-image Hom comparison: Leray followed by the
internal-Hom comparison defined by the evaluation mate equation.
Source: Stacks, Tag 0B6I (blueprint: lem-pc-global-hom-adjunction). -/
def schemeGlobalHomDirectImageMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : schemeDerivedCategory X) :
    (schemeGlobalScalarRestriction f).obj ((schemeGlobalDerivedHom X).obj (op P, Q)) ⟶
      (schemeGlobalDerivedHom Y).obj
        (op ((schemeDerivedDirectImage f).obj P), (schemeDerivedDirectImage f).obj Q) :=
  (schemeGlobalSectionsDirectImageIso f).inv.app
      ((derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).obj (op P, Q)) ≫
    (schemeDerivedGlobalSections Y).map
      ((Classical.choose (exists_schemeHomDirectImageComparison f)).app (op P, Q))

/-- The global Hom adjunction map is induced by the counit, not an arbitrary iso.
Source: Stacks, Tag 0B6I (blueprint: lem-pc-global-hom-adjunction). -/
def schemeGlobalHomAdjunctionMap {X Y : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y)
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (adj : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
      (fun E ↦ (schemeDerivedDirectImage_qcqs_hasRightAdjoint X Y f).fst
        E.obj E.property) ⊣ a)
    (P : schemeDerivedQCohCategory X) (K : schemeDerivedQCohCategory Y) :
    (schemeGlobalScalarRestriction f).obj
      ((schemeGlobalDerivedHom X).obj (op P.obj, (a.obj K).obj)) ⟶
      (schemeGlobalDerivedHom Y).obj (op ((schemeDerivedDirectImage f).obj P.obj), K.obj) :=
  schemeGlobalHomDirectImageMap f P.obj (a.obj K).obj ≫
    (schemeGlobalDerivedHom Y).map ((𝟙 _).op, (adj.counit.app K).hom)

/-- The counit-induced global Hom adjunction is invertible, naturally in P and K.
Source: Stacks, Tag 0B6I (blueprint: lem-pc-global-hom-adjunction).
Proof:
1. The qcqs right adjoint supplies the counit (sheafy trace). The evaluation-mate
comparison followed by internal Hom of this counit is invertible after DQ_Y, by
lem-pc-qcqs-sheaf-rhom-adjunction.
2. Apply derived global sections and the canonical Leray comparison. This is the
map above, by def-pc-global-derived-rhom and derived direct-image composition.
3. By lem-pc-dq-coherator-adjunction, H^i(Y,E) = Hom(O_Y[-i],DQ_Y(E)), since O_Y[-i]
is quasi-coherent. Thus the comparison is a quasi-isomorphism on global sections.
4. Naturality of the comparisons and the counit supplies naturality in both entries. -/
theorem schemeGlobalHomAdjunctionMap_isIso {X Y : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y)
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (adj : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
      (fun E ↦ (schemeDerivedDirectImage_qcqs_hasRightAdjoint X Y f).fst
        E.obj E.property) ⊣ a) :
    (∀ (P : schemeDerivedQCohCategory X) (K : schemeDerivedQCohCategory Y),
      IsIso (schemeGlobalHomAdjunctionMap f a adj P K)) ∧
    (∀ (P P' : schemeDerivedQCohCategory X) (K K' : schemeDerivedQCohCategory Y)
        (s : P' ⟶ P) (t : K ⟶ K'),
      (schemeGlobalScalarRestriction f).map
        ((schemeGlobalDerivedHom X).map (s.hom.op, (a.map t).hom)) ≫
          schemeGlobalHomAdjunctionMap f a adj P' K' =
        schemeGlobalHomAdjunctionMap f a adj P K ≫
          (schemeGlobalDerivedHom Y).map
            (((schemeDerivedDirectImage f).map s.hom).op, t.hom)) := by
  sorry

/-- The canonical global Hom adjunction iso.
Source: Stacks, Tag 0B6I (blueprint: lem-pc-global-hom-adjunction). -/
def schemeGlobalHomAdjunctionIso {X Y : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y)
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (adj : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
      (fun E ↦ (schemeDerivedDirectImage_qcqs_hasRightAdjoint X Y f).fst
        E.obj E.property) ⊣ a)
    (P : schemeDerivedQCohCategory X) (K : schemeDerivedQCohCategory Y) :
    (schemeGlobalScalarRestriction f).obj
      ((schemeGlobalDerivedHom X).obj (op P.obj, (a.obj K).obj)) ≅
      (schemeGlobalDerivedHom Y).obj (op ((schemeDerivedDirectImage f).obj P.obj), K.obj) :=
  haveI := (schemeGlobalHomAdjunctionMap_isIso f a adj).1 P K
  asIso (schemeGlobalHomAdjunctionMap f a adj P K)

end AlgebraicGeometry
