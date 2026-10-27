/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FlatCurveDerivedStructureModel
public import Sheaf.AlgebraicGeometry.CoherentAffineBaseChangeEdge
import Sheaf.AlgebraicGeometry.Picard.FlatInvertibleCanonicalDerivedBaseChange
import WeilConjectures.AlgebraicGeometry.FlatModuleCanonicalDerivedPullback
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-! # Affine degree-one comparisons for a split structure complex -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
noncomputable section
open Scheme.Modules
attribute [local semireducible] topDegreeDerivedImage globalLerayImage
variable [hD : ∀ Y : Scheme.{u}, HasDerivedCategory.{w}
  (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

attribute [local irreducible] tensorPullback tensorPullbackObj
  schemeDerivedBaseChangeMap Functor.mapDerivedCategory Functor.rightDerivedFunctor
  singleDegreeBaseChangeComposite derivedStructureUnit DerivedCategory.homologyFunctor

attribute [local instance 2000]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf

/-- Cache the standard module-category instances used by the exported splitting signature.
Source: Mathlib's module sheaves and exact restriction functor.
(blueprint: new-curve-split-affine-coherent-edge). -/
local instance curveEdge_schemeAbelian (Y : Scheme.{u}) : Abelian
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) := inferInstance

local instance curveEdge_overAbelian (S : Scheme.{u}) (U : S.Opens) : Abelian
    (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) := inferInstance

local instance curveEdge_overHasColimits (S : Scheme.{u}) (U : S.Opens) : HasColimits
    (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) := inferInstance

local instance curveEdge_overAdditive (S : Scheme.{u}) (U : S.Opens) :
    (SheafOfModules.overFunctor.{u} (moduleRings S.toRingedSpace) U).Additive :=
  inferInstance

local instance curveEdge_overLimits (S : Scheme.{u}) (U : S.Opens) :
    PreservesFiniteLimits
      (SheafOfModules.overFunctor.{u} (moduleRings S.toRingedSpace) U) :=
  inferInstance

local instance curveEdge_overColimits (S : Scheme.{u}) (U : S.Opens) :
    PreservesFiniteColimits
      (SheafOfModules.overFunctor.{u} (moduleRings S.toRingedSpace) U) :=
  inferInstance

private local instance unit_quasicoherent (Y : Scheme.{u}) :
    (SheafOfModules.unit Y.ringCatSheaf).IsQuasicoherent :=
  SheafOfModules.isQuasicoherent_unit.{u, u, u} (R := Y.ringCatSheaf)

private local instance unit_invertible (Y : Scheme.{u}) :
    (SheafOfModules.unit Y.ringCatSheaf).IsInvertible :=
  SheafOfModules.instIsInvertibleUnit.{u, u, u} (R := Y.ringCatSheaf)

private theorem edge_split {X S : Scheme.{u}} (f : X ⟶ S)
    [hDU : ∀ U : S.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    (e0 : SheafOfModules.unit S.ringCatSheaf ≅
      coherentEdgeCohomology.{u, w} f (SheafOfModules.unit X.ringCatSheaf) 0)
    (hsplit : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
      Nonempty ((@Functor.mapDerivedCategory.{w, w, u, u, u + 1, u + 1}
        (SheafOfModules.{u} (moduleRings S.toRingedSpace))
        SheafOfModules.instCategory (curveEdge_schemeAbelian S) (hD S)
        (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))
        SheafOfModules.instCategory (curveEdge_overAbelian S U) (hDU U)
        (SheafOfModules.overFunctor.{u} (moduleRings S.toRingedSpace) U)
        (curveEdge_overAdditive S U) (curveEdge_overLimits S U) (curveEdge_overColimits S U)).obj
          (derivedStructureImage.{u, w} f) ≅
        (DerivedCategory.singleFunctor.{w, u, u + 1}
          (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) 0).obj
            (SheafOfModules.unit ((moduleRings S.toRingedSpace).over U)) ⊞
        ((DerivedCategory.singleFunctor.{w, u, u + 1}
          (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) 0).obj
            ((derivedStructureH1.{u, w} f).over U))⟦(-1 : ℤ)⟧)) :
    ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ Nonempty
      ((schemeOpenRestriction S U).mapDerivedCategory.obj (derivedStructureImage.{u, w} f) ≅
        (DerivedCategory.singleFunctor.{w, u, u + 1}
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) 0).obj
          ((schemeOpenRestriction S U).obj
            (coherentEdgeCohomology.{u, w} f (SheafOfModules.unit X.ringCatSheaf) 0)) ⊞
        (DerivedCategory.singleFunctor.{w, u, u + 1}
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) 1).obj
          ((schemeOpenRestriction S U).obj (derivedStructureH1.{u, w} f))) := by
  let (Y : Scheme.{u}) : Abelian
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) := inferInstance
  let (U : S.Opens) : Abelian
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) := inferInstance
  let (U : S.Opens) : HasColimits
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) := inferInstance
  intro s
  obtain ⟨U, hs, ⟨e⟩⟩ := hsplit s
  let R := SheafOfModules.overFunctor.{u} (moduleRings S.toRingedSpace) U
  let F := Equivalence.functor
    (C := SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))
    (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
    (Scheme.Modules.overEquiv U)
  have : F.Additive := Functor.additive_of_preserves_binary_products _
  let D := Functor.mapDerivedCategory.{w, w, u, u, u + 1, u + 1} F
  have : D.Additive := inferInstance
  have : PreservesFiniteBiproducts D := inferInstance
  have := preservesBinaryBiproducts_of_preservesBiproducts D
  let K := derivedStructureImage.{u, w} f
  let M := (derivedStructureH1.{u, w} f).over U
  let O := SheafOfModules.unit ((moduleRings S.toRingedSpace).over U)
  let H := coherentEdgeCohomology.{u, w} f (SheafOfModules.unit X.ringCatSheaf) 0
  let A := SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)
  let B := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)
  let i0 := DerivedCategory.singleFunctor.{w, u, u + 1} A 0
  let j0 := DerivedCategory.singleFunctor.{w, u, u + 1} B 0
  let j1 := DerivedCategory.singleFunctor.{w, u, u + 1} B 1
  let a : F.obj O ≅ (schemeOpenRestriction S U).obj H := F.mapIso (R.mapIso e0)
  let c : (schemeOpenRestriction S U).mapDerivedCategory.obj K ≅
      D.obj (R.mapDerivedCategory.obj K) :=
    (@Functor.mapDerivedCategoryCompIso _ _ _ _ _ _ _ _ _
      (inferInstance : HasDerivedCategory.{w}
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)))
      (inferInstance : HasDerivedCategory.{w} A)
      (inferInstance : HasDerivedCategory.{w} B) R F
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance).app K
  let d0 : D.obj (i0.obj O) ≅ j0.obj (F.obj O) :=
    (Functor.mapDerivedCategorySingleFunctor.{w, w, u, u, u + 1, u + 1} F 0).app O
  let d1 : D.obj ((i0.obj M)⟦(-1 : ℤ)⟧) ≅ j1.obj (F.obj M) :=
    (D.commShiftIso (-1)).app (i0.obj M) ≪≫
      (shiftFunctor (DerivedCategory.{w, u, u + 1} B) (-1)).mapIso
        ((Functor.mapDerivedCategorySingleFunctor.{w, w, u, u, u + 1, u + 1} F 0).app M) ≪≫
      (((DerivedCategory.singleFunctors.{w, u, u + 1} B).shiftIso
        (-1) 1 0 (by omega)).app (F.obj M))
  refine ⟨U, hs, ⟨c ≪≫ D.mapIso e ≪≫ D.mapBiprod _ _ ≪≫
    biprod.mapIso (d0 ≪≫ j0.mapIso a) d1⟩⟩

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem edge_delta_isIso {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f] [Flat f] (T : Scheme.{u}) (g : T ⟶ S) :
    IsIso (coherentEdgeDelta.{u, w} f (SheafOfModules.unit X.ringCatSheaf) g) := by
  let : ∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (tensorPullback k).Additive :=
    fun {_ _} k ↦ (Classical.choose exists_derivedPullbackComposition.{u, w}) k
  let G := SheafOfModules.unit X.ringCatSheaf
  let : G.IsInvertible := unit_invertible X
  let a := pullback.fst f g
  let p := pullback.snd f g
  let ε := (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition.{u, w})) a
  let c : (derivedPullback.{u, w} a).obj
      ((DerivedCategory.singleFunctor.{w, u, u + 1}
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ⟶
      (DerivedCategory.singleFunctor.{w, u, u + 1}
        (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) 0).obj
        ((tensorPullback a).obj G) :=
    ε.app ((HomotopyCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (tensorPullback a) (ComplexShape.up ℤ) 0).hom.app G))
  have hc : IsDerivedModulePullbackComparison a G c := by
    refine ⟨ε, ?_, rfl⟩
    exact (Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w}))) a
  have : IsIso c := isIso_modulePullbackComparison_of_isFlatOver_identity a G
    (isFlatOver_of_isInvertible (𝟙 X) G) c hc
  have : IsIso (schemeDerivedBaseChangeMap f p g a pullback.condition
      ((DerivedCategory.singleFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G)) :=
    isIso_derivedBaseChange_of_flat_invertible f g a p (IsPullback.of_hasPullback f g) G
  unfold coherentEdgeDelta topDegreeTensorBaseChange singleDegreeBaseChangeComposite
  change IsIso (schemeDerivedBaseChangeMap f p g a pullback.condition
    ((DerivedCategory.singleFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ≫
        (schemeDerivedDirectImage p).map c)
  infer_instance

/-- The affine Leray comparisons attached to the split structural direct image.
Source: Stacks Project, curves.tex, Tag 0GKA, and cohomology.tex, Tags 0ATM and 01F2.
(blueprint: new-curve-split-affine-coherent-edge)

Proof: The structural H0 unit identifies the zeroth cohomology with the unit module,
so that it is finite locally free. Transport the splitting from the localized open
site to the open subscheme through the exact module equivalence. The shifted single
in degree zero is the single in degree one. Flatness of the unit module and relative
flat base change make the canonical tensor counit and base-change composite invertible.
The coherent affine edge theorem now gives simultaneous linear equivalences and their
restriction identity; retain precisely those two clauses. -/
theorem exists_curve_coherentEdge {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f] [Flat f]
    [hDU : ∀ U : S.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    [SheafOfModules.IsFiniteLocallyFree (derivedStructureH1.{u, w} f)]
    (hzero : IsIso ((DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).map
      (derivedStructureUnit.{u, w} f)))
    (hsplit : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
      Nonempty ((@Functor.mapDerivedCategory.{w, w, u, u, u + 1, u + 1}
        (SheafOfModules.{u} (moduleRings S.toRingedSpace))
        SheafOfModules.instCategory (curveEdge_schemeAbelian S) (hD S)
        (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))
        SheafOfModules.instCategory (curveEdge_overAbelian S U) (hDU U)
        (SheafOfModules.overFunctor.{u} (moduleRings S.toRingedSpace) U)
        (curveEdge_overAdditive S U) (curveEdge_overLimits S U) (curveEdge_overColimits S U)).obj
          (derivedStructureImage.{u, w} f) ≅
        (DerivedCategory.singleFunctor.{w, u, u + 1}
          (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) 0).obj
            (SheafOfModules.unit ((moduleRings S.toRingedSpace).over U)) ⊞
        ((DerivedCategory.singleFunctor.{w, u, u + 1}
          (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) 0).obj
            ((derivedStructureH1.{u, w} f).over U))⟦(-1 : ℤ)⟧)) :
    ∃ e : ∀ (T : Scheme.{u}) (g : T ⟶ S) (_ : IsAffine T),
        coherentEdgeH.{u} f (SheafOfModules.unit X.ringCatSheaf) g ≃ₗ[Γ(T, ⊤)]
          (RingedSpace.globalSectionsFunctor T.toRingedSpace).obj
            ((tensorPullback g).obj
              (coherentEdgeCohomology.{u, w} f (SheafOfModules.unit X.ringCatSheaf) 1)),
      ∀ (T T' : Scheme.{u}) (g : T ⟶ S) (h : T' ⟶ T)
        (hT : IsAffine T) (hT' : IsAffine T')
        (x : coherentEdgeH.{u} f (SheafOfModules.unit X.ringCatSheaf) g),
        e T' (h ≫ g) hT' (coherentEdgePullback.{u} f
          (SheafOfModules.unit X.ringCatSheaf) g h x) =
          coherentEdgeRho.{u} g h
            (coherentEdgeCohomology.{u, w} f (SheafOfModules.unit X.ringCatSheaf) 1)
              (e T g hT x) := by
  let : IsIso ((DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).map
      (derivedStructureUnit.{u, w} f)) := hzero
  have : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
    unit_quasicoherent X
  have : (SheafOfModules.unit S.ringCatSheaf).IsInvertible :=
    unit_invertible S
  have : (SheafOfModules.unit S.ringCatSheaf).IsFiniteLocallyFree := inferInstance
  let e0 : SheafOfModules.unit S.ringCatSheaf ≅
      coherentEdgeCohomology.{u, w} f (SheafOfModules.unit X.ringCatSheaf) 0 :=
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).app _).symm ≪≫
      asIso ((DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).map (derivedStructureUnit.{u, w} f))
  have : SheafOfModules.IsFiniteLocallyFree
      (coherentEdgeCohomology.{u, w} f (SheafOfModules.unit X.ringCatSheaf) 0) :=
    SheafOfModules.IsFiniteLocallyFree.of_iso e0
  have : SheafOfModules.IsFiniteLocallyFree
      (coherentEdgeCohomology.{u, w} f (SheafOfModules.unit X.ringCatSheaf) 1) := by
    change SheafOfModules.IsFiniteLocallyFree (derivedStructureH1.{u, w} f)
    infer_instance
  obtain ⟨τ, _, _, β, _, e, _, he⟩ := coherent_affine_base_change_edge_naturality.{u, w}
    f (SheafOfModules.unit X.ringCatSheaf) (edge_split f e0 hsplit) (edge_delta_isIso f)
  exact ⟨e, he⟩

end
end AlgebraicGeometry
