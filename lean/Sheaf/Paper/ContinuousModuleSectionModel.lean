/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.Paper.ProfiniteCoefficientLinearization
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.Topology.ContinuousMapCondensedRing
public import Sheaf.Paper.CartesianCoefficients

/-! # Section-normalized continuous module realizations

Source: Bhatt--Scholze, Lemma 4.2.12 and Proposition 6.8.4(1), continuous-module
interpretation (blueprint: def-sfb-continuous-module-section-model).

The object is characterized on every profinite set. Its scheme charts are normalized
by the point adjunction, and hence describe the actual inverse image from the point.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.ContinuousModule

/-- Bundle the existing continuous-function ring, retaining its recorded multiplication.
Source: BS Definition 6.8.1 (blueprint: def-sfb-continuous-module-section-model). -/
def ring (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
  { X := Profinite.continuousMapRingObjOfUniverse A
    mon := Profinite.continuousMapRingObjOfUniverseMonObj A }

/-- Commutativity of the same pointwise multiplication.
Source: BS Definition 6.8.1 (blueprint: def-sfb-continuous-module-section-model). -/
instance ring_comm (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    IsCommMonObj (ring A).X :=
  Profinite.isCommMonObj_continuousMapRingObjOfUniverse A

/-- The existing internal coefficient-module category on the point.
Source: BS Lemma 4.2.12 (blueprint: def-sfb-continuous-module-section-model). -/
abbrev Modules (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :=
  Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) (ring A).X

/-- The existing internal coefficient-module category on a scheme.
Source: BS Definition 6.8.1 (blueprint: def-sfb-continuous-module-section-model). -/
abbrev SchemeModules (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (X : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj (ring A).X X)

/-- Actual monoidal inverse image of an internal module from the point.
Source: BS Lemma 4.2.12 (blueprint: def-sfb-continuous-module-section-model). -/
abbrev pull (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (X : Scheme.{u}) : Modules A ⥤ SchemeModules A X :=
  (upperStarFromPoint X).mapMod (ring A).X

/-- All continuous additive sections on profinite sets, with precomposition restrictions.
Source: BS Lemma 4.2.12 (blueprint: def-sfb-continuous-module-section-model). -/
def pointFunctions (V : Type u) [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] : Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1} where
  obj S := AddCommGrpCat.of (ULift.{u + 1} C(S.unop, V))
  map f := AddCommGrpCat.ofHom
    { toFun := fun v ↦ ULift.up (v.down.comp f.unop.hom.hom)
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- All continuous additive sections on the small pro-etale site.
Source: BS Lemma 4.2.12 (blueprint: def-sfb-continuous-module-section-model). -/
def schemeFunctions (V : Type u) [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] (X : Scheme.{u}) : X.ProEtᵒᵖ ⥤ Ab.{u + 1} where
  obj U := AddCommGrpCat.of (ULift.{u + 1} C(U.unop.left, V))
  map f := AddCommGrpCat.ofHom
    { toFun := fun v ↦ ULift.up (v.down.comp f.unop.left.base.hom)
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The canonical point-adjunction unit, evaluated on a profinite test object.
Source: BS Lemma 4.2.12 (blueprint: def-sfb-continuous-module-section-model). -/
def testUnit {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (M : Modules A) (X : Scheme.{u}) (S : Profinite.{u}) :
    M.X.obj.obj (op S) ⟶
      ((pull A X).obj M).X.obj.obj (op ((profiniteToProEtOf X).obj S)) :=
  ((pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).unit.app M.X).hom.app (op S)

/-- A presentation of the actual continuous module and its actual scheme inverse images.
Scalar and restriction formulas specify the whole module, rather than only its points.
The test-unit equation fixes the scheme charts by the point adjunction.
Source: BS Lemma 4.2.12, Definition 6.8.1 and Proposition 6.8.4(1)
(blueprint: def-sfb-continuous-module-section-model). -/
structure Model (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (V : Type u) [AddCommGroup V] [Module A V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] where
  object : Modules A
  point : object.X.obj ≅ pointFunctions V
  scalar (S : Profinite.{u})
      (r : (InternalAbelianSheafModule.sectionRings
        (coherentTopology Profinite.{u}) (ring A).X).obj (op S))
      (v : ((InternalAbelianSheafModule.sectionModuleFunctor
        (coherentTopology Profinite.{u}) (ring A).X).obj object).val.obj (op S))
      (s : S) :
    (point.hom.app (op S) (r • v)).down s = r.down s • (point.hom.app (op S) v).down s
  scheme (X : Scheme.{u}) : ((pull A X).obj object).X.obj ≅ schemeFunctions V X
  normalization (X : Scheme.{u}) (S : Profinite.{u})
      (v : object.X.obj.obj (op S)) (x : coefficientParameter X S) :
    ((scheme X).hom.app (op ((profiniteToProEtOf X).obj S)) (testUnit object X S v)).down x =
      (point.hom.app (op S) v).down (profiniteTestProjection X S x)

/-- The underlying object of the existing module inverse image from the point.
Source: BS Lemma 4.2.12 (blueprint: def-sfb-continuous-module-section-model). -/
def pointUnderlying
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (M : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) (X : Scheme.{u}) :
    (((upperStarFromPoint X).mapMod Λ).obj M).X ≅
      (upperStarFromPoint X).obj M.X := Iso.refl _

/-- The Cartesian lift keeps the underlying abelian inverse image literally.
Source: BS Lemma 4.2.12 (blueprint: def-sfb-continuous-module-section-model). -/
def liftUnderlying
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    ((cartesianCoefficientLift Λ f).obj M).X ≅
      (upperStar Ab.{u + 1} f).obj M.X := Iso.refl _

/-- Composition comparison on the original underlying abelian sheaves.
Source: BS Lemma 4.2.12 (blueprint: def-sfb-continuous-module-section-model). -/
def pointComp {X Y : Scheme.{u}} (f : Y ⟶ X)
    (M : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :
    (upperStar Ab.{u + 1} f).obj ((upperStarFromPoint X).obj M) ≅
      (upperStarFromPoint Y).obj M := (upperStarFromPointComp f).app M

/-- Canonical underlying comparison for pulling a continuous module along a scheme map.
This is extension along the Cartesian coefficient isomorphism followed by p-composition.
Source: BS Lemma 4.2.12 (blueprint: def-sfb-continuous-module-section-model). -/
def pullIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (M : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ)
    {X Y : Scheme.{u}} (f : Y ⟶ X) :
    ((cartesianCoefficientLift Λ f).obj (((upperStarFromPoint X).mapMod Λ).obj M)).X ≅
      (((upperStarFromPoint Y).mapMod Λ).obj M).X :=
  liftUnderlying Λ f (((upperStarFromPoint X).mapMod Λ).obj M) ≪≫
    (upperStar Ab.{u + 1} f).mapIso (pointUnderlying Λ M X) ≪≫
      pointComp f M.X ≪≫ (pointUnderlying Λ M Y).symm

/-- A map of continuous realizations is specified by postcomposition on all sections.
Source: BS Proposition 6.8.4(1), morphisms
(blueprint: def-sfb-continuous-module-section-model). -/
def RepresentsMap {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    {V W : Type u} [AddCommGroup V] [Module A V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [AddCommGroup W] [Module A W] [TopologicalSpace W]
    [IsTopologicalAddGroup W] (P : Model A V) (Q : Model A W)
    (f : V →ₗ[A] W) (g : P.object ⟶ Q.object) : Prop :=
  ∀ (S : Profinite.{u}) (v : P.object.X.obj.obj (op S)) (s : S),
    (Q.point.hom.app (op S) (g.hom.hom.app (op S) v)).down s =
      f ((P.point.hom.app (op S) v).down s)

end AlgebraicGeometry.ProEtale.ContinuousModule
