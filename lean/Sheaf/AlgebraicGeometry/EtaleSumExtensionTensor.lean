/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.SixFunctors.Etale.Derived.Perfect.SitePerfect

/-!
# Tensor compatibility for étale sum extension

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/
thm-asd-smooth-tensor.md, proof paragraph 3 (blueprint: lem-asd-etale-sum-extension-tensor).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

universe u u'

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

-- Prefer the direct sheaf-colimit construction when elaborating the derived adjunction.
attribute [local instance 2000] Sheaf.instHasColimitsOfShape

/-- The canonical tensor comparison for exact, termwise derived inverse image. Transport
`leftDerivedUpperStarTensorIso` through `leftDerivedUpperStarIsoMapDerivedCategory` in both
arguments and in the value. Source: Stacks, Tag 0G7E and the tensor comparison in
lem-weil-pbc-ringed-topoi-derived-tensor-pullback
(blueprint: lem-asd-etale-sum-extension-tensor). -/
noncomputable def etaleSumExtensionTensorPullbackIso
    (A : Type (u + 1)) [CommRing A] {V T : Scheme.{u}} (v : V ⟶ T)
    (B C : DerivedCategoryModule A T) :
    ((derivedTensor (ModuleCat.{u + 1} A) V).obj
        ((upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj B)).obj
        ((upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj C) ≅
      (upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj
        (((derivedTensor (ModuleCat.{u + 1} A) T).obj B).obj C) :=
  ((derivedTensor (ModuleCat.{u + 1} A) V).mapIso
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) v).app B).symm).app
        ((upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj C) ≪≫
    ((derivedTensor (ModuleCat.{u + 1} A) V).obj _).mapIso
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) v).app C).symm ≪≫
    (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) v B C).symm ≪≫
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) v).app _

/-- The canonical comparison `v_!(v^*B ⊗ᴸ M) ⟶ B ⊗ᴸ v_!M`. It is the adjoint transpose
of `1 ⊗ unit`, followed by the canonical tensor-pullback comparison. On sum-extension
sections its inverse sends `b ⊗ (s,m)` to `(s,s^*b ⊗ m)`.
Source: Stacks Project, Tag 0GKF (blueprint: lem-asd-etale-sum-extension-tensor). -/
noncomputable def etaleSumExtensionTensorComparison
    (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (v : V ⟶ T)
    [Etale v] [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    (B : DerivedCategoryModule A T) (M : DerivedCategoryModule A V) :
    (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory.obj
        (((derivedTensor (ModuleCat.{u + 1} A) V).obj
          ((upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj B)).obj M) ⟶
      ((derivedTensor (ModuleCat.{u + 1} A) T).obj B).obj
        ((etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory.obj M) :=
  (((etaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategoryAdjunction).homEquiv _ _).symm
    (((derivedTensor (ModuleCat.{u + 1} A) V).obj
        ((upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj B)).map
        (((etaleLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategoryAdjunction).unit.app M) ≫
      (etaleSumExtensionTensorPullbackIso A v B
        ((etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory.obj M)).hom)

-- Projection invertibility is invariant under monoidal transport of the right adjoint.
private theorem isIso_projectionMap_transport
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalClosed C] [MonoidalClosed D]
    {F G : C ⥤ D} [F.Monoidal] (e : F ≅ G) {L : D ⥤ C}
    (adjF : L ⊣ F) (adjG : L ⊣ G) (B : C)
    [IsIso (Functor.Monoidal.projectionMap adjF B)] :
    letI := Functor.Monoidal.transport e
    IsIso (Functor.Monoidal.projectionMap adjG B) := by
  let := Functor.Monoidal.transport e
  have : NatTrans.IsMonoidal e.hom := Functor.Monoidal.natTransIsMonoidal_of_transport e
  have : NatTrans.IsMonoidal e.symm.hom :=
    inferInstanceAs (NatTrans.IsMonoidal e.inv)
  have := Functor.Monoidal.isIso_ihomComparison_of_isIso_projectionMap adjF B
  have := Functor.LaxMonoidal.isIso_ihomComparison_of_iso e.symm B
  exact Functor.Monoidal.isIso_projectionMap_of_isIso_ihomComparison adjG B

-- The lax tensorator is the inverse of the specified oplax tensor comparison.
private theorem leftDerivedUpperStar_mu_eq
    (D : Type u') [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
    [SymmetricCategory D] [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D]
    {V T : Scheme.{u}} (v : V ⟶ T) [(upperStar D v).PreservesFlat]
    (K N : _root_.DerivedCategory (Sheaf T.smallEtaleTopology D)) :
    let _ := leftDerivedUpperStarMonoidal D v
    Functor.LaxMonoidal.μ (upperStar D v).leftDerivedFunctor K N =
      (leftDerivedUpperStarTensorIso D v K N).inv := by
  let := leftDerivedUpperStarMonoidal D v
  apply (cancel_mono (leftDerivedUpperStarTensorIso D v K N).hom).1
  rw [Iso.inv_hom_id]
  exact Functor.Monoidal.μ_δ (upperStar D v).leftDerivedFunctor K N

private theorem exactUpperStar_mu_eq
    (D : Type u') [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
    [SymmetricCategory D] [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D]
    {V T : Scheme.{u}} (v : V ⟶ T) [(upperStar D v).PreservesFlat]
    (K N : _root_.DerivedCategory (Sheaf T.smallEtaleTopology D)) :
    let _ := leftDerivedUpperStarMonoidal D v
    let e := leftDerivedUpperStarIsoMapDerivedCategory D v
    let _ := Functor.Monoidal.transport e
    Functor.LaxMonoidal.μ (upperStar D v).mapDerivedCategory K N =
      (((derivedTensor D V).mapIso (e.app K).symm).app
          ((upperStar D v).mapDerivedCategory.obj N) ≪≫
        ((derivedTensor D V).obj _).mapIso (e.app N).symm ≪≫
        (leftDerivedUpperStarTensorIso D v K N).symm ≪≫ e.app _).hom := by
  let := leftDerivedUpperStarMonoidal D v
  have hLμ := leftDerivedUpperStar_mu_eq D v
  let e := leftDerivedUpperStarIsoMapDerivedCategory D v
  let := Functor.Monoidal.transport e
  dsimp only
  rw [Functor.Monoidal.transport_μ, hLμ]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom,
    derivedTensor_map_app, derivedTensor_obj_map, MonoidalCategory.tensorHom_def, Category.assoc]
  rfl

-- Keep exact functors and adjunctions folded during the transport calculation.
attribute [local irreducible] Functor.mapDerivedCategory Adjunction.mapDerivedCategoryAdjunction
    leftDerivedUpperStarIsoMapDerivedCategory etaleLowerShriek upperStar

private theorem exactUpperStar_projection
    (D : Type u') [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
    [SymmetricCategory D] [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D]
    [HasSmallSiteSheafify D]
    {V T : Scheme.{u}} (v : V ⟶ T) [Etale v] [(upperStar D v).PreservesFlat]
    [∀ N : D, PreservesFilteredColimitsOfSize.{u, u + 1} (tensorLeft N)]
    [(V.smallEtaleTopology.W (A := D)).IsMonoidal]
    [(T.smallEtaleTopology.W (A := D)).IsMonoidal]
    (K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology D)) :
    let _ := leftDerivedUpperStarMonoidal D v
    let e := leftDerivedUpperStarIsoMapDerivedCategory D v
    let _ := Functor.Monoidal.transport e
    IsIso (Functor.Monoidal.projectionMap
      ((etaleLowerShriekUpperStarAdjunction D v inferInstance).mapDerivedCategoryAdjunction)
      K) := by
  let := leftDerivedUpperStarMonoidal D v
  have := isIso_projectionMap_derivedEtaleLowerShriek (A := D) v K
  exact isIso_projectionMap_transport (leftDerivedUpperStarIsoMapDerivedCategory D v)
    (derivedEtaleLowerShriekLeftDerivedUpperStarAdjunction (A := D) v)
    ((etaleLowerShriekUpperStarAdjunction D v inferInstance).mapDerivedCategoryAdjunction) K

private theorem projection_formula
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    {G : C ⥤ D} [G.Monoidal] {L : D ⥤ C} (adj : L ⊣ G)
    (θ : ∀ X Y : C, G.obj X ⊗ G.obj Y ≅ G.obj (X ⊗ Y))
    (hθ : ∀ X Y, Functor.LaxMonoidal.μ G X Y = (θ X Y).hom)
    (B : C) (M : D) [IsIso (Functor.Monoidal.projectionMap adj B)] :
    IsIso ((adj.homEquiv _ _).symm
      (G.obj B ◁ adj.unit.app M ≫ (θ B (L.obj M)).hom)) ∧
    ∀ N : C,
      (adj.homEquiv _ _).symm
          (G.obj B ◁ adj.unit.app (G.obj N) ≫ (θ B (L.obj (G.obj N))).hom) ≫
          B ◁ adj.counit.app N =
        L.map (θ B N).hom ≫ adj.counit.app (B ⊗ N) := by
  have he (P : D) : (adj.homEquiv _ _).symm
      (G.obj B ◁ adj.unit.app P ≫ (θ B (L.obj P)).hom) =
      (Functor.Monoidal.projectionMap adj B).app P := by
    simp only [Adjunction.homEquiv_counit, Functor.Monoidal.projectionMap, hθ]
  constructor
  · rw [he]
    infer_instance
  · intro N
    rw [he, ← hθ]
    simp only [Functor.Monoidal.projectionMap, Category.assoc]
    rw [← adj.counit_naturality, ← Functor.map_comp_assoc]
    congr 1
    rw [Category.assoc, ← Functor.LaxMonoidal.μ_natural_right,
      ← MonoidalCategory.whiskerLeft_comp_assoc, adj.right_triangle_components,
      MonoidalCategory.whiskerLeft_id, Category.id_comp]
    rfl

-- Calculate over an abstract coefficient category before specializing to modules.
private theorem exactUpperStar_formula
    (D : Type u') [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
    [SymmetricCategory D] [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D]
    [HasSmallSiteSheafify D]
    {V T : Scheme.{u}} (v : V ⟶ T) [Etale v] [(upperStar D v).PreservesFlat]
    [∀ N : D, PreservesFilteredColimitsOfSize.{u, u + 1} (tensorLeft N)]
    [(V.smallEtaleTopology.W (A := D)).IsMonoidal]
    [(T.smallEtaleTopology.W (A := D)).IsMonoidal]
    (B : _root_.DerivedCategory (Sheaf T.smallEtaleTopology D))
    (M : _root_.DerivedCategory (Sheaf V.smallEtaleTopology D)) :
    let e := leftDerivedUpperStarIsoMapDerivedCategory D v
    let θ := fun K N ↦
      ((derivedTensor D V).mapIso (e.app K).symm).app
          ((upperStar D v).mapDerivedCategory.obj N) ≪≫
        ((derivedTensor D V).obj _).mapIso (e.app N).symm ≪≫
        (leftDerivedUpperStarTensorIso D v K N).symm ≪≫ e.app _
    let adj := (etaleLowerShriekUpperStarAdjunction D v inferInstance).mapDerivedCategoryAdjunction
    IsIso ((adj.homEquiv _ _).symm
      (((derivedTensor D V).obj ((upperStar D v).mapDerivedCategory.obj B)).map
        (adj.unit.app M) ≫
        (θ B ((etaleLowerShriek D v inferInstance).mapDerivedCategory.obj M)).hom)) ∧
    ∀ N : _root_.DerivedCategory (Sheaf T.smallEtaleTopology D),
      (adj.homEquiv _ _).symm
        (((derivedTensor D V).obj ((upperStar D v).mapDerivedCategory.obj B)).map
          (adj.unit.app ((upperStar D v).mapDerivedCategory.obj N)) ≫
          (θ B ((etaleLowerShriek D v inferInstance).mapDerivedCategory.obj
            ((upperStar D v).mapDerivedCategory.obj N))).hom) ≫
        ((derivedTensor D T).obj B).map (adj.counit.app N) =
      (etaleLowerShriek D v inferInstance).mapDerivedCategory.map (θ B N).hom ≫
        adj.counit.app (((derivedTensor D T).obj B).obj N) := by
  let := leftDerivedUpperStarMonoidal D v
  let e := leftDerivedUpperStarIsoMapDerivedCategory D v
  let := Functor.Monoidal.transport e
  have hp := exactUpperStar_projection D v B
  have hμ := exactUpperStar_mu_eq D v
  exact projection_formula
    ((etaleLowerShriekUpperStarAdjunction D v inferInstance).mapDerivedCategoryAdjunction)
    _ hμ B M

/-- Sum extension commutes with arbitrary unbounded derived tensor products, compatibly
with the fold counit. Source: blueprint thm-asd-smooth-tensor, proof paragraph 3;
Stacks Tag 0GKF (blueprint: lem-asd-etale-sum-extension-tensor).

Proof:
1. Equip left derived pullback with `leftDerivedUpperStarMonoidal`, whose oplax tensorator
is `leftDerivedUpperStarTensorIso.hom`. The monoidal inverse identity identifies its lax
tensorator with `leftDerivedUpperStarTensorIso.inv`.
2. Transport this monoidal structure along `leftDerivedUpperStarIsoMapDerivedCategory`.
The transport formula for the lax tensorator is exactly
`etaleSumExtensionTensorPullbackIso.hom`, by the two whiskering formulas for `derivedTensor`.
3. The source library's `isIso_projectionMap_derivedEtaleLowerShriek` proves the projection
formula for sum extension adjoint to left derived pullback. Projection invertibility is
equivalent to invertibility of the right adjoint's internal-hom comparison. That comparison
is preserved by a monoidal natural isomorphism, so the projection map for the exact termwise
derived adjunction is invertible as well. Its component is the specified adjoint transpose.
4. Expand that transpose. Naturality of the counit moves `1 ⊗ counit` inside sum extension;
naturality of the tensorator then combines the unit with pulled-back counit. The right
triangle identity cancels these maps, leaving exactly sum extension of the tensorator
followed by the counit at the tensor product. This is the required fold-counit identity.
All calculations apply to arbitrary objects of the unbounded derived categories.
-/
theorem isIso_etaleSumExtensionTensorComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V T : Scheme.{u}} (v : V ⟶ T)
    [Etale v] [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    [IsNoetherian V] [IsNoetherian T]
    (B : DerivedCategoryModule A T) (M : DerivedCategoryModule A V) :
    IsIso (etaleSumExtensionTensorComparison A v B M) ∧
      ∀ C : DerivedCategoryModule A T,
        etaleSumExtensionTensorComparison A v B
            ((upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj C) ≫
            ((derivedTensor (ModuleCat.{u + 1} A) T).obj B).map
              (((etaleLowerShriekUpperStarAdjunction
                (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategoryAdjunction).counit.app C) =
          (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory.map
            (etaleSumExtensionTensorPullbackIso A v B C).hom ≫
            ((etaleLowerShriekUpperStarAdjunction
              (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategoryAdjunction).counit.app
              (((derivedTensor (ModuleCat.{u + 1} A) T).obj B).obj C) := by
  exact exactUpperStar_formula (ModuleCat.{u + 1} A) v B M

end AlgebraicGeometry.Etale
