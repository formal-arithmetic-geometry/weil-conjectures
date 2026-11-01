/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
public import WeilConjectures.AlgebraicGeometry.FiniteConstantModel.FiniteConstantModelResolutionSupplement
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.GaloisCategories
public import WeilConjectures.CategoryTheory.SetFunctorAut.AutProfinite
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.Algebra.Category.MonCat.FilteredColimits
public import WeilConjectures.AlgebraicGeometry.ProEtaleObjectPullbackRestriction
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import WeilConjectures.CategoryTheory.Sites.UnitHomEval
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# The pointed connected tower for an integral lisse morphism

Source: latest blueprint, part-six-operations/sec-reduction-finite-coefficients/
sec-constructible-sheaves-with-field-coefficients/sk-lem-coefficient-heart/
sk-lem-coefficient-heart.proof.md, proof (1), paragraph beginning "The reductions",
through the completed-fibre matrix.
(blueprint: lem-sfb-coefficient-heart-connected-tower).

The witnesses below retain the quotient maps, etale origins, pointed sections and
all reduction compatibilities. The constant realization is the existing scalar
extension `FiniteConstantModel.modelFunctor`, including on morphisms.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.ProEtale.CoefficientHeartTower

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- Native modules over the pulled-back continuous condensed coefficient ring.
Source: blueprint proof (1), integral lattices
(blueprint: lem-sfb-coefficient-heart-connected-tower). -/
abbrev Modules (X : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (Profinite.continuousCoefficientRingObj A) X)

/-- The canonical regular-module comparison for the existing scalar realization.
Every comparison is the identity on regular actions or the scalar-extension unit.
Source: blueprint proof (1), completed constant realization
(blueprint: lem-sfb-coefficient-heart-connected-tower). -/
def modelRegularIso (X : Scheme.{u}) :
    (FiniteConstantModel.modelFunctor A X).obj (ModuleCat.of A (ULift.{u + 1} A)) ≅
      Mod.regular (condensedRingObj (Profinite.continuousCoefficientRingObj A) X) := by
  let R := AddCommGrpCat.of (ULift.{u + 1} A)
  let F := constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  let Λ := Profinite.continuousCoefficientRingObj A
  let e : (FiniteConstantModel.scalarModules A).obj
      (ModuleCat.of A (ULift.{u + 1} A)) ≅ Mod.regular R :=
    Mod.isoMk (Iso.refl _) (by
      apply AddCommGrpCat.hom_ext_toIntLinearMap
      apply TensorProduct.ext'
      intro a b
      rfl)
  let eF : (F.mapMod R).obj (Mod.regular R) ≅ Mod.regular (F.obj R) :=
    Mod.isoMk (Iso.refl _) (by simp)
  let eX : ((upperStarFromPoint X).mapMod Λ).obj (Mod.regular Λ) ≅
      Mod.regular (condensedRingObj Λ X) :=
    Mod.isoMk (Iso.refl _) (by simp)
  exact ((upperStarFromPoint X).mapMod Λ).mapIso
    ((Mod.extendScalars (FiniteConstantModel.scalarToContinuous A)).mapIso
      ((F.mapMod R).mapIso e ≪≫ eF) ≪≫
        Mod.regularExtensionIso (FiniteConstantModel.scalarToContinuous A)) ≪≫ eX

/-- Scalar multiplication on a native module, using the canonical scalar endomorphism
of the tensor unit and its left unitor. Source: blueprint proof (1), scalar quotients
(blueprint: lem-sfb-coefficient-heart-connected-tower). -/
def scalar (X : Scheme.{u}) (M : Modules A X) (a : A) : M ⟶ M :=
  (λ_ M).inv ≫
    ((modelRegularIso A X).inv ≫ (FiniteConstantModel.modelFunctor A X).map
      (ModuleCat.ofHom (a • LinearMap.id)) ≫ (modelRegularIso A X).hom) ▷ M ≫
    (λ_ M).hom

/-- The section `1 tensor p` of the actual scalar-extension realization, on any
pro-etale object. Source: blueprint proof (1), pointed finite trivializations
(blueprint: lem-sfb-coefficient-heart-connected-tower). -/
def generator (X : Scheme.{u}) (P : ModuleCat.{u + 1} A) (U : X.ProEt) (p : P) :
    ((FiniteConstantModel.modelFunctor A X).obj P).X.obj.obj (op U) :=
  Sheaf.unitHomEval.{u + 1, u, u + 1} U
    (MonObj.one (X := condensedRingObj (Profinite.continuousCoefficientRingObj A) X) ≫
      (modelRegularIso A X).inv.hom ≫
      ((FiniteConstantModel.modelFunctor A X).map
        (ModuleCat.ofHom
          { toFun := fun a : ULift.{u + 1} A ↦ a.down • p
            map_add' := fun a b ↦ add_smul a.down b.down p
            map_smul' := fun a b ↦ mul_smul a b.down p })).hom)

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]

/-- Underlying abelian pullback along a site object, with the canonical inverse
coefficient map and the canonical localization comparison. No arbitrary underlying
isomorphism is chosen. Source: blueprint proof (1), slice restriction
(blueprint: lem-sfb-coefficient-heart-connected-tower). -/
def restrictionIso (U : X.ProEt) (M : Modules A X) :
    ((CondensedRing.upperStar (Profinite.continuousCoefficientRingObj A) U.hom).obj M).X ≅
      (localizationRestriction Ab.{u + 1} U.hom U.prop).obj M.X :=
  (Mod.forget _).mapIso ((Mod.extendScalarsIsoComapInv
      (condensedPullbackHom (Profinite.continuousCoefficientRingObj A) U.hom)).app
        (((upperStar Ab.{u + 1} U.hom).mapMod _).obj M)) ≪≫
    (upperStarIsoSheafPushforward Ab.{u + 1} U.hom U.prop).app M.X

/-- Evaluation of the canonical restriction comparison, using the published
section formula to identify its codomain without unfolding the localization functor.
Source: blueprint proof (1), slice restriction; the section formula of
`proEtaleObjectPullbackRestriction`
(blueprint: lem-sfb-coefficient-heart-connected-tower). -/
def restrictionAt (U : X.ProEt) (M : Modules A X) (Z : U.left.ProEt) :
    ((CondensedRing.upperStar (Profinite.continuousCoefficientRingObj A) U.hom).obj
      M).X.obj.obj (op Z) ⟶
        M.X.obj.obj (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj Z)) :=
  (restrictionIso A U M).hom.hom.app (op Z) ≫
    eqToHom ((proEtaleObjectPullbackRestriction X U).2.2.2 M.X Z)

/-- The quotient projection, expressed as one bundled additive map on a scalar
realization. Bundling avoids repeated computation of the realization's carrier.
Every factor is the specified comparison, native pullback, or restriction map.
Source: blueprint proof (1), finite projections of the completed realization
(blueprint: lem-sfb-coefficient-heart-connected-tower). -/
def realizationProjection (U : X.ProEt) (M N : Modules A X)
    (P : ModuleCat.{u + 1} A)
    (e : (CondensedRing.upperStar (Profinite.continuousCoefficientRingObj A) U.hom).obj M ≅
      (FiniteConstantModel.modelFunctor A U.left).obj P)
    (q : M ⟶ N) (Z : U.left.ProEt) :
    ((FiniteConstantModel.modelFunctor A U.left).obj P).X.obj.obj (op Z) ⟶
      N.X.obj.obj (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj Z)) :=
  e.inv.hom.hom.app (op Z) ≫
    ((CondensedRing.upperStar (Profinite.continuousCoefficientRingObj A) U.hom).map
      q).hom.hom.app (op Z) ≫ restrictionAt A U N Z

/-- One finite projection has the specified values on the pure generators of
an existing scalar realization. Keeping its scalar module abstract avoids unfolding
an inverse-limit carrier while forming this predicate.
Source: blueprint proof (1), normalization of each finite projection
(blueprint: lem-sfb-coefficient-heart-connected-tower). -/
def NormalizedProjection (U : X.ProEt) (M N : Modules A X)
    (P : ModuleCat.{u + 1} A)
    (e : (CondensedRing.upperStar (Profinite.continuousCoefficientRingObj A) U.hom).obj M ≅
      (FiniteConstantModel.modelFunctor A U.left).obj P)
    (q : M ⟶ N) (V : X.Etale)
    (r : ∀ Z : U.left.ProEt,
      (MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj Z ⟶
        (Scheme.toProEt X).obj V)
    (sigma : (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1}).obj P ⟶
      N.X.obj.obj (op ((Scheme.toProEt X).obj V))) : Prop :=
  ∀ (Z : U.left.ProEt) (p : P),
    realizationProjection A U M N P e q Z (generator A U.left P Z p) =
      N.X.obj.map (r Z).op (sigma p)

end AlgebraicGeometry.ProEtale.CoefficientHeartTower
