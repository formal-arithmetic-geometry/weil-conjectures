/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.Paper.CanonicalTateOrdinaryNaturality
import all Sheaf.Paper.CanonicalTateOrdinaryNaturality
import Sheaf.SecSmoothPurity.CochainCoefficientArrows

/-! # Canonical Tate naturality: ScalarNaturality

Source: current blueprint, def-pur-tate-datum, canonical root-arrow comparisons.
Existing declarations are retained in this compilation subdivision.
(blueprint: def-pur-canonical-tate-scalar-naturality).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u v a b c d
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct ChangeOfRings
namespace WeilConjectures.CanonicalTate
open FrobeniusCoefficientTwists

attribute [local instance 5000] integralTowerHasDerivedCategory scalarReductionTargetDerived
attribute [local irreducible] HasDerivedCategory.standard
  integralPull finitePull rationalPull commonPull
  integralProduct finiteProduct rationalProduct commonProduct
  proEtaleRingModulePullback proEtaleRingModuleAdjunction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
private local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

private theorem scalar_obj
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (X : Scheme.{u}) (M : integralTowerModules l E X) :
    (integralOrdinaryScalar l E L ι X).obj M =
      SheafOfModules.changeOfRings (integralCompletedScalarMap l E L ι X) M := by
  unfold integralOrdinaryScalar
  exact (integralOrdinaryScalarWitness l E L ι X).choose_spec.choose M

private def scalarPresentation
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (X : Scheme.{u}) :
    integralOrdinaryScalar l E L ι X ≅
      CategoryTheory.CochainPullback.extensionFunctor.{u + 1, u + 1, u}
        (integralCompletedScalarMap l E L ι X) :=
  NatIso.ofComponents
    (fun M ↦ eqToIso (scalar_obj l E L ι X M))
    (by
      intro M N f
      have hm : (integralOrdinaryScalar l E L ι X).map f =
          eqToHom (scalar_obj l E L ι X M) ≫
            SheafOfModules.changeOfRingsHom (integralCompletedScalarMap l E L ι X) M f ≫
              eqToHom (scalar_obj l E L ι X N).symm := by
        unfold integralOrdinaryScalar
        exact (integralOrdinaryScalarWitness l E L ι X).choose_spec.choose_spec.choose f
      rw [hm]
      simp [CategoryTheory.CochainPullback.extensionFunctor])


private def scalarAdj
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (X : Scheme.{u}) :
    integralOrdinaryScalar l E L ι X ⊣
      proEtaleRingRestrictScalars (integralCompletedScalarMap l E L ι X) :=
  (CategoryTheory.CochainPullback.extensionAdjunction.{u + 1, u + 1, u}
    (integralCompletedScalarMap l E L ι X)).ofNatIsoLeft
      (scalarPresentation l E L ι X).symm

private theorem scalarAdj_unit
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
    (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ) (x : M.val.obj U) :
    ((scalarAdj l E L ι X).unit.app M).val.app U x =
      integralOrdinaryTensorSection l E L ι X M U 1 x := by
  have hu := (Classical.choose_spec
    (CategoryTheory.CochainPullback.extensionAdjunction_existsUnique
      (integralCompletedScalarMap l E L ι X))).1 M U x
  dsimp only [scalarAdj]
  rw [Adjunction.ofNatIsoLeft_unit]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, scalarPresentation,
    Iso.symm_hom, NatIso.ofComponents_inv_app, eqToIso.inv]
  change (eqToHom (scalar_obj l E L ι X M).symm).val.app U
    (((CategoryTheory.CochainPullback.extensionAdjunction
      (integralCompletedScalarMap l E L ι X)).unit.app M).val.app U x) = _
  erw [hu]
  unfold CategoryTheory.CochainPullback.extensionTmul integralOrdinaryTensorSection
  have hη := PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app
    (𝟙 ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (completedIntegralCommRingSheafUnrestricted l L X)).obj)
    (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
      (integralCompletedScalarMap l E L ι X) M)
  with_unfolding_all
    exact congrArg (fun f ↦ (eqToHom (scalar_obj l E L ι X M).symm).val.app U
      (f.app U ((1 : (completedIntegralCommRingSheafUnrestricted l L X).obj.obj U)
        ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E X).obj.obj U,
          ((integralCompletedScalarMap l E L ι X).hom.app U).hom] x))) hη


private theorem scalarMap_eq_completed
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (X : Scheme.{u}) :
    integralCompletedScalarMap l E L ι X = completedCoefficientMap l E L ι X := by
  apply (completedCoefficientMap_existsUnique l E L ι X).unique
  · exact (integralCompletedScalarMap_existsUnique l E L ι X).exists.choose_spec
  · exact (completedCoefficientMap_existsUnique l E L ι X).exists.choose_spec

/-- Ordinary coefficient extension and inverse image commute with their actual units.
Source: blueprint scalar/root balancing before quotient realization
(blueprint: def-pur-canonical-tate-scalar-naturality).
Proof: both composites extend scalars after inverse image. The tensor associator
sends b tensor f-star(a tensor x) to f-star(b tensor (a tensor x)); its inverse
multiplies coefficients. This is balanced and commutes with restrictions. The
unit formula fixes its action on every local generator, proving uniqueness. -/
theorem ordinaryScalarSquare_existsUnique
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) {X Y : Scheme.{u}} (g : X ⟶ Y) :
    ∃! e : modulePull l E g ⋙ integralOrdinaryScalar l E L ι X ≅
        integralOrdinaryScalar l E L ι Y ⋙ modulePull l L g,
      ∀ (M : integralTowerModules l E Y) (V : Y.ProEt) (x : M.val.obj (op V)),
        (e.hom.app M).val.app (op ((proEtaleBaseChange g).obj V))
          (integralOrdinaryTensorSection l E L ι X ((modulePull l E g).obj M)
            (op ((proEtaleBaseChange g).obj V)) 1 (moduleSection l E g M V x)) =
        moduleSection l L g ((integralOrdinaryScalar l E L ι Y).obj M) V
          (integralOrdinaryTensorSection l E L ι Y M (op V) 1 x) := by
  have hc : ((PurCompactSupport.completed l E).pull g).hom ≫
      integralCompletedScalarMap l E L ι X =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
        (integralCompletedScalarMap l E L ι Y) ≫
          ((PurCompactSupport.completed l L).pull g).hom := by
    rw [scalarMap_eq_completed, scalarMap_eq_completed]
    exact PurCompactSupport.completedChange_square l E L ι g
  let d := proEtaleRingRestrictionDirectImage g
    ((PurCompactSupport.completed l E).ring Y) ((PurCompactSupport.completed l L).ring Y)
    ((PurCompactSupport.completed l E).ring X) ((PurCompactSupport.completed l L).ring X)
    (integralCompletedScalarMap l E L ι Y) (integralCompletedScalarMap l E L ι X)
    ((PurCompactSupport.completed l E).pull g) ((PurCompactSupport.completed l L).pull g) hc
  let adjA := (ordinaryAdj l E g).comp (scalarAdj l E L ι X)
  let adjB := (scalarAdj l E L ι Y).comp (ordinaryAdj l L g)
  let e := (conjugateIsoEquiv adjB adjA).symm d
  have hd (N : integralTowerModules l L X) (U : Y.ProEtᵒᵖ)
      (x : N.val.obj ((proEtaleBaseChange g).op.obj U)) :
      (d.hom.app N).val.app U x = x :=
    (Classical.choose_spec (proEtaleRingRestrictionDirectImage_existsUnique g
      ((PurCompactSupport.completed l E).ring Y) ((PurCompactSupport.completed l L).ring Y)
      ((PurCompactSupport.completed l E).ring X) ((PurCompactSupport.completed l L).ring X)
      (integralCompletedScalarMap l E L ι Y) (integralCompletedScalarMap l E L ι X)
      ((PurCompactSupport.completed l E).pull g)
      ((PurCompactSupport.completed l L).pull g) hc)).1 N U x
  have he : ∀ (M : integralTowerModules l E Y) (V : Y.ProEt) (x : M.val.obj (op V)),
      (e.hom.app M).val.app (op ((proEtaleBaseChange g).obj V))
        (integralOrdinaryTensorSection l E L ι X ((modulePull l E g).obj M)
          (op ((proEtaleBaseChange g).obj V)) 1 (moduleSection l E g M V x)) =
      moduleSection l L g ((integralOrdinaryScalar l E L ι Y).obj M) V
        (integralOrdinaryTensorSection l E L ι Y M (op V) 1 x) := by
    intro M V x
    have hu := congrArg (fun z ↦ z.val.app (op V) x)
      (unit_conjugateEquiv_symm adjB adjA d.hom M)
    change (d.hom.app ((modulePull l L g).obj
        ((integralOrdinaryScalar l E L ι Y).obj M))).val.app (op V)
        (moduleSection l L g ((integralOrdinaryScalar l E L ι Y).obj M) V
          (((scalarAdj l E L ι Y).unit.app M).val.app (op V) x)) =
      (e.hom.app M).val.app (op ((proEtaleBaseChange g).obj V))
        (((scalarAdj l E L ι X).unit.app ((modulePull l E g).obj M)).val.app
          (op ((proEtaleBaseChange g).obj V)) (moduleSection l E g M V x)) at hu
    simpa only [hd, scalarAdj_unit] using hu.symm
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (adjA.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext x
  change (e'.hom.app M).val.app (op ((proEtaleBaseChange g).obj V.unop))
      (((scalarAdj l E L ι X).unit.app ((modulePull l E g).obj M)).val.app
        (op ((proEtaleBaseChange g).obj V.unop)) (moduleSection l E g M V.unop x)) =
    (e.hom.app M).val.app (op ((proEtaleBaseChange g).obj V.unop))
      (((scalarAdj l E L ι X).unit.app ((modulePull l E g).obj M)).val.app
        (op ((proEtaleBaseChange g).obj V.unop)) (moduleSection l E g M V.unop x))
  rw [scalarAdj_unit]
  exact (he' M V.unop x).trans (he M V.unop x).symm


/-- The scalar comparison fixed by the entire unit-section formula.
Source: blueprint canonical coefficient extension comparison
(blueprint: def-pur-canonical-tate-scalar-naturality). -/
def ordinaryScalarSquare
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) {X Y : Scheme.{u}} (g : X ⟶ Y) :=
  (ordinaryScalarSquare_existsUnique l E L ι g).exists.choose

/-- The normalized finite quotient of an integral sheaf line, before deriving.
Source: blueprint strict quotient lines, signed-reduction comparison
(blueprint: def-pur-canonical-tate-scalar-naturality). -/
def integralReductionSheafLine (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] (n r : ℕ) :=
  ((((signedTwistReduction_comparison l E X).1 n).exists.choose_spec.2
    (r : ℤ)).exists.choose)

/-- Coefficient naturality before realization: each strict quotient, and entire
strict target systems for completed finite scalar extension.
Source: blueprint strict quotient-system coefficient identities
(blueprint: def-pur-canonical-tate-scalar-naturality). -/
def strictCoefficientLaws (X : Scheme.{u}) (g : X ⟶ X) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)] : Prop :=
  (∀ n r : ℕ,
    (scalarReductionExtension l E X n).map (positiveLineMaps l E g r).hom ≫
      (integralReductionSheafLine l E X n r).hom =
    (ordinaryReductionSquare l E g n).hom.app (positiveLine l E X r) ≫
      (finiteModulePull l E g n).map (integralReductionSheafLine l E X n r).hom ≫
      (finitePositiveLineMaps l E g n r).hom) ∧
  ∀ (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (r : ℕ),
    (pullbackTensorOrdinaryReduction l L X).map
      ((integralOrdinaryScalar l E L ι X).map (positiveLineMaps l E g r).hom ≫
        (twistLineScalarIso l E X L ι (r : ℤ)).hom) =
    (pullbackTensorOrdinaryReduction l L X).map
      ((ordinaryScalarSquare l E L ι g).hom.app (positiveLine l E X r) ≫
        (modulePull l L g).map (twistLineScalarIso l E X L ι (r : ℤ)).hom ≫
        (positiveLineMaps l L g r).hom)

end WeilConjectures.CanonicalTate
