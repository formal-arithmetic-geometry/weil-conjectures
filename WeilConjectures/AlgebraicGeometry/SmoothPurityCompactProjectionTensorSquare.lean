/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityCompactProjectionData
import all WeilConjectures.AlgebraicGeometry.RingedProjectionLocalTensorSquare
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.Algebra.Homology.CochainTensorModelRigidity
import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Tensor compatibility of the section-normalized pullback square

Source: Stacks 03EL, 07A4, 0D6D and 0E48.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
open SheafOfModules.OpenTensorNormalization
namespace AlgebraicGeometry.ProEtale.CompactProjectionBaseChange

attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  HasDerivedCategory.standard DerivedCategory SheafOfModules.monoidalCategory

section
variable {m : Mode} {c : Coefficients.{u} m} (o : Presentation c)
  {X' X Y' Y : Scheme.{u}}
  {a : X' ⟶ X} {b : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  (s : CommSq a b f g)

private theorem two_pure_unit {Z₀ Z₁ Z₂ : Scheme.{u}}
    (f : Z₁ ⟶ Z₀) (a : Z₂ ⟶ Z₁) (M N : Mod (c.ring Z₀))
    (W : (Site m Z₀)ᵒᵖ) (x : M.val.obj W) (y : N.val.obj W) :
    (((o.operation a).pushforward ⋙ (o.operation f).pushforward).map
      ((o.operation a).pullback.map ((o.ordinaryTensor f).iso M N).hom ≫
        ((o.ordinaryTensor a).iso ((o.operation f).pullback.obj M)
          ((o.operation f).pullback.obj N)).hom)).val.app W
      ((((o.operation f).moduleAdjunction.comp
        (o.operation a).moduleAdjunction).unit.app (((tensor (c.ring Z₀)).obj M).obj N)).val.app
          W (pure (c.ring Z₀) M N W x y)) =
    pure (c.ring Z₂) _ _ ((baseChange m a).op.obj ((baseChange m f).op.obj W))
      ((((o.operation f).moduleAdjunction.comp
        (o.operation a).moduleAdjunction).unit.app M).val.app W x)
      ((((o.operation f).moduleAdjunction.comp
        (o.operation a).moduleAdjunction).unit.app N).val.app W y) := by
  let Wf := (baseChange m f).op.obj W
  let z := ((o.operation f).moduleAdjunction.unit.app
    (((tensor (c.ring Z₀)).obj M).obj N)).val.app W (pure (c.ring Z₀) M N W x y)
  have hn := (o.operation a).moduleAdjunction.unit.naturality
    ((o.ordinaryTensor f).iso M N).hom
  have hu := congrArg (fun k ↦ k.val.app Wf z) hn
  change ((o.operation a).moduleAdjunction.unit.app _).val.app Wf
      ((((o.ordinaryTensor f).iso M N).hom.val.app Wf) z) =
    (((o.operation a).pushforward.map
      ((o.operation a).pullback.map ((o.ordinaryTensor f).iso M N).hom)).val.app Wf)
      (((o.operation a).moduleAdjunction.unit.app _).val.app Wf z) at hu
  change (((o.operation a).pushforward.map
      ((o.ordinaryTensor a).iso ((o.operation f).pullback.obj M)
        ((o.operation f).pullback.obj N)).hom).val.app Wf)
      ((((o.operation a).pushforward.map
        ((o.operation a).pullback.map ((o.ordinaryTensor f).iso M N).hom)).val.app Wf)
        (((o.operation a).moduleAdjunction.unit.app _).val.app Wf z)) = _
  rw [← hu]
  change (((o.operation a).pushforward.map
      ((o.ordinaryTensor a).iso ((o.operation f).pullback.obj M)
        ((o.operation f).pullback.obj N)).hom).val.app Wf)
      (((o.operation a).moduleAdjunction.unit.app _).val.app Wf
        ((((o.operation f).pushforward.map ((o.ordinaryTensor f).iso M N).hom).val.app W)
          (((o.operation f).moduleAdjunction.unit.app _).val.app W
            (pure (c.ring Z₀) M N W x y)))) = _
  rw [(o.ordinaryTensor f).pure_unit, (o.ordinaryTensor a).pure_unit]
  rfl

private theorem inverse_square_unit (M : Mod (c.ring Y)) :
    ((o.operation f).moduleAdjunction.comp (o.operation a).moduleAdjunction).unit.app M ≫
      ((o.operation a).pushforward ⋙ (o.operation f).pushforward).map
        ((o.ordinarySquare s).inv.app M) =
    ((o.operation g).moduleAdjunction.comp (o.operation b).moduleAdjunction).unit.app M ≫
      (o.rightSquare s).hom.app
        ((o.operation b).pullback.obj ((o.operation g).pullback.obj M)) := by
  exact (unit_conjugateEquiv_symm
    ((o.operation g).moduleAdjunction.comp (o.operation b).moduleAdjunction)
    ((o.operation f).moduleAdjunction.comp (o.operation a).moduleAdjunction)
    (o.rightSquare s).hom M).symm

private theorem inverse_square_unit_sections (M : Mod (c.ring Y))
    (W : (Site m Y)ᵒᵖ) (x : M.val.obj W) :
    ((((o.operation a).pushforward ⋙ (o.operation f).pushforward).map
      ((o.ordinarySquare s).inv.app M)).val.app W)
      ((((o.operation f).moduleAdjunction.comp
        (o.operation a).moduleAdjunction).unit.app M).val.app W x) =
    ((o.operation b).pullback.obj ((o.operation g).pullback.obj M)).val.map
      ((siteSquare m s).inv.app W.unop).op
      ((((o.operation g).moduleAdjunction.comp
        (o.operation b).moduleAdjunction).unit.app M).val.app W x) := by
  have h := congrArg (fun k ↦ k.val.app W x) (inverse_square_unit o s M)
  change _ = ((o.rightSquare s).hom.app
    ((o.operation b).pullback.obj ((o.operation g).pullback.obj M))).val.app W
    ((((o.operation g).moduleAdjunction.comp
      (o.operation b).moduleAdjunction).unit.app M).val.app W x) at h
  exact h.trans (congrFun (eq_of_heq (o.rightSections s
    ((o.operation b).pullback.obj ((o.operation g).pullback.obj M)) W))
      ((((o.operation g).moduleAdjunction.comp
        (o.operation b).moduleAdjunction).unit.app M).val.app W x))

private theorem ordinary_inverse_tensor_square (M N : Mod (c.ring Y)) :
    (o.ordinarySquare s).inv.app (((tensor (c.ring Y)).obj M).obj N) ≫
      (o.operation b).pullback.map ((o.ordinaryTensor g).iso M N).hom ≫
      ((o.ordinaryTensor b).iso ((o.operation g).pullback.obj M)
        ((o.operation g).pullback.obj N)).hom =
    (o.operation a).pullback.map ((o.ordinaryTensor f).iso M N).hom ≫
      ((o.ordinaryTensor a).iso ((o.operation f).pullback.obj M)
        ((o.operation f).pullback.obj N)).hom ≫
      (Functor.uncurry.obj (tensor (c.ring X'))).map
        (Prod.mkHom ((o.ordinarySquare s).inv.app M)
          ((o.ordinarySquare s).inv.app N)) := by
  let adj := (o.operation f).moduleAdjunction.comp (o.operation a).moduleAdjunction
  let v := (o.operation b).pullback.mapIso ((o.ordinaryTensor g).iso M N) ≪≫
    (o.ordinaryTensor b).iso ((o.operation g).pullback.obj M)
      ((o.operation g).pullback.obj N)
  let w := (o.operation a).pullback.mapIso ((o.ordinaryTensor f).iso M N) ≪≫
    (o.ordinaryTensor a).iso ((o.operation f).pullback.obj M)
      ((o.operation f).pullback.obj N)
  let δ := (o.ordinarySquare s).inv
  let FA := (o.operation a).pushforward ⋙ (o.operation f).pushforward
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply SheafOfModules.CochainScalarConstruction.pure_hom_ext (c.ring Y) M N
  intro W x y
  let Wfa := (baseChange m a).op.obj ((baseChange m f).op.obj W)
  let i := ((siteSquare m s).inv.app W.unop).op
  let z := (((o.operation g).moduleAdjunction.comp
    (o.operation b).moduleAdjunction).unit.app (((tensor (c.ring Y)).obj M).obj N)).val.app
      W (pure (c.ring Y) M N W x y)
  have ht := inverse_square_unit_sections o s (((tensor (c.ring Y)).obj M).obj N) W
    (pure (c.ring Y) M N W x y)
  have hM := inverse_square_unit_sections o s M W x
  have hN := inverse_square_unit_sections o s N W y
  have hn := PresheafOfModules.naturality_apply v.hom.val i z
  have hg := two_pure_unit o g b M N W x y
  have hf := two_pure_unit o f a M N W x y
  have hr := SheafOfModules.CochainScalarConstruction.pure_restrict (c.ring X')
    ((o.operation b).pullback.obj ((o.operation g).pullback.obj M))
    ((o.operation b).pullback.obj ((o.operation g).pullback.obj N)) i
    ((((o.operation g).moduleAdjunction.comp
      (o.operation b).moduleAdjunction).unit.app M).val.app W x)
    ((((o.operation g).moduleAdjunction.comp
      (o.operation b).moduleAdjunction).unit.app N).val.app W y)
  have hm := SheafOfModules.CochainScalarConstruction.pure_map (c.ring X')
    (δ.app M) (δ.app N) Wfa
    ((adj.unit.app M).val.app W x) ((adj.unit.app N).val.app W y)
  change (v.hom.val.app Wfa)
      (((FA.map (δ.app (((tensor (c.ring Y)).obj M).obj N))).val.app W)
        ((adj.unit.app _).val.app W (pure (c.ring Y) M N W x y))) =
    (((Functor.uncurry.obj (tensor (c.ring X'))).map
      (Prod.mkHom (δ.app M) (δ.app N))).val.app Wfa)
      (((FA.map w.hom).val.app W)
        ((adj.unit.app _).val.app W (pure (c.ring Y) M N W x y)))
  erw [ht, hf]
  erw [hn, hg, hr]
  simp only [CategoryTheory.MonoidalCategory.tensorHom_def] at hm
  exact (hm.trans (by erw [hM, hN]; rfl)).symm

private theorem ordinary_tensor_square (M N : Mod (c.ring Y)) :
    (o.ordinarySquare s).hom.app (((tensor (c.ring Y)).obj M).obj N) ≫
      (o.operation a).pullback.map ((o.ordinaryTensor f).iso M N).hom ≫
      ((o.ordinaryTensor a).iso ((o.operation f).pullback.obj M)
        ((o.operation f).pullback.obj N)).hom =
    (o.operation b).pullback.map ((o.ordinaryTensor g).iso M N).hom ≫
      ((o.ordinaryTensor b).iso ((o.operation g).pullback.obj M)
        ((o.operation g).pullback.obj N)).hom ≫
      (Functor.uncurry.obj (tensor (c.ring X'))).map
        (Prod.mkHom ((o.ordinarySquare s).hom.app M)
          ((o.ordinarySquare s).hom.app N)) := by
  apply (cancel_epi ((o.ordinarySquare s).inv.app
    (((tensor (c.ring Y)).obj M).obj N))).1
  simp only [Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% (ordinary_inverse_tensor_square o s M N)]
  simp only [← Functor.map_comp, prod_comp, Iso.inv_hom_id_app]
  simp

private theorem square_normalization (P : CochainComplex (Mod (c.ring Y)) ℤ) :
    (o.square s).hom.app (DerivedCategory.Q.obj P) ≫
      (twoFactors (o.operation f).leftModel (o.operation a).leftModel P).hom =
    (twoFactors (o.operation g).leftModel (o.operation b).leftModel P).hom ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (o.ordinarySquare s).hom (.up ℤ)).app P) := by
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso (o.operation g).pullback
    (o.operation b).pullback).hom.app (DerivedCategory.Q.obj P))).1
  simp only [Presentation.square, twoFactors, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.mapIso_hom, Iso.app_hom, Category.assoc,
    Iso.hom_inv_id_app_assoc]
  erw [Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac,
    Functor.mapDerivedCategoryCompIso_hom_app_factors_assoc]


private theorem inverse_on_representatives
    (P Q : CochainComplex (Mod (c.ring Y)) ℤ)
    (hp : resolving (c.ring Y) P) (hq : resolving (c.ring Y) Q) :
    (o.tensor X').functor.map (Prod.mkHom
        ((o.square s).hom.app (DerivedCategory.Q.obj P))
        ((o.square s).hom.app (DerivedCategory.Q.obj Q))) ≫
      (o.tensorComparison a).comparison.inv.app
        ((o.operation f).left.obj (DerivedCategory.Q.obj P),
          (o.operation f).left.obj (DerivedCategory.Q.obj Q)) ≫
      (o.operation a).left.map ((o.tensorComparison f).comparison.inv.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) =
    (o.tensorComparison b).comparison.inv.app
        ((o.operation g).left.obj (DerivedCategory.Q.obj P),
          (o.operation g).left.obj (DerivedCategory.Q.obj Q)) ≫
      (o.operation b).left.map ((o.tensorComparison g).comparison.inv.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      (o.square s).hom.app
        ((o.tensor Y).functor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) := by
  exact four_models_inverse (o.tensorComparison f) (o.tensorComparison g)
    (o.tensorComparison a) (o.tensorComparison b) (o.ordinarySquare s).hom
    (ordinary_tensor_square o s) (o.square s).hom (square_normalization o s) P Q hp hq

end

/-- Tensor compatibility of the section-normalized pullback square.
This is an equality of inverse-image comparisons alone, before taking mates or
introducing an open extension or a compact-support projection map.
Source: Stacks 03EL, 07A4, 0D6D and 0E48
(blueprint: lem-sp-compact-projection-tensor-square).

Proof: conjugate the specified sectionwise direct-image square through the ordinary
module adjunctions. The resulting ordinary square sends each scalar-extension
insertion to the insertion along the same fibre-product comparison. The ordinary
pure-tensor normalizations therefore make the two routes equal: on a generalized
pure tensor both apply this comparison to its two factors. The tensor universal
property extends the equation to module sheaves. Apply it in each bidegree of two
flat-term K-flat complexes and sum along the total-complex diagonals. Both routes
preserve bidegrees and the sign on the second differential, so give equal chain maps.
The defining representative equations of `TensorComparison` and the termwise
localization formula for `Presentation.square` identify these maps with the displayed
routes. Two-variable K-flat descent proves the equality for all derived inputs.
This proof takes place on the vertical diagram site as a single ringed site for
systems, retaining transitions; it does not infer equality from level evaluations. -/
theorem Presentation.tensor_square {m : Mode} {c : Coefficients.{u} m}
    (o : Presentation c) {X' X Y' Y : Scheme.{u}}
    {a : X' ⟶ X} {b : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (s : CommSq a b f g) (M N : Der (c.ring Y)) :
    (o.square s).hom.app ((o.tensor Y).functor.obj (M, N)) ≫
        (o.operation a).left.map ((o.tensorComparison f).comparison.hom.app (M, N)) ≫
        (o.tensorComparison a).comparison.hom.app
          ((o.operation f).left.obj M, (o.operation f).left.obj N) =
      (o.operation b).left.map ((o.tensorComparison g).comparison.hom.app (M, N)) ≫
        (o.tensorComparison b).comparison.hom.app
          ((o.operation g).left.obj M, (o.operation g).left.obj N) ≫
        (o.tensor X').functor.map
          (CategoryTheory.Prod.mkHom ((o.square s).hom.app M) ((o.square s).hom.app N)) := by
  let F := (o.operation f).left
  let G := (o.operation g).left
  let H := (o.operation a).left
  let K := (o.operation b).left
  let A := (o.tensor Y).functor
  let D := (o.tensor X').functor
  let tF := (o.tensorComparison f).comparison
  let tG := (o.tensorComparison g).comparison
  let tH := (o.tensorComparison a).comparison
  let tK := (o.tensorComparison b).comparison
  let theta := (o.square s).hom
  let α : (G.prod G) ⋙ (K.prod K) ⋙ D ⟶ A ⋙ F ⋙ H :=
    Functor.whiskerRight (theta.prod theta) D ≫
      Functor.whiskerLeft (F.prod F) tH.inv ≫ Functor.whiskerRight tF.inv H
  let β : (G.prod G) ⋙ (K.prod K) ⋙ D ⟶ A ⋙ F ⋙ H :=
    Functor.whiskerLeft (G.prod G) tK.inv ≫ Functor.whiskerRight tG.inv K ≫
      Functor.whiskerLeft A theta
  have he : α = β := by
    obtain ⟨_, _, _, hd⟩ := SheafOfModules.cochain_tensor_model_rigidity
      (topology m Y) (c.ring Y)
    apply (hd (Der (c.ring X')) inferInstance _ _).1
    apply NatTrans.ext
    funext Z
    rcases Z with ⟨P, Q⟩
    exact inverse_on_representatives o s P.obj Q.obj P.property Q.property
  have hi := congrArg (fun t ↦ t.app (M, N)) he
  change D.map (Prod.mkHom (theta.app M) (theta.app N)) ≫
      tH.inv.app (F.obj M, F.obj N) ≫ H.map (tF.inv.app (M, N)) =
    tK.inv.app (G.obj M, G.obj N) ≫ K.map (tG.inv.app (M, N)) ≫
      theta.app (A.obj (M, N)) at hi
  let v := K.mapIso (tG.app (M, N)) ≪≫ tK.app (G.obj M, G.obj N)
  let w := H.mapIso (tF.app (M, N)) ≪≫ tH.app (F.obj M, F.obj N)
  have hi' : D.map (Prod.mkHom (theta.app M) (theta.app N)) ≫ w.inv =
      v.inv ≫ theta.app (A.obj (M, N)) := by
    simpa only [v, w, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc]
      using hi
  have hf : v.hom ≫ D.map (Prod.mkHom (theta.app M) (theta.app N)) =
      theta.app (A.obj (M, N)) ≫ w.hom := by
    apply (Iso.comp_inv_eq w).1
    rw [Category.assoc, hi', Iso.hom_inv_id_assoc]
  simpa only [v, w, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc]
    using hf.symm

end AlgebraicGeometry.ProEtale.CompactProjectionBaseChange
