/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ClopenComparisonTensorSquareData
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
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModelSupplement
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

/-!
# Tensor compatibility of the Cartesian pullback compositor

Source: `literature/stacks-project/sites-cohomology.tex`, Tags 07A4 and 0D6D;
the normalized clopen tensor refinement (blueprint:
`lem-sf-clopen-pullback-tensor-compatibility`).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.ProjectionRestriction
open SheafOfModules.OpenTensorNormalization

namespace SheafOfModules.ClopenComparisonTensorSquare

set_option maxHeartbeats 800000 in
-- The mate equation compares the concrete scalar-restricted section functors.
private theorem ordinary_unit_square {m : Mode} {d : Input.{u} m} {t : SiteSquare d}
    (o : Operations d t) (M : Mod d.R) (W : (Site m d.U)ᵒᵖ)
    (x : M.val.obj ((openInclusion m d.j).op.obj W)) :
    (o.ordinaryTheta.inv.app M).val.app ((baseChange m d.gU).op.obj W)
        ((o.gUPull.adjunction.unit.app ((restrict m d.j d.R).obj M)).val.app W x) =
      (o.gPull.ordinary.obj M).val.map (t.iso.inv.app W.unop).op
        ((o.gPull.adjunction.unit.app M).val.app ((openInclusion m d.j).op.obj W) x) := by
  have hm := o.ordinaryTheta_mate M
  erw [Adjunction.homEquiv_unit] at hm
  have h := congrArg (fun z ↦ z.val.app W x) hm
  change (o.ordinaryTheta.inv.app M).val.app ((baseChange m d.gU).op.obj W)
      ((o.gUPull.adjunction.unit.app ((restrict m d.j d.R).obj M)).val.app W x) =
    (o.rightSquare.hom.app (o.gPull.ordinary.obj M)).val.app W
      ((o.gPull.adjunction.unit.app M).val.app ((openInclusion m d.j).op.obj W) x) at h
  exact h.trans (o.rightSections _ W _)

set_option maxHeartbeats 800000 in
-- Four section functors and their coefficient restrictions occur in this calculation.
private theorem ordinary_tensor_square {m : Mode} {d : Input.{u} m} {t : SiteSquare d}
    {o : Operations d t} {A : Scheme.{u}} {s : A ⟶ d.U'} [IsOpenImmersion s]
    (v : Data o s) (M N : Mod d.R) :
    o.ordinaryTheta.inv.app (((tensor d.R).obj M).obj N) ≫
        (restrict m d.j' d.S).map (v.tensorP.ordinary M N).hom ≫
        (v.tensorB.ordinary (o.gPull.ordinary.obj M) (o.gPull.ordinary.obj N)).hom =
      o.gUPull.ordinary.map (o.restrictionTensor M N).hom ≫
        (v.tensorQ.ordinary ((restrict m d.j d.R).obj M)
          ((restrict m d.j d.R).obj N)).hom ≫
        (Functor.uncurry.obj (tensor (restrictRing m d.j' d.S))).map
          (Prod.mkHom (o.ordinaryTheta.inv.app M) (o.ordinaryTheta.inv.app N)) := by
  apply (o.gUPull.adjunction.homEquiv _ _).injective
  erw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply (cancel_epi (o.restrictionTensor M N).inv).1
  apply SheafOfModules.CochainScalarConstruction.pure_hom_ext (restrictRing m d.j d.R)
    ((restrict m d.j d.R).obj M) ((restrict m d.j d.R).obj N)
  intro W x y
  have hback : (o.restrictionTensor M N).inv.val.app W
      (pure (restrictRing m d.j d.R) ((restrict m d.j d.R).obj M)
        ((restrict m d.j d.R).obj N) W x y) =
      pure d.R M N ((openInclusion m d.j).op.obj W) x y := by
    have h := congrArg (fun z ↦ (o.restrictionTensor M N).inv.val.app W z)
      (o.restrictionTensor_sections M N W x y)
    have hi := congrArg (fun z ↦ z.val.app W
      (pure d.R M N ((openInclusion m d.j).op.obj W) x y))
      (o.restrictionTensor M N).hom_inv_id
    change (o.restrictionTensor M N).inv.val.app W
      ((o.restrictionTensor M N).hom.val.app W
        (pure d.R M N ((openInclusion m d.j).op.obj W) x y)) = _ at hi
    exact h.symm.trans hi
  have hn := o.gUPull.adjunction.unit.naturality (o.restrictionTensor M N).hom
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  let T := (baseChange m d.gU).op.obj W
  let V := (openInclusion m d.j).op.obj W
  let Z := (openInclusion m d.j').op.obj T
  let i := (t.iso.inv.app W.unop).op
  have hu := congrArg (fun k ↦ k.val.app W (pure d.R M N V x y)) hn
  change (o.gUPull.adjunction.unit.app
      (((tensor (restrictRing m d.j d.R)).obj ((restrict m d.j d.R).obj M)).obj
        ((restrict m d.j d.R).obj N))).val.app W
        ((o.restrictionTensor M N).hom.val.app W (pure d.R M N V x y)) =
      ((direct m d.gU _ _ (cornerCoefficient t)).map
        (o.gUPull.ordinary.map (o.restrictionTensor M N).hom)).val.app W
          ((o.gUPull.adjunction.unit.app _).val.app W (pure d.R M N V x y)) at hu
  erw [o.restrictionTensor_sections] at hu
  have hM := ordinary_unit_square o M W x
  have hN := ordinary_unit_square o N W y
  have hT := ordinary_unit_square o (((tensor d.R).obj M).obj N) W
    (pure d.R M N V x y)
  have hmap := SheafOfModules.CochainScalarConstruction.pure_map
    (restrictRing m d.j' d.S) (o.ordinaryTheta.inv.app M)
      (o.ordinaryTheta.inv.app N) T
      ((o.gUPull.adjunction.unit.app ((restrict m d.j d.R).obj M)).val.app W x)
      ((o.gUPull.adjunction.unit.app ((restrict m d.j d.R).obj N)).val.app W y)
  simp only [CategoryTheory.MonoidalCategory.tensorHom_def] at hmap
  change ((Functor.uncurry.obj (tensor (restrictRing m d.j' d.S))).map
    (Prod.mkHom (o.ordinaryTheta.inv.app M) (o.ordinaryTheta.inv.app N))).val.app T
      (pure (restrictRing m d.j' d.S) _ _ T _ _) = _ at hmap
  erw [hM, hN] at hmap
  have hnat := PresheafOfModules.naturality_apply (v.tensorP.ordinary M N).hom.val i
    ((o.gPull.adjunction.unit.app (((tensor d.R).obj M).obj N)).val.app V
      (pure d.R M N V x y))
  have hp := v.tensorP.pure_unit M N V x y
  have hr := SheafOfModules.CochainScalarConstruction.pure_restrict d.S
    (o.gPull.ordinary.obj M) (o.gPull.ordinary.obj N) i
    ((o.gPull.adjunction.unit.app M).val.app V x)
    ((o.gPull.adjunction.unit.app N).val.app V y)
  change (v.tensorB.ordinary _ _).hom.val.app T
      ((v.tensorP.ordinary M N).hom.val.app Z
        ((o.ordinaryTheta.inv.app (((tensor d.R).obj M).obj N)).val.app T
          ((o.gUPull.adjunction.unit.app _).val.app W
            ((o.restrictionTensor M N).inv.val.app W
              (pure (restrictRing m d.j d.R) _ _ W x y))))) =
    ((Functor.uncurry.obj (tensor (restrictRing m d.j' d.S))).map
      (Prod.mkHom (o.ordinaryTheta.inv.app M) (o.ordinaryTheta.inv.app N))).val.app T
      (((direct m d.gU _ _ (cornerCoefficient t)).map
          (v.tensorQ.ordinary _ _).hom).val.app W
        (((direct m d.gU _ _ (cornerCoefficient t)).map
          (o.gUPull.ordinary.map (o.restrictionTensor M N).hom)).val.app W
          ((o.gUPull.adjunction.unit.app _).val.app W
            ((o.restrictionTensor M N).inv.val.app W
              (pure (restrictRing m d.j d.R) _ _ W x y)))))
  erw [hback, hT, ← hu, v.tensorQ.pure_unit]
  change (v.tensorB.ordinary _ _).hom.val.app T
      ((v.tensorP.ordinary M N).hom.val.app Z
        ((o.gPull.ordinary.obj (((tensor d.R).obj M).obj N)).val.map i
          ((o.gPull.adjunction.unit.app _).val.app V (pure d.R M N V x y)))) = _
  erw [hnat, hp, hr]
  exact (v.tensorB.pure_sections _ _ T _ _).trans hmap.symm

-- Adapted from RingedProjectionLocalTensorSquare, with comparison maps required
-- to be invertible only on resolving complexes.
section Representatives

variable {C₀ C₁ C₂ : Type (u + 1)}
  [Category.{u} C₀] [Category.{u} C₁] [Category.{u} C₂]
  [EssentiallySmall.{u + 1} C₀] [EssentiallySmall.{u + 1} C₁]
  [EssentiallySmall.{u + 1} C₂]
  {J₀ : GrothendieckTopology C₀} {J₁ : GrothendieckTopology C₁}
  {J₂ : GrothendieckTopology C₂}
  {R₀ : Sheaf J₀ CommRingCat.{u + 1}} {R₁ : Sheaf J₁ CommRingCat.{u + 1}}
  {R₂ : Sheaf J₂ CommRingCat.{u + 1}}

-- The counit comparison need only be invertible on the resolving class.
private structure PartialModel (L : Mod R₀ ⥤ Mod R₁) [L.Additive] where
  functor : Der R₀ ⥤ Der R₁
  factors : DerivedCategory.Q ⋙ functor ⟶
    L.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  flat : ∀ P, resolving R₀ P → IsIso (factors.app P)

private structure PartialTensor (L : Mod R₀ ⥤ Mod R₁) [L.Additive]
    (d : PartialModel L) (a : TensorModel R₀) (b : TensorModel R₁)
    (mu : ∀ M N, L.obj (((tensor R₀).obj M).obj N) ≅
      ((tensor R₁).obj (L.obj M)).obj (L.obj N)) where
  preserves : ∀ P, resolving R₀ P → resolving R₁ ((L.mapHomologicalComplex (.up ℤ)).obj P)
  comparison : a.functor ⋙ d.functor ≅ (d.functor.prod d.functor) ⋙ b.functor
  comm : ∀ (P Q : CochainComplex (Mod R₀) ℤ) (n m : ℤ),
    totalComponent a b L mu P Q n ≫ L.map (((total R₀).obj (P, Q)).d n m) =
      ((total R₁).obj ((L.mapHomologicalComplex (.up ℤ)).obj P,
        (L.mapHomologicalComplex (.up ℤ)).obj Q)).d n m ≫ totalComponent a b L mu P Q m
  representative : ∀ (P Q : CochainComplex (Mod R₀) ℤ)
      (hp : resolving R₀ P) (hq : resolving R₀ Q),
    d.functor.map (a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
      comparison.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      b.functor.map (Prod.mkHom (d.factors.app P) (d.factors.app Q)) ≫
      b.representative.inv.app
        (⟨(L.mapHomologicalComplex (.up ℤ)).obj P, preserves P hp⟩,
          ⟨(L.mapHomologicalComplex (.up ℤ)).obj Q, preserves Q hq⟩) ≫
      DerivedCategory.Q.map (totalMap a b L mu comm P Q) =
      d.factors.app ((total R₀).obj (P, Q))

@[irreducible] private def chain {L : Mod R₀ ⥤ Mod R₁} [L.Additive] {d : PartialModel L}
    {a : TensorModel R₀} {b : TensorModel R₁}
    {mu : ∀ M N, L.obj (((tensor R₀).obj M).obj N) ≅
      ((tensor R₁).obj (L.obj M)).obj (L.obj N)}
    (t : PartialTensor L d a b mu) (P Q : CochainComplex (Mod R₀) ℤ) :=
  totalMap a b L mu t.comm P Q

private theorem chain_summand
    {L : Mod R₀ ⥤ Mod R₁} [L.Additive] {d : PartialModel L}
    {a : TensorModel R₀} {b : TensorModel R₁}
    {mu : ∀ M N, L.obj (((tensor R₀).obj M).obj N) ≅
      ((tensor R₁).obj (L.obj M)).obj (L.obj N)}
    (t : PartialTensor L d a b mu) (P Q : CochainComplex (Mod R₀) ℤ)
    (i j n : ℤ) (hij : i + j = n) :
    HomologicalComplex.ιMapBifunctor ((L.mapHomologicalComplex (.up ℤ)).obj P)
        ((L.mapHomologicalComplex (.up ℤ)).obj Q) (tensor R₁) (.up ℤ) i j n hij ≫
      (chain t P Q).f n =
    (mu (P.X i) (Q.X j)).inv ≫
      L.map (HomologicalComplex.ιMapBifunctor P Q (tensor R₀) (.up ℤ) i j n hij) := by
  let := SheafOfModules.monoidalCategory R₀
  let := SheafOfModules.monoidalCategory R₁
  let := a.preadditive
  let := b.preadditive
  simp only [chain, totalMap, totalComponent, tensorPullbackTotalComponent]
  exact HomologicalComplex.ι_mapBifunctorDesc
    (K₁ := (L.mapHomologicalComplex (.up ℤ)).obj P)
    (K₂ := (L.mapHomologicalComplex (.up ℤ)).obj Q) (F := tensor R₁) (c := .up ℤ)
    (fun p q h ↦ (mu (P.X p) (Q.X q)).inv ≫
      L.map (HomologicalComplex.ιMapBifunctor P Q (tensor R₀) (.up ℤ) p q n h)) i j hij

private theorem total_map
    {P P' Q Q' : CochainComplex (Mod R₀) ℤ} (a : P ⟶ P') (b : Q ⟶ Q') :
    (total R₀).map (Prod.mkHom a b) =
      HomologicalComplex.mapBifunctorMap a b (tensor R₀) (.up ℤ) := by
  simp only [total, Functor.uncurry_obj_map, Functor.map₂HomologicalComplex,
    HomologicalComplex.mapBifunctorMap, ← HomologicalComplex₂.total.map_comp,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.comp_id, Category.id_comp]

private theorem total_summand_map
    {P P' Q Q' : CochainComplex (Mod R₀) ℤ} (a : P ⟶ P') (b : Q ⟶ Q')
    (p q n : ℤ) (hpq : p + q = n) :
    HomologicalComplex.ιMapBifunctor P Q (tensor R₀) (.up ℤ) p q n hpq ≫
        ((total R₀).map (Prod.mkHom a b)).f n =
      (Functor.uncurry.obj (tensor R₀)).map (Prod.mkHom (a.f p) (b.f q)) ≫
        HomologicalComplex.ιMapBifunctor P' Q' (tensor R₀) (.up ℤ) p q n hpq := by
  erw [total_map, HomologicalComplex.ι_mapBifunctorMap]
  simp only [Functor.uncurry_obj_map, Category.assoc]
  rfl

private theorem model_inverse
    {L : Mod R₀ ⥤ Mod R₁} [L.Additive] {d : PartialModel L}
    {a : TensorModel R₀} {b : TensorModel R₁}
    {mu : ∀ M N, L.obj (((tensor R₀).obj M).obj N) ≅
      ((tensor R₁).obj (L.obj M)).obj (L.obj N)}
    (t : PartialTensor L d a b mu)
    (P Q : CochainComplex (Mod R₀) ℤ) (hp : resolving R₀ P) (hq : resolving R₀ Q) :
    t.comparison.inv.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      d.functor.map (a.representative.inv.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
      d.factors.app ((total R₀).obj (P, Q)) =
    b.functor.map (Prod.mkHom (d.factors.app P) (d.factors.app Q)) ≫
      b.representative.inv.app
        (⟨(L.mapHomologicalComplex (.up ℤ)).obj P, t.preserves P hp⟩,
          ⟨(L.mapHomologicalComplex (.up ℤ)).obj Q, t.preserves Q hq⟩) ≫
      DerivedCategory.Q.map (chain t P Q) := by
  have h := t.representative P Q hp hq
  have he := congrArg (fun z ↦
    t.comparison.inv.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      d.functor.map (a.representative.inv.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫ z) h
  simp only [← d.functor.map_comp_assoc, Iso.inv_hom_id_app] at he
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc] at he
  simpa only [chain] using he.symm

@[irreducible] private def twoFactors
    {F : Mod R₀ ⥤ Mod R₁} [F.Additive] {G : Mod R₁ ⥤ Mod R₂} [G.Additive]
    (d : PartialModel F) (e : PartialModel G) (P : CochainComplex (Mod R₀) ℤ) :
    e.functor.obj (d.functor.obj (DerivedCategory.Q.obj P)) ⟶
      DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj P)) :=
  e.functor.map (d.factors.app P) ≫
    e.factors.app ((F.mapHomologicalComplex (.up ℤ)).obj P)

private theorem two_models
    {F : Mod R₀ ⥤ Mod R₁} [F.Additive] {G : Mod R₁ ⥤ Mod R₂} [G.Additive]
    {d : PartialModel F} {e : PartialModel G}
    {a : TensorModel R₀} {b : TensorModel R₁} {c : TensorModel R₂}
    {mu : ∀ M N, F.obj (((tensor R₀).obj M).obj N) ≅
      ((tensor R₁).obj (F.obj M)).obj (F.obj N)}
    {nu : ∀ M N, G.obj (((tensor R₁).obj M).obj N) ≅
      ((tensor R₂).obj (G.obj M)).obj (G.obj N)}
    (t : PartialTensor F d a b mu) (s : PartialTensor G e b c nu)
    (P Q : CochainComplex (Mod R₀) ℤ) (hp : resolving R₀ P) (hq : resolving R₀ Q) :
    s.comparison.inv.app (d.functor.obj (DerivedCategory.Q.obj P),
        d.functor.obj (DerivedCategory.Q.obj Q)) ≫
      e.functor.map (t.comparison.inv.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      e.functor.map (d.functor.map (a.representative.inv.app (⟨P, hp⟩, ⟨Q, hq⟩))) ≫
      (twoFactors d e ((total R₀).obj (P, Q))) =
    c.functor.map (Prod.mkHom (twoFactors d e P) (twoFactors d e Q)) ≫
      c.representative.inv.app
        (⟨(G.mapHomologicalComplex (.up ℤ)).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj P),
          s.preserves _ (t.preserves P hp)⟩,
        ⟨(G.mapHomologicalComplex (.up ℤ)).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj Q),
          s.preserves _ (t.preserves Q hq)⟩) ≫
      DerivedCategory.Q.map
        (chain s ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj Q) ≫
          (G.mapHomologicalComplex (.up ℤ)).map (chain t P Q)) := by
  let FP := (F.mapHomologicalComplex (.up ℤ)).obj P
  let FQ := (F.mapHomologicalComplex (.up ℤ)).obj Q
  have hF := model_inverse t P Q hp hq
  have hG := model_inverse s FP FQ (t.preserves P hp) (t.preserves Q hq)
  have hn := s.comparison.inv.naturality
    (Prod.mkHom (d.factors.app P) (d.factors.app Q))
  change c.functor.map (Prod.mkHom
      (e.functor.map (d.factors.app P)) (e.functor.map (d.factors.app Q))) ≫
      s.comparison.inv.app (DerivedCategory.Q.obj FP, DerivedCategory.Q.obj FQ) =
    s.comparison.inv.app (d.functor.obj (DerivedCategory.Q.obj P),
      d.functor.obj (DerivedCategory.Q.obj Q)) ≫
      e.functor.map (b.functor.map (Prod.mkHom
        (d.factors.app P) (d.factors.app Q))) at hn
  simp only [twoFactors]
  rw [← e.functor.map_comp_assoc, ← e.functor.map_comp_assoc]
  simp only [Category.assoc]
  rw [hF]
  simp only [e.functor.map_comp, Category.assoc]
  rw [← reassoc_of% hn]
  have hg := e.factors.naturality (chain t P Q)
  dsimp only [Functor.comp_map] at hg
  erw [hg]
  rw [reassoc_of% hG]
  simp only [← c.functor.map_comp_assoc, prod_comp, Functor.map_comp]
  rfl

set_option maxHeartbeats 600000 in
-- On each signed-total summand the square is the inverse ordinary tensor square.
private theorem total_square
    {C₃ : Type (u + 1)} [Category.{u} C₃] [EssentiallySmall.{u + 1} C₃]
    {J₃ : GrothendieckTopology C₃} {R₃ : Sheaf J₃ CommRingCat.{u + 1}}
    {F : Mod R₀ ⥤ Mod R₁} {G : Mod R₀ ⥤ Mod R₂}
    {H : Mod R₁ ⥤ Mod R₃} {K : Mod R₂ ⥤ Mod R₃}
    [F.Additive] [G.Additive] [H.Additive] [K.Additive]
    {dF : PartialModel F} {dG : PartialModel G} {dH : PartialModel H} {dK : PartialModel K}
    {a : TensorModel R₀} {b : TensorModel R₁} {c : TensorModel R₂}
    {d : TensorModel R₃}
    {muF : ∀ M N, F.obj (((tensor R₀).obj M).obj N) ≅
      ((tensor R₁).obj (F.obj M)).obj (F.obj N)}
    {muG : ∀ M N, G.obj (((tensor R₀).obj M).obj N) ≅
      ((tensor R₂).obj (G.obj M)).obj (G.obj N)}
    {muH : ∀ M N, H.obj (((tensor R₁).obj M).obj N) ≅
      ((tensor R₃).obj (H.obj M)).obj (H.obj N)}
    {muK : ∀ M N, K.obj (((tensor R₂).obj M).obj N) ≅
      ((tensor R₃).obj (K.obj M)).obj (K.obj N)}
    (tF : PartialTensor F dF a b muF) (tG : PartialTensor G dG a c muG)
    (tH : PartialTensor H dH b d muH) (tK : PartialTensor K dK c d muK)
    (gamma : G ⋙ K ⟶ F ⋙ H)
    (ho : ∀ M N,
      gamma.app (((tensor R₀).obj M).obj N) ≫ H.map (muF M N).hom ≫
          (muH (F.obj M) (F.obj N)).hom =
        K.map (muG M N).hom ≫ (muK (G.obj M) (G.obj N)).hom ≫
          (Functor.uncurry.obj (tensor R₃)).map (Prod.mkHom (gamma.app M) (gamma.app N)))
    (P Q : CochainComplex (Mod R₀) ℤ) :
    chain tK ((G.mapHomologicalComplex (.up ℤ)).obj P)
        ((G.mapHomologicalComplex (.up ℤ)).obj Q) ≫
      (K.mapHomologicalComplex (.up ℤ)).map (chain tG P Q) ≫
      (NatTrans.mapHomologicalComplex gamma (.up ℤ)).app ((total R₀).obj (P, Q)) =
    (total R₃).map (Prod.mkHom
        ((NatTrans.mapHomologicalComplex gamma (.up ℤ)).app P)
        ((NatTrans.mapHomologicalComplex gamma (.up ℤ)).app Q)) ≫
      chain tH ((F.mapHomologicalComplex (.up ℤ)).obj P)
        ((F.mapHomologicalComplex (.up ℤ)).obj Q) ≫
      (H.mapHomologicalComplex (.up ℤ)).map (chain tF P Q) := by
  let := SheafOfModules.monoidalCategory R₃
  let := d.preadditive
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  let GP := (G.mapHomologicalComplex (.up ℤ)).obj P
  let GQ := (G.mapHomologicalComplex (.up ℤ)).obj Q
  let FP := (F.mapHomologicalComplex (.up ℤ)).obj P
  let FQ := (F.mapHomologicalComplex (.up ℤ)).obj Q
  let i0 := HomologicalComplex.ιMapBifunctor P Q (tensor R₀) (.up ℤ) p q n hpq
  let iG := HomologicalComplex.ιMapBifunctor GP GQ (tensor R₂) (.up ℤ) p q n hpq
  let iF := HomologicalComplex.ιMapBifunctor FP FQ (tensor R₁) (.up ℤ) p q n hpq
  let iK := HomologicalComplex.ιMapBifunctor
    ((K.mapHomologicalComplex (.up ℤ)).obj GP)
    ((K.mapHomologicalComplex (.up ℤ)).obj GQ) (tensor R₃) (.up ℤ) p q n hpq
  let iH := HomologicalComplex.ιMapBifunctor
    ((H.mapHomologicalComplex (.up ℤ)).obj FP)
    ((H.mapHomologicalComplex (.up ℤ)).obj FQ) (tensor R₃) (.up ℤ) p q n hpq
  let chK := (chain tK GP GQ).f n
  let chG := (chain tG P Q).f n
  let chH := (chain tH FP FQ).f n
  let chF := (chain tF P Q).f n
  let muK' := muK (G.obj (P.X p)) (G.obj (Q.X q))
  let muG' := muG (P.X p) (Q.X q)
  let muH' := muH (F.obj (P.X p)) (F.obj (Q.X q))
  let muF' := muF (P.X p) (Q.X q)
  let dt := gamma.app (((total R₀).obj (P, Q)).X n)
  let dm := gamma.app (((tensor R₀).obj (P.X p)).obj (Q.X q))
  let beta := (Functor.uncurry.obj (tensor R₃)).map
    (Prod.mkHom (gamma.app (P.X p)) (gamma.app (Q.X q)))
  let dc := NatTrans.mapHomologicalComplex gamma (.up ℤ)
  let tm := ((total R₃).map (Prod.mkHom (dc.app P) (dc.app Q))).f n
  have hK : iK ≫ chK = muK'.inv ≫ K.map iG :=
    chain_summand tK GP GQ p q n hpq
  have hG : K.map iG ≫ K.map chG = K.map muG'.inv ≫ K.map (G.map i0) := by
    have h := congrArg K.map (chain_summand tG P Q p q n hpq)
    change K.map (iG ≫ chG) = K.map (muG'.inv ≫ G.map i0) at h
    exact (K.map_comp _ _).symm.trans (h.trans (K.map_comp _ _))
  have hH : iH ≫ chH = muH'.inv ≫ H.map iF :=
    chain_summand tH FP FQ p q n hpq
  have hF : H.map iF ≫ H.map chF = H.map muF'.inv ≫ H.map (F.map i0) := by
    have h := congrArg H.map (chain_summand tF P Q p q n hpq)
    change H.map (iF ≫ chF) = H.map (muF'.inv ≫ F.map i0) at h
    exact (H.map_comp _ _).symm.trans (h.trans (H.map_comp _ _))
  have hn : K.map (G.map i0) ≫ dt = dm ≫ H.map (F.map i0) :=
    gamma.naturality i0
  have hm : iK ≫ tm = beta ≫ iH := total_summand_map (dc.app P) (dc.app Q) p q n hpq
  have hl : iK ≫ chK ≫ K.map chG ≫ dt =
      muK'.inv ≫ K.map muG'.inv ≫ dm ≫ H.map (F.map i0) := by
    have h1 := congrArg (fun z ↦ z ≫ K.map chG ≫ dt) hK
    have h2 := congrArg (fun z ↦ muK'.inv ≫ z ≫ dt) hG
    have h3 := congrArg (fun z ↦ muK'.inv ≫ K.map muG'.inv ≫ z) hn
    repeat' erw [Category.assoc] at h1
    repeat' erw [Category.assoc] at h2
    exact h1.trans (h2.trans h3)
  have hr : iK ≫ tm ≫ chH ≫ H.map chF =
      beta ≫ muH'.inv ≫ H.map muF'.inv ≫ H.map (F.map i0) := by
    have h1 := congrArg (fun z ↦ z ≫ chH ≫ H.map chF) hm
    have h2 := congrArg (fun z ↦ beta ≫ z ≫ H.map chF) hH
    have h3 := congrArg (fun z ↦ beta ≫ muH'.inv ≫ z) hF
    repeat' erw [Category.assoc] at h1
    repeat' erw [Category.assoc] at h2
    exact h1.trans (h2.trans h3)
  let x := K.mapIso muG' ≪≫ muK'
  let y := H.mapIso muF' ≪≫ muH'
  have hi : x.inv ≫ dm = beta ≫ y.inv := by
    apply (Iso.inv_comp_eq x).2
    rw [← Category.assoc]
    apply (Iso.eq_comp_inv y).2
    exact ho _ _
  have h := congrArg (fun z ↦ z ≫ H.map (F.map i0)) hi
  simp only [x, y, Iso.trans_inv, Functor.mapIso_inv, Category.assoc] at h
  exact hl.trans (h.trans hr.symm)

set_option maxHeartbeats 600000 in
-- Keep the four-model calculation abstract, so its category algebra does not
-- unfold the concrete pro-étale pullbacks and restriction functors.
private theorem four_models_inverse
    {C₃ : Type (u + 1)} [Category.{u} C₃] [EssentiallySmall.{u + 1} C₃]
    {J₃ : GrothendieckTopology C₃} {R₃ : Sheaf J₃ CommRingCat.{u + 1}}
    {F : Mod R₀ ⥤ Mod R₁} {G : Mod R₀ ⥤ Mod R₂}
    {H : Mod R₁ ⥤ Mod R₃} {K : Mod R₂ ⥤ Mod R₃}
    [F.Additive] [G.Additive] [H.Additive] [K.Additive]
    {dF : PartialModel F} {dG : PartialModel G} {dH : PartialModel H} {dK : PartialModel K}
    {a : TensorModel R₀} {b : TensorModel R₁} {c : TensorModel R₂}
    {d : TensorModel R₃}
    {muF : ∀ M N, F.obj (((tensor R₀).obj M).obj N) ≅
      ((tensor R₁).obj (F.obj M)).obj (F.obj N)}
    {muG : ∀ M N, G.obj (((tensor R₀).obj M).obj N) ≅
      ((tensor R₂).obj (G.obj M)).obj (G.obj N)}
    {muH : ∀ M N, H.obj (((tensor R₁).obj M).obj N) ≅
      ((tensor R₃).obj (H.obj M)).obj (H.obj N)}
    {muK : ∀ M N, K.obj (((tensor R₂).obj M).obj N) ≅
      ((tensor R₃).obj (K.obj M)).obj (K.obj N)}
    (tF : PartialTensor F dF a b muF) (tG : PartialTensor G dG a c muG)
    (tH : PartialTensor H dH b d muH) (tK : PartialTensor K dK c d muK)
    (gamma : G ⋙ K ⟶ F ⋙ H)
    (ho : ∀ M N,
      gamma.app (((tensor R₀).obj M).obj N) ≫ H.map (muF M N).hom ≫
          (muH (F.obj M) (F.obj N)).hom =
        K.map (muG M N).hom ≫ (muK (G.obj M) (G.obj N)).hom ≫
          (Functor.uncurry.obj (tensor R₃)).map (Prod.mkHom (gamma.app M) (gamma.app N)))
    (theta : dG.functor ⋙ dK.functor ⟶ dF.functor ⋙ dH.functor)
    (hnorm : ∀ (P : CochainComplex (Mod R₀) ℤ), resolving R₀ P →
      theta.app (DerivedCategory.Q.obj P) ≫ (twoFactors dF dH P) =
        (twoFactors dG dK P) ≫ DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex gamma (.up ℤ)).app P))
    (P Q : CochainComplex (Mod R₀) ℤ) (hp : resolving R₀ P) (hq : resolving R₀ Q)
    (hTot : resolving R₀ ((total R₀).obj (P, Q))) :
    d.functor.map (Prod.mkHom (theta.app (DerivedCategory.Q.obj P))
        (theta.app (DerivedCategory.Q.obj Q))) ≫
      tH.comparison.inv.app (dF.functor.obj (DerivedCategory.Q.obj P),
        dF.functor.obj (DerivedCategory.Q.obj Q)) ≫
      dH.functor.map (tF.comparison.inv.app (DerivedCategory.Q.obj P,
        DerivedCategory.Q.obj Q)) =
    tK.comparison.inv.app (dG.functor.obj (DerivedCategory.Q.obj P),
        dG.functor.obj (DerivedCategory.Q.obj Q)) ≫
      dK.functor.map (tG.comparison.inv.app (DerivedCategory.Q.obj P,
        DerivedCategory.Q.obj Q)) ≫
      theta.app (a.functor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) := by
  let D := d.functor
  let gammaC := NatTrans.mapHomologicalComplex gamma (.up ℤ)
  let FP := (F.mapHomologicalComplex (.up ℤ)).obj P
  let FQ := (F.mapHomologicalComplex (.up ℤ)).obj Q
  let GP := (G.mapHomologicalComplex (.up ℤ)).obj P
  let GQ := (G.mapHomologicalComplex (.up ℤ)).obj Q
  let HFP := (H.mapHomologicalComplex (.up ℤ)).obj FP
  let HFQ := (H.mapHomologicalComplex (.up ℤ)).obj FQ
  let KGP := (K.mapHomologicalComplex (.up ℤ)).obj GP
  let KGQ := (K.mapHomologicalComplex (.up ℤ)).obj GQ
  let Tot := (total R₀).obj (P, Q)
  let bGK := twoFactors dG dK
  let bFH := twoFactors dF dH
  let r0 := a.representative.app (⟨P, hp⟩, ⟨Q, hq⟩)
  let rGK := d.representative.app
    (⟨KGP, tK.preserves _ (tG.preserves P hp)⟩,
      ⟨KGQ, tK.preserves _ (tG.preserves Q hq)⟩)
  let rFH := d.representative.app
    (⟨HFP, tH.preserves _ (tF.preserves P hp)⟩,
      ⟨HFQ, tH.preserves _ (tF.preserves Q hq)⟩)
  let cGK := chain tK GP GQ ≫
    (K.mapHomologicalComplex (.up ℤ)).map (chain tG P Q)
  let cFH := chain tH FP FQ ≫
    (H.mapHomologicalComplex (.up ℤ)).map (chain tF P Q)
  have hGK := two_models tG tK P Q hp hq
  have hFH := two_models tF tH P Q hp hq
  change _ = D.map (Prod.mkHom (bGK P) (bGK Q)) ≫
    rGK.inv ≫ DerivedCategory.Q.map cGK at hGK
  change _ = D.map (Prod.mkHom (bFH P) (bFH Q)) ≫
    rFH.inv ≫ DerivedCategory.Q.map cFH at hFH
  have hp' := hnorm P hp
  have hq' := hnorm Q hq
  have ht := hnorm Tot hTot
  have hn := d.representative.hom.naturality
    (Prod.mkHom
      (ObjectProperty.homMk
        (X := ⟨KGP, tK.preserves _ (tG.preserves P hp)⟩)
        (Y := ⟨HFP, tH.preserves _ (tF.preserves P hp)⟩)
        (gammaC.app P))
      (ObjectProperty.homMk
        (X := ⟨KGQ, tK.preserves _ (tG.preserves Q hq)⟩)
        (Y := ⟨HFQ, tH.preserves _ (tF.preserves Q hq)⟩)
        (gammaC.app Q)))
  change DerivedCategory.Q.map
      ((total R₃).map
        (Prod.mkHom (gammaC.app P) (gammaC.app Q))) ≫ rFH.hom =
    rGK.hom ≫ D.map (Prod.mkHom (DerivedCategory.Q.map (gammaC.app P))
      (DerivedCategory.Q.map (gammaC.app Q))) at hn
  have hinv := congrArg (fun z ↦ rGK.inv ≫ z ≫ rFH.inv) hn
  repeat' erw [Category.assoc] at hinv
  erw [Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc] at hinv
  have hc := total_square tF tG tH tK gamma ho P Q
  change cGK ≫ gammaC.app Tot =
    (total R₃).map
      (Prod.mkHom (gammaC.app P) (gammaC.app Q)) ≫ cFH at hc
  have := dF.flat Tot hTot
  have := dH.flat _ (tF.preserves Tot hTot)
  let z := dH.functor.map (dF.functor.map r0.inv) ≫ bFH Tot
  have : IsIso z := by
    unfold z bFH twoFactors
    infer_instance
  apply (cancel_mono z).1
  simp only [z, Category.assoc]
  have htheta := theta.naturality r0.inv
  change dK.functor.map (dG.functor.map r0.inv) ≫
      theta.app (DerivedCategory.Q.obj Tot) =
    theta.app (a.functor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      dH.functor.map (dF.functor.map r0.inv) at htheta
  erw [← reassoc_of% htheta]
  erw [ht]
  erw [reassoc_of% hGK]
  erw [hFH]
  rw [← D.map_comp_assoc]
  simp only [prod_comp]
  erw [hp', hq']
  erw [← prod_comp (Prod.mkHom (bGK P) (bGK Q))
    (Prod.mkHom (DerivedCategory.Q.map (gammaC.app P))
      (DerivedCategory.Q.map (gammaC.app Q))), D.map_comp]
  simp only [Category.assoc]
  have hi := congrArg (fun z ↦ D.map (Prod.mkHom (bGK P) (bGK Q)) ≫ z ≫
    DerivedCategory.Q.map cFH) hinv.symm
  repeat' erw [Category.assoc] at hi
  have hQ := (DerivedCategory.Q.map_comp cGK (gammaC.app Tot)).symm.trans
    ((congrArg DerivedCategory.Q.map hc).trans
      (DerivedCategory.Q.map_comp
        ((total R₃).map (Prod.mkHom (gammaC.app P) (gammaC.app Q))) cFH))
  exact hi.trans (congrArg (fun z ↦
    D.map (Prod.mkHom (bGK P) (bGK Q)) ≫ rGK.inv ≫ z) hQ.symm)

end Representatives
section ModelSpecialization

variable {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
  [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {R : Sheaf J CommRingCat.{u + 1}} {S : Sheaf K CommRingCat.{u + 1}}

private def exactPartial {L : Mod R ⥤ Mod S} [L.Additive] (e : ExactModel L) :
    PartialModel L where
  functor := e.functor
  factors := e.factors.hom
  flat := fun _ _ ↦ inferInstance

private def pullPartial {V : Mod S ⥤ Mod R} (p : Pullback R S V) :
    PartialModel p.ordinary where
  functor := p.derived
  factors :=
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso (Mod R)).inv p.derived ≫
      Functor.whiskerLeft (HomotopyCategory.quotient (Mod R) (.up ℤ)) p.epsilon ≫
      Functor.whiskerRight (p.ordinary.mapHomotopyCategoryFactors (.up ℤ)).hom
        DerivedCategory.Qh ≫
      Functor.whiskerLeft (p.ordinary.mapHomologicalComplex (.up ℤ))
        (DerivedCategory.quotientCompQhIso (Mod S)).hom
  flat := p.flat

private def exactTensorPartial {L : Mod R ⥤ Mod S} [L.Additive] {e : ExactModel L}
    {a : TensorModel R} {b : TensorModel S}
    {mu : ∀ M N, L.obj (((tensor R).obj M).obj N) ≅
      ((tensor S).obj (L.obj M)).obj (L.obj N)}
    (v : TensorComparison L e a b mu) : PartialTensor L (exactPartial e) a b mu where
  preserves := v.preserves
  comparison := v.comparison
  comm := v.comm
  representative := v.representative

private theorem resolving_total (R : Sheaf J CommRingCat.{u + 1})
    (P Q : CochainComplex (Mod R) ℤ) (hp : resolving R P) (hq : resolving R Q) :
    resolving R ((total R).obj (P, Q)) := by
  have h := SheafOfModules.KFlatTotalTensorModel.kFlat_total_tensor_model
    R P Q hp.1 hq.1 hp.2 hq.2
  exact ⟨h.1, h.2.1⟩

end ModelSpecialization

private def pullTensorPartial {m : Mode} {X Y : Scheme.{u}} {f : X ⟶ Y}
    {R : Sheaf (topology m Y) CommRingCat.{u + 1}}
    {S : Sheaf (topology m X) CommRingCat.{u + 1}}
    {c : R ⟶ ((baseChange m f).sheafPushforwardContinuous CommRingCat.{u + 1}
      (topology m Y) (topology m X)).obj S}
    {p : Pullback R S (direct m f R S c)} {a : TensorModel R} {b : TensorModel S}
    (v : PullTensor m f R S c p a b) :
    PartialTensor p.ordinary (pullPartial p) a b v.ordinary where
  preserves := v.preserves
  comparison := v.comparison
  comm := v.comm
  representative := v.representative

set_option maxHeartbeats 800000 in
-- Specialize four resolving models without unfolding the concrete derived pullbacks.
private theorem inverse_on_representatives {m : Mode} {d : Input.{u} m}
    {t : SiteSquare d} {o : Operations d t} {A : Scheme.{u}}
    {s : A ⟶ d.U'} [IsOpenImmersion s] (v : Data o s)
    (P Q : CochainComplex (Mod d.R) ℤ) (hp : resolving d.R P) (hq : resolving d.R Q) :
    o.tensorU'.functor.map (Prod.mkHom (o.theta.inv.app (DerivedCategory.Q.obj P))
        (o.theta.inv.app (DerivedCategory.Q.obj Q))) ≫
      v.tensorB.tensorComparison.comparison.inv.app
        (o.gPull.derived.obj (DerivedCategory.Q.obj P),
          o.gPull.derived.obj (DerivedCategory.Q.obj Q)) ≫
      o.opens.jStar'.map
        (v.tensorP.comparison.inv.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) =
    v.tensorQ.comparison.inv.app (o.opens.jStar.obj (DerivedCategory.Q.obj P),
        o.opens.jStar.obj (DerivedCategory.Q.obj Q)) ≫
      o.gUPull.derived.map
        (o.tensorComparison.comparison.inv.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      o.theta.inv.app
        (o.tensorX.functor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) := by
  apply four_models_inverse (pullTensorPartial v.tensorP)
    (exactTensorPartial o.tensorComparison) (exactTensorPartial v.tensorB.tensorComparison)
    (pullTensorPartial v.tensorQ) o.ordinaryTheta.inv (ordinary_tensor_square v)
    o.theta.inv ?_ P Q hp hq (resolving_total d.R P Q hp hq)
  intro T hT
  unfold twoFactors
  change o.theta.inv.app (DerivedCategory.Q.obj T) ≫
      o.opens.jStar'.map (derivedPullbackComplexComparison
        o.gPull.ordinary o.gPull.derived o.gPull.epsilon T) ≫
      (restrict m d.j' d.S).mapDerivedCategoryFactors.hom.app
        ((o.gPull.ordinary.mapHomologicalComplex (.up ℤ)).obj T) =
    (o.gUPull.derived.map ((restrict m d.j d.R).mapDerivedCategoryFactors.hom.app T) ≫
      derivedPullbackComplexComparison o.gUPull.ordinary o.gUPull.derived o.gUPull.epsilon
        (((restrict m d.j d.R).mapHomologicalComplex (.up ℤ)).obj T)) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex o.ordinaryTheta.inv (.up ℤ)).app T)
  let e := DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex
    o.ordinaryTheta (.up ℤ)).app T)
  apply (Iso.inv_comp_eq (o.theta.app (DerivedCategory.Q.obj T))).2
  erw [← Category.assoc]
  apply (Iso.eq_comp_inv e).2
  exact (Category.assoc _ _ _).trans (o.theta_model T hT).symm

/-- The normalized Cartesian pullback compositor is compatible with the two
derived tensor comparisons after restriction to an arbitrary open immersion.

Source: `literature/stacks-project/sites-cohomology.tex`, Tags 07A4
(`lemma-pullback-tensor-product`) and 0D6D (`lemma-derived-pullback-composition`),
with the clopen tensor refinement (blueprint:
`lem-sf-clopen-pullback-tensor-compatibility`).

Proof plan: on flat-term K-flat representatives, use the representative
equations for the pullback and open tensor comparisons together with the
normalized compositor.  After cancellation, both composites are the same
ordinary tensor square; the equality follows on pure tensors from the
adjunction-mate normalization and the pure-unit formulas.  Sheafification and
balancing extend this to module-sheaf maps, and the signed total differentials
agree without interchanging degrees.  Two-variable resolving descent then
extends the equality to arbitrary unbounded derived objects.
-/
theorem pullback_tensor_compatibility {m : Mode} {d : Input.{u} m} {t : SiteSquare d}
    {o : Operations d t} (_a : Assertion o) {A : Scheme.{u}}
    {s : A ⟶ d.U'} [IsOpenImmersion s] (v : Data o s)
    (X Y : Der d.R) :
    o.gUPull.derived.map (o.tensorComparison.comparison.inv.app (X, Y)) ≫
        o.theta.inv.app (o.tensorX.functor.obj (X, Y)) ≫
        o.opens.jStar'.map (v.tensorP.comparison.hom.app (X, Y)) =
      v.tensorQ.comparison.hom.app (o.opens.jStar.obj X, o.opens.jStar.obj Y) ≫
        o.tensorU'.functor.map
          (Prod.mkHom (o.theta.inv.app X) (o.theta.inv.app Y)) ≫
        v.tensorB.tensorComparison.comparison.inv.app
          (o.gPull.derived.obj X, o.gPull.derived.obj Y) := by
  let F := o.gPull.derived
  let G := o.opens.jStar
  let H := o.opens.jStar'
  let K := o.gUPull.derived
  let T := o.tensorX.functor
  let D := o.tensorU'.functor
  let tF := v.tensorP.comparison
  let tG := o.tensorComparison.comparison
  let tH := v.tensorB.tensorComparison.comparison
  let tK := v.tensorQ.comparison
  let theta := o.theta.inv
  let a : (G.prod G) ⋙ (K.prod K) ⋙ D ⟶ T ⋙ F ⋙ H :=
    Functor.whiskerRight (theta.prod theta) D ≫
      Functor.whiskerLeft (F.prod F) tH.inv ≫ Functor.whiskerRight tF.inv H
  let b : (G.prod G) ⋙ (K.prod K) ⋙ D ⟶ T ⋙ F ⋙ H :=
    Functor.whiskerLeft (G.prod G) tK.inv ≫ Functor.whiskerRight tG.inv K ≫
      Functor.whiskerLeft T theta
  have he : a = b := by
    obtain ⟨_, _, _, hd⟩ := SheafOfModules.cochain_tensor_model_rigidity
      (topology m d.X) d.R
    apply (hd (Der (restrictRing m d.j' d.S)) inferInstance _ _).1
    apply NatTrans.ext
    funext Z
    rcases Z with ⟨P, Q⟩
    exact inverse_on_representatives v P.obj Q.obj P.property Q.property
  have hi := congrArg (fun t ↦ t.app (X, Y)) he
  change D.map (Prod.mkHom (theta.app X) (theta.app Y)) ≫
      tH.inv.app (F.obj X, F.obj Y) ≫ H.map (tF.inv.app (X, Y)) =
    tK.inv.app (G.obj X, G.obj Y) ≫ K.map (tG.inv.app (X, Y)) ≫
      theta.app (T.obj (X, Y)) at hi
  have move {A B C E : Der (restrictRing m d.j' d.S)}
      (f : A ⟶ B) (i : C ≅ B) (j : E ≅ A) (g : E ⟶ C)
      (h : f ≫ i.inv = j.inv ≫ g) : g ≫ i.hom = j.hom ≫ f := by
    symm
    apply (Iso.comp_inv_eq i).1
    rw [Category.assoc, h, Iso.hom_inv_id_assoc]
  have h := move
    (D.map (Prod.mkHom (theta.app X) (theta.app Y)) ≫ tH.inv.app (F.obj X, F.obj Y))
    (H.mapIso (tF.app (X, Y))) (tK.app (G.obj X, G.obj Y))
    (K.map (tG.inv.app (X, Y)) ≫ theta.app (T.obj (X, Y)))
    ((Category.assoc _ _ _).trans hi)
  exact (Category.assoc _ _ _).symm.trans h


end SheafOfModules.ClopenComparisonTensorSquare
