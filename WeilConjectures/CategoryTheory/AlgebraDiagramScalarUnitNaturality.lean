/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.AlgebraDiagramPullbackData
import all Mathlib.CategoryTheory.Limits.HasLimits
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import all WeilConjectures.AlgebraicGeometry.KFlatScalarComparisonNormalization
import all WeilConjectures.AlgebraicGeometry.PullbackTensorCanonicalShiftUnit
import all WeilConjectures.Algebra.Homology.RingedKFlatSingleTensorComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Localization.Construction
import all Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import all Mathlib.CategoryTheory.Functor.Currying
import all Mathlib.CategoryTheory.Whiskering
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all Mathlib.CategoryTheory.Localization.Prod
import all Mathlib.Algebra.Homology.BifunctorFlip
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all Mathlib.CategoryTheory.Localization.CalculusOfFractions
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulatedSupplement
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import all WeilConjectures.Algebra.Homology.PrincipalKoszulQuotientTowersSupplement

/-! # Units and coefficient maps of normalized scalar presentations

Source: Stacks 03CY, 06YU and 07A4.
(blueprint: lem-pur-algebra-diagram-scalar-unit-naturality).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
attribute [local instance 100000] CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize
set_option synthInstance.maxSize 4096

universe u w v v' v'' u' u''
open CategoryTheory CategoryTheory.Limits CategoryTheory.CochainPullback
open scoped ZeroObject
namespace CategoryTheory.AlgebraDiagramPullback
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {K : GrothendieckTopology C} {L : GrothendieckTopology D}
  {R : Sheaf K CommRingCat.{u}} {S : Sheaf L CommRingCat.{u}}

open MonoidalCategory
open SheafOfModules.KFlatFixedTensor hiding Modules
open SheafOfModules.PullbackTensorCanonical
attribute [local irreducible] DerivedCategory.Q
attribute [local irreducible] Functor.curry SheafOfModules.monoidalCategory
attribute [local instance] SheafOfModules.monoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private theorem unit_transport
    {A : Type u} [Category.{v} A]
    {M X X' Y Y' Z Z' W W' : A}
    (a : X ≅ Y) (a' : X' ≅ Y')
    (c : Y ≅ Z) (c' : Y' ≅ Z')
    (o : Z ≅ W) (o' : Z' ≅ W')
    (h : X ≅ W) (h' : X' ≅ W')
    (f : Y ⟶ Y') (g : Z ⟶ Z')
    (u : M ⟶ X) (u' : M ⟶ X') (v : M ⟶ W) (v' : M ⟶ W')
    (ha : a.inv ≫ h.hom = c.hom ≫ o.hom)
    (ha' : a'.inv ≫ h'.hom = c'.hom ≫ o'.hom)
    (hn : f ≫ c'.hom = c.hom ≫ g)
    (hu : u ≫ h.hom = v) (hu' : u' ≫ h'.hom = v')
    (hv : v ≫ o.inv ≫ g ≫ o'.hom = v') :
    u ≫ a.hom ≫ f ≫ a'.inv = u' := by
  apply (cancel_mono h'.hom).mp
  simp only [Category.assoc]
  rw [ha', ← Category.assoc f, hn]
  have hh : a.hom ≫ c.hom = h.hom ≫ o.inv := by
    apply (cancel_mono o.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← ha, Iso.hom_inv_id_assoc]
  calc
    _ = u ≫ (a.hom ≫ c.hom) ≫ g ≫ o'.hom := by simp only [Category.assoc]
    _ = u ≫ (h.hom ≫ o.inv) ≫ g ≫ o'.hom := by rw [hh]
    _ = (u ≫ h.hom) ≫ o.inv ≫ g ≫ o'.hom := by simp only [Category.assoc]
    _ = v' := by rw [hu]; exact hv
    _ = u' ≫ h'.hom := hu'.symm
variable {B : Sheaf K CommRingCat.{u}}
private theorem scalar_tensor_unit_natural
    {B' : Sheaf K CommRingCat.{u}} (a : R ⟶ B) (a' : R ⟶ B')
    (t : ScalarTensorPresentation a) (t' : ScalarTensorPresentation a')
    (psi : B ⟶ B') (h : coefficient a ⟶ coefficient a')
    (hh : ∀ (V : Cᵒᵖ) (b : B.obj.obj V), h.val.app V b = psi.hom.app V b)
    (M : Modules.{u, u, u} R) :
    (extensionAdjunction.{u, u, u} a).unit.app M ≫
      t.iso.inv.app M ≫ ((curriedTensor (Modules.{u, u, u} R)).flip.map h).app M ≫
        t'.iso.hom.app M = (extensionAdjunction.{u, u, u} a').unit.app M := by
  have hu (a : R ⟶ B) (t : ScalarTensorPresentation a) (V : Cᵒᵖ)
      (x : M.val.obj V) :
      (t.iso.inv.app M).val.app V
        (((extensionAdjunction.{u, u, u} a).unit.app M).val.app V x) =
      moduleTmul M (coefficient a) V x (1 : B.obj.obj V) := by
    have ht := t.pure M V x 1
    have he := (Classical.choose_spec (extensionAdjunction_existsUnique a)).1 M V x
    rw [← he] at ht
    have hz := congrArg (fun z ↦ (t.iso.inv.app M).val.app V z) ht
    have hi := congrArg (fun z ↦ z.val.app V (moduleTmul M (coefficient a) V x (1 : B.obj.obj V)))
      (t.iso.hom_inv_id_app M)
    exact hz.symm.trans hi
  ext V x
  change (t'.iso.hom.app M).val.app V
    ((((curriedTensor (Modules.{u, u, u} R)).flip.map h).app M).val.app V
      ((t.iso.inv.app M).val.app V
        (((extensionAdjunction.{u, u, u} a).unit.app M).val.app V x))) = _
  rw [hu]
  change (t'.iso.hom.app M).val.app V
    ((M ◁ h).val.app V (moduleTmul M (coefficient a) V x (1 : B.obj.obj V))) = _
  have hm := moduleTmul_map (𝟙 M) h V x (1 : B.obj.obj V)
  simp only [id_tensorHom, SheafOfModules.id_val, PresheafOfModules.id_app,
    ModuleCat.id_apply] at hm
  erw [hm]
  change (t'.iso.hom.app M).val.app V
    (moduleTmul M (coefficient a') V x (h.val.app V (1 : B.obj.obj V))) = _
  rw [hh, map_one]
  exact (t'.pure M V x 1).trans
    ((Classical.choose_spec (extensionAdjunction_existsUnique a')).1 M V x).symm

variable {B : Sheaf K CommRingCat.{u}} (a : R ⟶ B)
  [HasDerivedCategory.{w} (Modules.{u, u, u} R)]
  [HasDerivedCategory.{w} (Modules.{u, u, u} B)] [ExactRestriction a]
private def scalarEvaluation
    (s : ScalarDerivedPresentation.{u, w} a)
    (P : CategoryTheory.CochainPullback.Complex.{u, u, u} R)
    (hp : P.IsKFlatIndependentCoefficients) :
    (restrictionFunctor.{u, u, u, u} a).mapDerivedCategory.{w, w}.obj
      (s.model.T.obj (DerivedCategory.Q.{w}.obj P)) ≅
    DerivedCategory.Q.{w}.obj ((restrictComplex a).obj ((extend a).obj P)) := by
  have := s.model.computes P hp
  exact (restrictionFunctor.{u, u, u, u} a).mapDerivedCategory.{w, w}.mapIso
      (asIso (s.model.ε.app P)) ≪≫
    (restrictionFunctor.{u, u, u, u} a).mapDerivedCategoryFactors.{w, w}.app
      ((s.model.E.mapHomologicalComplex (.up ℤ)).obj P) ≪≫
    DerivedCategory.Q.{w}.mapIso ((restrictComplex a).mapIso
      ((NatIso.mapHomologicalComplex s.ordinary (.up ℤ)).app P))

private def ordinaryScalarTotal (t : ScalarTensorPresentation a)
    (P : CategoryTheory.CochainPullback.Complex.{u, u, u} R) :
    ((((curriedTensor (Modules.{u, u, u} R)).flip.obj (coefficient a)).mapHomologicalComplex
      (.up ℤ)).obj P) ≅ (restrictComplex a).obj ((extend a).obj P) :=
  (NatIso.mapHomologicalComplex t.iso (.up ℤ)).app P ≪≫
    ((Functor.mapHomologicalComplexCompIso
      (Iso.refl (extensionFunctor.{u, u, u} a ⋙ restrictionFunctor.{u, u, u, u} a))
        (.up ℤ)).app P).symm

private theorem normalized_underlying_computes
    (s : ScalarDerivedPresentation.{u, w} a)
    (P Q : CategoryTheory.CochainPullback.Complex.{u, u, u} R)
    (hp : P.IsKFlatIndependentCoefficients) (hq : Q.IsKFlatIndependentCoefficients)
    (hf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := K) (R := R) (P.X n))
    (hg : ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := K) (R := R) (Q.X n))
    (q : Q ⟶ coefficientComplex a) (hqi : QuasiIso q)
    (c : ((canonicalDerivedTensor.{u, u, u, w} R).obj (DerivedCategory.Q.{w}.obj P)).obj
        (DerivedCategory.Q.{w}.obj (coefficientComplex a)) ≅
      DerivedCategory.Q.{w}.obj
        ((((curriedTensor (Modules.{u, u, u} R)).flip.obj (coefficient a)).mapHomologicalComplex
          (.up ℤ)).obj P))
    (hc : (canonicalRepresentativeIso.{u, u, u, w} R P Q hp hq hf hg).hom ≫
      (Functor.uncurry.obj (canonicalDerivedTensor.{u, u, u, w} R)).map
        (Prod.mkHom (𝟙 (DerivedCategory.Q.{w}.obj P)) (DerivedCategory.Q.{w}.map q)) ≫ c.hom =
      DerivedCategory.Q.{w}.map (((totalTensor R).obj P).map q ≫
        (CochainComplex.mapBifunctorSingle₂Iso (ordinaryTensor R) (coefficient a) P).hom)) :
    s.underlyingIso.inv.app (DerivedCategory.Q.{w}.obj P) ≫ (scalarEvaluation a s P hp).hom =
      c.hom ≫ DerivedCategory.Q.{w}.map (ordinaryScalarTotal a s.tensor P).hom := by
  have := hqi
  let j := (canonicalRepresentativeIso.{u, u, u, w} R P Q hp hq hf hg).hom ≫
    (Functor.uncurry.obj (canonicalDerivedTensor.{u, u, u, w} R)).map
      (Prod.mkHom (𝟙 (DerivedCategory.Q.{w}.obj P)) (DerivedCategory.Q.{w}.map q))
  have hj : IsIso j := by
    dsimp only [j, Functor.uncurry_obj_map]
    infer_instance
  apply (cancel_epi j).mp
  dsimp only [j, canonicalRepresentativeIso, canonicalDerivedTensor, scalarTensorFunctor] at *
  have hs := s.tensor_model P Q hp hq hf hg q hqi
  simp only [scalarTensorComparison, Iso.refl_inv, NatTrans.id_app,
    Category.id_comp, Category.comp_id] at hs
  dsimp only [scalarEvaluation]
  simp only [Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Iso.app_hom, Category.assoc]
  have hs' : (representativeIso.{u, u, u, w} R P Q hp hq hf hg).hom ≫
      (Functor.uncurry.obj (derivedTensor.{u, u, u, w} R)).map
        (Prod.mkHom (𝟙 (DerivedCategory.Q.{w}.obj P)) (DerivedCategory.Q.{w}.map q)) ≫
      s.underlyingIso.inv.app (DerivedCategory.Q.{w}.obj P) ≫
      (restrictionFunctor a).mapDerivedCategory.{w, w}.map (s.model.ε.app P) ≫
      (restrictionFunctor a).mapDerivedCategoryFactors.{w, w}.hom.app
        ((s.model.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.{w}.map ((restrictComplex a).map
        ((NatIso.mapHomologicalComplex s.ordinary (.up ℤ)).hom.app P)) =
      DerivedCategory.Q.{w}.map (((totalTensor R).obj P).map q ≫
        (s.tensor.total P).hom) := by
    repeat' erw [Category.id_comp] at hs
    simpa only [scalarTensorFunctor, canonicalDerivedTensor,
      canonicalRepresentativeIso, Category.id_comp, Category.assoc] using hs
  calc
    _ = DerivedCategory.Q.{w}.map (((totalTensor R).obj P).map q ≫
        (s.tensor.total P).hom) := hs'
    _ = DerivedCategory.Q.{w}.map (((totalTensor R).obj P).map q ≫
        (CochainComplex.mapBifunctorSingle₂Iso (ordinaryTensor R)
          (coefficient a) P).hom) ≫
        DerivedCategory.Q.{w}.map (ordinaryScalarTotal a s.tensor P).hom := by
      rw [← DerivedCategory.Q.{w}.map_comp]
      congr 1
    _ = ((representativeIso.{u, u, u, w} R P Q hp hq hf hg).hom ≫
        (Functor.uncurry.obj (derivedTensor.{u, u, u, w} R)).map
          (Prod.mkHom (𝟙 (DerivedCategory.Q.{w}.obj P)) (DerivedCategory.Q.{w}.map q)) ≫ c.hom) ≫
        DerivedCategory.Q.{w}.map (ordinaryScalarTotal a s.tensor P).hom := by rw [hc]
    _ = _ := by simp only [Category.assoc]

/-- Scalar units are natural under the actual coefficient module map. The
normalized tensor comparison is natural in its degree-zero factor; conjugating
that square by the ordinary tensor presentations reduces the assertion to
preservation of one. Source: Stacks 03EL and 07A4
(blueprint: lem-pur-algebra-diagram-scalar-unit-naturality). -/
theorem scalar_unit_natural
    {B' : Sheaf K CommRingCat.{u}} (a' : R ⟶ B')
    [HasDerivedCategory.{w} (Modules.{u, u, u} B')] [ExactRestriction a']
    (s : ScalarDerivedPresentation.{u, w} a) (t : ScalarDerivedPresentation.{u, w} a')
    (psi : B ⟶ B') (h : coefficient a ⟶ coefficient a')
    (hh : ∀ (V : Cᵒᵖ) (b : B.obj.obj V), h.val.app V b = psi.hom.app V b)
    (M : DerivedCategory (Modules.{u, u, u} R)) :
    s.adj.unit.app M ≫ (scalarUnderlyingMap s t h).app M = t.adj.unit.app M := by
  have he : s.adj.unit ≫ scalarUnderlyingMap s t h = t.adj.unit := by
    apply derivedNatTrans_ext (R := R) (S := R)
    intro P hp hf
    obtain ⟨c, ⟨hn, hc⟩, _⟩ := SheafOfModules.ringed_kFlat_single_tensor_comparison R
    dsimp only [canonicalDerivedTensor, canonicalRepresentativeIso] at *
    have computes {B₀ : Sheaf K CommRingCat.{u}} (a₀ : R ⟶ B₀)
        [HasDerivedCategory.{w} (Modules.{u, u, u} B₀)] [ExactRestriction a₀]
        (s₀ : ScalarDerivedPresentation.{u, w} a₀) :
        s₀.underlyingIso.inv.app (DerivedCategory.Q.{w}.obj P) ≫
          (scalarEvaluation a₀ s₀ P hp).hom =
        (c P hp (coefficient a₀)).hom ≫
          DerivedCategory.Q.{w}.map (ordinaryScalarTotal a₀ s₀.tensor P).hom := by
      obtain ⟨Q, q,⟨hq, hg⟩,hqi⟩ := exists_resolving (R := R) (coefficientComplex a₀)
      apply normalized_underlying_computes a₀ s₀ P Q hp hq hf hg q hqi
      have hc' := hc P hp (coefficient a₀) P Q hp hq hf hg (𝟙 P) q
        (by infer_instance) hqi
      simpa only [canonicalDerivedTensor, canonicalRepresentativeIso,
        Functor.map_id, NatTrans.id_app, Category.id_comp,
        Category.comp_id, Category.assoc, Functor.uncurry_obj_map] using hc'
    let f := ((canonicalDerivedTensor.{u, u, u, w} R).obj (DerivedCategory.Q.{w}.obj P)).map
      (DerivedCategory.Q.{w}.map ((HomologicalComplex.single (Modules.{u, u, u} R)
        (.up ℤ) 0).map h))
    let g := DerivedCategory.Q.{w}.map ((NatTrans.mapHomologicalComplex
      ((curriedTensor (Modules.{u, u, u} R)).flip.map h) (.up ℤ)).app P)
    have hn' : f ≫ (c P hp (coefficient a')).hom =
        (c P hp (coefficient a)).hom ≫ g := by
      simpa only [f, g, ordinaryTensor, canonicalDerivedTensor, canonicalRepresentativeIso,
        Functor.map_id, NatTrans.id_app, Category.id_comp, Category.comp_id] using
          hn P P hp hp (coefficient a) (coefficient a') (𝟙 P) h
    have hv : DerivedCategory.Q.{w}.map ((scalarCochainUnit a).app P) ≫
        (DerivedCategory.Q.{w}.mapIso (ordinaryScalarTotal a s.tensor P)).inv ≫ g ≫
        (DerivedCategory.Q.{w}.mapIso (ordinaryScalarTotal a' t.tensor P)).hom =
      DerivedCategory.Q.{w}.map ((scalarCochainUnit a').app P) := by
      simp only [Functor.mapIso_inv, Functor.mapIso_hom]
      rw [← DerivedCategory.Q.{w}.map_comp, ← DerivedCategory.Q.{w}.map_comp,
        ← DerivedCategory.Q.{w}.map_comp]
      congr 1
      ext n : 1
      simp only [scalarCochainUnit, ordinaryScalarTotal, g,
        Functor.mapHomologicalComplexCompIso, Iso.trans_hom, Iso.trans_inv,
        Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv,
        NatTrans.comp_app, HomologicalComplex.comp_f,
        Functor.mapHomologicalComplexIdIso_inv_app_f,
        NatIso.mapHomologicalComplex_inv_app_f, NatIso.mapHomologicalComplex_hom_app_f,
        Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
        NatTrans.mapHomologicalComplex_app_f, Category.id_comp, Category.comp_id]
      dsimp only [Functor.mapHomologicalComplex, Iso.app, Iso.symm, Iso.trans,
        NatTrans.vcomp, NatTrans.id, NatTrans.mapHomologicalComplex,
        HomologicalComplex.Hom.isoOfComponents, NatIso.ofComponents]
      simp only [Category.id_comp, Category.comp_id, Category.assoc]
      change (extensionAdjunction a).unit.app (P.X n) ≫
        s.tensor.iso.inv.app (P.X n) ≫
        ((curriedTensor (Modules.{u, u, u} R)).flip.map h).app (P.X n) ≫
        t.tensor.iso.hom.app (P.X n) = (extensionAdjunction a').unit.app (P.X n)
      exact scalar_tensor_unit_natural a a' s.tensor t.tensor psi h hh (P.X n)
    have ht := unit_transport (s.underlyingIso.app (DerivedCategory.Q.{w}.obj P))
      (t.underlyingIso.app (DerivedCategory.Q.{w}.obj P))
      (c P hp (coefficient a)) (c P hp (coefficient a'))
      (DerivedCategory.Q.{w}.mapIso (ordinaryScalarTotal a s.tensor P))
      (DerivedCategory.Q.{w}.mapIso (ordinaryScalarTotal a' t.tensor P))
      (scalarEvaluation a s P hp) (scalarEvaluation a' t P hp)
      f g (s.adj.unit.app (DerivedCategory.Q.{w}.obj P))
      (t.adj.unit.app (DerivedCategory.Q.{w}.obj P))
      (DerivedCategory.Q.{w}.map ((scalarCochainUnit a).app P))
      (DerivedCategory.Q.{w}.map ((scalarCochainUnit a').app P))
      (computes a s) (computes a' t) hn' (s.unit_model P hp hf)
      (t.unit_model P hp hf) hv
    simpa only [f, Iso.app_hom, Iso.app_inv, canonicalDerivedTensor,
      scalarTensorFunctor, NatTrans.comp_app, scalarUnderlyingMap, scalarTensorComparison,
      Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Category.id_comp, Category.comp_id,
      Functor.flip_map_app, Category.assoc] using ht
  exact NatTrans.congr_app he M
end CategoryTheory.AlgebraDiagramPullback
