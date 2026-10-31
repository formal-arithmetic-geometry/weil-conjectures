/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import WeilConjectures.CategoryTheory.RingedIdealGenerators
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import WeilConjectures.Algebra.Homology.Ringed.RingedToposPullbackFiniteType
import all WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.GeometricRingTransport
import all Mathlib.CategoryTheory.Sites.Limits
import all WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import all WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import all WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import all WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import all WeilConjectures.Algebra.Homology.KFlatResolution
import all WeilConjectures.SmoothPurity.Supporting.ChangeOfRingsKFlatQuasiIsoSupplement
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all Mathlib.CategoryTheory.Sites.EpiMono
import all Mathlib.CategoryTheory.Adjunction.Additive
import all Mathlib.Algebra.Category.Grp.EpiMono
import all Mathlib.Algebra.Category.Grp.Abelian
import all Mathlib.CategoryTheory.Sites.Abelian
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import all WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackUnitExistence
import all WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonData
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
import WeilConjectures.CategoryTheory.FiniteTypeRestrictionExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.CategoryTheory.Sites.Pullback

/-! # Finite type of the structural image ideal

Source: Stacks Project, algebraization.tex, Tags 099E and 0A0G, finite generating covers.
(blueprint: lem-weil-pbc-image-ideal-finite-type).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

private noncomputable abbrev underlyingModules
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) :=
  SheafOfModules.toSheaf R ⋙ sheafCompose J (forget AddCommGrpCat)

private theorem linear_lift
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N Q : SheafOfModules.{u} R}
    (j : N ⟶ Q) [Mono j] (a : M ⟶ Q)
    (k : (underlyingModules R).obj M ⟶ (underlyingModules R).obj N)
    (hk : k ≫ (underlyingModules R).map j = (underlyingModules R).map a) :
    ∃ b : M ⟶ N, b ≫ j = a := by
  have hj (W : Cᵒᵖ) : Function.Injective (j.val.app W) := by
    exact (ModuleCat.mono_iff_injective ((SheafOfModules.evaluation R W).map j)).mp
      inferInstance
  have he (W : Cᵒᵖ) (m : M.val.obj W) :
      j.val.app W (k.hom.app W m) = a.val.app W m :=
    congrArg (fun f ↦ f.hom.app W m) hk
  let b : M ⟶ N := ⟨{
    app := fun W ↦ ModuleCat.ofHom {
      toFun := k.hom.app W
      map_add' := fun x y ↦ hj W (by simp only [map_add, he])
      map_smul' := fun r x ↦ hj W (by simp only [map_smul, RingHom.id_apply, he]) }
    naturality := by
      intro W V f
      ext x
      exact CategoryTheory.congr_fun (k.hom.naturality f) x }⟩
  refine ⟨b, ?_⟩
  ext W x
  exact he W x

/-- The least ideal containing the structural image of a finite-type ideal is finite type.

Source: Stacks Project, algebraization.tex, Tags 099E and 0A0G.
(blueprint: lem-weil-pbc-image-ideal-finite-type).

Proof: choose an algebraic presentation `I` of the inverse image with ring `RI` and write
the structural ring map as a commutative-ring map `c : RI ⟶ RX`. The ordinary pullback
`P = RX ⊗_RI I(IY)` is of finite type by `isFiniteType_ordinaryRingedToposPullback`.
Identify `I(RY)` with `RI` by `inverseImage_unit_iso`; composing `I(ιY)`, this identification
and `c` gives an `RI`-linear map `d : I(IY) ⟶ RX`, whose tensor adjoint is `α : P ⟶ RX`.
For a monic ideal `j : N ⟶ RX`, a set-sheaf factorization of the structural image
through `N` is sectionwise additive and linear because `j` is sectionwise injective, so
it is a module map and its adjoint factors `α` through `j`; conversely a factorization
of `α` gives one of the structural image by precomposing with `x ↦ 1 ⊗ x`. So `hImage`
gives `β : P ⟶ IX` over `RX` and `IX ⟶ image α` over `RX`. The image universal property
gives `image α ⟶ IX`, a split epimorphism by monicity of `ιX`, so `β` is epi.
Restriction to each object slice is exact, so the local finite generators of `P`, pushed
along `β`, are local finite generators of `IX`. Empty covers and zero ranks are allowed. -/
theorem ringed_imageIdeal_finiteType
    {C X : Type u} [SmallCategory C] [SmallCategory X]
    {J : GrothendieckTopology C} {K : GrothendieckTopology X}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (RY : Sheaf J CommRingCat.{u}) (RX : Sheaf K CommRingCat.{u})
    (f : RingedToposMorphism
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))
    (IY : ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))
    (ιY : IY ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))
    [Mono ιY] [IY.IsFiniteType]
    (IX : ringedSiteModules.{u, u, u, u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
    (ιX : IX ⟶ SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
    [Mono ιX]
    (hImage : ∀ (N : ringedSiteModules.{u, u, u, u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
      (j : N ⟶ SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)),
      Mono j →
      (∃ k : f.inverse.obj ((SheafOfModules.toSheaf
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY) ⋙
          sheafCompose J (forget AddCommGrpCat)).obj IY) ⟶
          (SheafOfModules.toSheaf ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX) ⋙
            sheafCompose K (forget AddCommGrpCat)).obj N,
        (k ≫ (SheafOfModules.toSheaf ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX) ⋙
            sheafCompose K (forget AddCommGrpCat)).map j : _ ⟶ (sheafCompose K (forget RingCat)).obj
              ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)) =
          (f.inverse.map ((SheafOfModules.toSheaf
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY) ⋙
            sheafCompose J (forget AddCommGrpCat)).map ιY) : _ ⟶ f.inverse.obj
              ((sheafCompose J (forget RingCat)).obj
                ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))) ≫ f.ringMap) ↔
      ∃ a : IX ⟶ N, a ≫ j = ιX)
 :
    IX.IsFiniteType := by
  classical
  let _ := f.leftExact
  obtain ⟨RI, ⟨I⟩⟩ := algebraic_image J K
    f.inverse f.direct f.adj RY
  obtain ⟨c, hc⟩ := structural_map K J RX RY f RI I
  have hc' : I.ringUnderlying.hom ≫
      (sheafCompose K (forget CommRingCat)).map c = f.ringMap := by
    rw [hc, Iso.hom_inv_id_assoc]
  have hfin := SheafOfModules.isFiniteType_ordinaryRingedToposPullback RX RY f RI I c hc' IY
  obtain ⟨eI, heI⟩ := SheafOfModules.inverseImage_unit_iso RY RI f.inverse I
  let A := (sheafCompose K (forget₂ CommRingCat RingCat)).obj RI
  let B := (sheafCompose K (forget₂ CommRingCat RingCat)).obj RX
  let U := underlyingModules A
  let V := underlyingModules B
  let T := SheafOfModules.tensorFunctor c
  let S := SheafOfModules.restrictScalars
    ((sheafCompose K (forget₂ CommRingCat RingCat)).map c)
  let adj := SheafOfModules.tensorAdjunction c
  let _ : PreservesLimits S := adj.rightAdjoint_preservesLimits
  let q : SheafOfModules.unit A ⟶ S.obj (SheafOfModules.unit B) := ⟨{
    app := fun W ↦ ModuleCat.ofHom
      (X := (SheafOfModules.unit A).val.obj W)
      (Y := (S.obj (SheafOfModules.unit B)).val.obj W) {
      toFun := c.hom.app W
      map_add' := map_add (c.hom.app W).hom
      map_smul' := fun r x ↦ (c.hom.app W).hom.map_mul r x }
    naturality := by
      intro W V a
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact CategoryTheory.congr_fun (c.hom.naturality a) x }⟩
  let d := I.modules.map ιY ≫ eI.inv ≫ q
  let α := (adj.homEquiv _ _).symm d
  have heI' : U.map eI.inv = I.moduleUnderlying.hom.app _ ≫ I.ringUnderlying.hom := by
    apply (cancel_epi (U.map eI.hom)).mp
    rw [← U.map_comp, Iso.hom_inv_id, U.map_id, heI]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id]
  have hd : U.map d = I.moduleUnderlying.hom.app IY ≫
      f.inverse.map ((underlyingModules
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY)).map ιY) ≫ f.ringMap := by
    dsimp only [d]
    rw [U.map_comp, U.map_comp, heI']
    have hn := I.moduleUnderlying.hom.naturality ιY
    change U.map (I.modules.map ιY) ≫ I.moduleUnderlying.hom.app _ =
      I.moduleUnderlying.hom.app IY ≫ f.inverse.map
        ((underlyingModules
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY)).map ιY) at hn
    change U.map (I.modules.map ιY) ≫
      (I.moduleUnderlying.hom.app _ ≫ I.ringUnderlying.hom) ≫
        (sheafCompose K (forget CommRingCat)).map c = _
    rw [Category.assoc, ← Category.assoc (U.map (I.modules.map ιY)), hn]
    simp only [Category.assoc, hc']
  have hα : U.map d = SheafOfModules.tensorUnit c (I.modules.obj IY) ≫ V.map α := by
    rw [← SheafOfModules.tensorAdjunction_underlying]
    exact congrArg (fun a ↦ U.map a) ((adj.homEquiv _ _).apply_symm_apply d).symm
  have hfac (N : SheafOfModules.{u} B) (j : N ⟶ SheafOfModules.unit B) [Mono j] :
      (∃ k : f.inverse.obj ((underlyingModules
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY)).obj IY) ⟶ V.obj N,
        k ≫ V.map j =
          f.inverse.map ((underlyingModules
            ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY)).map ιY) ≫
              f.ringMap) ↔ ∃ b : T.obj (I.modules.obj IY) ⟶ N, b ≫ j = α := by
    constructor
    · rintro ⟨k, hk⟩
      obtain ⟨b, hb⟩ := linear_lift (S.map j) d
        (I.moduleUnderlying.hom.app IY ≫ k) (by
          change (I.moduleUnderlying.hom.app IY ≫ k) ≫ V.map j = U.map d
          rw [Category.assoc, hk, hd])
      refine ⟨(adj.homEquiv _ _).symm b, ?_⟩
      apply (adj.homEquiv _ _).injective
      rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply,
        Equiv.apply_symm_apply]
      exact hb
    · rintro ⟨b, hb⟩
      refine ⟨I.moduleUnderlying.inv.app IY ≫
        SheafOfModules.tensorUnit c (I.modules.obj IY) ≫ V.map b, ?_⟩
      simp only [Category.assoc, ← V.map_comp, hb]
      rw [← hα, hd]
      simp only [Iso.inv_hom_id_app_assoc]
  obtain ⟨b, hb⟩ := (hfac IX ιX).mp
    ((hImage IX ιX).mpr ⟨𝟙 IX, Category.id_comp _⟩ inferInstance)
  obtain ⟨a, ha⟩ := (hImage (image α) (image.ι α)).mp
    (fun _ ↦ (hfac (image α) (image.ι α)).mpr ⟨factorThruImage α, image.fac α⟩)
  let mf : MonoFactorisation α := { I := IX, m := ιX, e := b, fac := hb }
  let v := image.lift mf
  have hv : v ≫ ιX = image.ι α := image.lift_fac mf
  have hav : a ≫ v = 𝟙 IX := by
    apply (cancel_mono ιX).mp
    rw [Category.assoc, hv, ha, Category.id_comp]
  have : Epi v := epi_of_epi_fac hav
  have : Epi b := by
    have h : factorThruImage α ≫ v = b := image.fac_lift mf
    rw [← h]
    infer_instance
  let P := T.obj (I.modules.obj IY)
  have : P.IsFiniteType := hfin
  obtain ⟨σ, hσ⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData P
  have (W : X) : PreservesFiniteColimits (SheafOfModules.overFunctor B W) :=
    (SheafOfModules.overFunctor_exact B W).2
  let τ : IX.LocalGeneratorsData := {
    I := σ.I
    X := σ.X
    coversTop := σ.coversTop
    generators := fun i ↦ (σ.generators i).ofEpi (b.over (σ.X i)) }
  have hτ : τ.IsFiniteType := ⟨fun i ↦ by
    have := hσ.isFiniteType i
    exact inferInstanceAs ((σ.generators i).ofEpi (b.over (σ.X i))).IsFiniteType⟩
  exact ⟨⟨τ, hτ⟩⟩

end CategoryTheory
