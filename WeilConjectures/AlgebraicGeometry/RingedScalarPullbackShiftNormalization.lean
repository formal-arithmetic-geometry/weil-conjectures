/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
public import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
public import WeilConjectures.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullbackIndependentSupplement
public import WeilConjectures.AlgebraicGeometry.RingedCoefficientScalarShifts
public import Mathlib.CategoryTheory.Shift.CommShift
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Shift
import WeilConjectures.CategoryTheory.CochainUniversalCounitTransport

/-! # Counit-normalized shifts of the ringed scalar/pullback comparison

Source: the proper-base-change blueprint, scalar extension, operations shift clause;
Stacks Project, Tags 0G7E, 0D6D and 05SU
(blueprint: lem-weil-pbc-ringed-scalar-pullback-shift-normalization).

The ordinary comparison is the existing balanced scalar association. All four
universal pairs and their counit-normalized shift structures are quantified explicitly.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe c v x z r w

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.CochainPullback

namespace SheafOfModules

-- The fixed cochain counit of any universal pair computes on resolving complexes.
private theorem pull_counit_isIso
    {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    {X : Type x} [Category.{z} X] [EssentiallySmall.{r} X]
    {J : GrothendieckTopology C} {T : GrothendieckTopology X}
    {R : Sheaf J CommRingCat.{r}} {S : Sheaf T CommRingCat.{r}}
    (f : RingedPullback R S)
    [HasDerivedCategory.{w} (Modules R)] [HasDerivedCategory.{w} (Modules S)]
    (L : DerivedCategory (Modules R) ⥤ DerivedCategory (Modules S))
    (e : DerivedCategory.Q ⋙ L ⟶ pull f ⋙ DerivedCategory.Q)
    [L.IsLeftDerivedFunctor e (HomologicalComplex.quasiIso (Modules R) (.up ℤ))]
    (P : Complex R) (hp : P.IsKFlatIndependentCoefficients)
    (hf : ∀ i : ℤ, IsFlatOnSite (J := J) (R := R) (P.X i)) :
    IsIso (e.app P) := by
  have := f.finiteLimits
  obtain ⟨L', ε, hu, _, _, hc, _⟩ := ringedTopoiDerivedPullbackIndependent
    f.uInv f.uPush f.adj f.I f.coefficient f.L f.hobj f.hmap
  have := hu
  have := Functor.IsLeftDerivedFunctor.isRightKanExtension L' ε
    (HomotopyCategory.quasiIso (Modules R) (.up ℤ))
  let β := derivedCochainCounit f.L L' ε
  have htransport := cochainUniversalCounitTransport f.L L' ε
  have hβ : L'.IsRightKanExtension β := htransport.1
  have hβu : L'.IsLeftDerivedFunctor β
      (HomologicalComplex.quasiIso (Modules R) (.up ℤ)) := ⟨hβ⟩
  let a := Functor.leftDerivedNatIso L' L β e
    (HomologicalComplex.quasiIso (Modules R) (.up ℤ)) (Iso.refl _)
  have hfac : a.hom.app (DerivedCategory.Q.obj P) ≫ e.app P = β.app P := by
    simp [a]
  have := hc P hp hf
  have : IsIso (β.app P) := (htransport.2 P).2 inferInstance
  rw [← hfac] at this
  exact IsIso.of_isIso_comp_left (a.hom.app _) _

-- Cancellation of the two normalized computation squares on a shifted model.
private theorem shift_on_model
    {A D E : Type*} [Category A] [Category D] [Category E]
    [HasShift A ℤ] [HasShift D ℤ] [HasShift E ℤ]
    (Q : A ⥤ D) [Q.CommShift ℤ]
    (H₁ H₂ : D ⥤ E) [H₁.CommShift ℤ] [H₂.CommShift ℤ]
    (F₁ F₂ : A ⥤ E) [F₁.CommShift ℤ] [F₂.CommShift ℤ]
    (b₁ : Q ⋙ H₁ ⟶ F₁) (b₂ : Q ⋙ H₂ ⟶ F₂) (β : F₁ ⟶ F₂)
    [NatTrans.CommShift b₁ ℤ] [NatTrans.CommShift b₂ ℤ]
    [NatTrans.CommShift β ℤ] (τ : H₁ ⟶ H₂) (P : A) (n : ℤ)
    [IsIso (b₂.app P)]
    (h₀ : τ.app (Q.obj P) ≫ b₂.app P = b₁.app P ≫ β.app P)
    (hₙ : τ.app (Q.obj (P⟦n⟧)) ≫ b₂.app (P⟦n⟧) =
      b₁.app (P⟦n⟧) ≫ β.app (P⟦n⟧)) :
    τ.app ((Q.obj P)⟦n⟧) ≫ (H₂.commShiftIso n).hom.app (Q.obj P) =
      (H₁.commShiftIso n).hom.app (Q.obj P) ≫ (τ.app (Q.obj P))⟦n⟧' := by
  have h := NatTrans.shift_app_comm (b₁ ≫ β) n P
  simp only [NatTrans.comp_app] at h
  rw [← h₀, ← hₙ, Functor.map_comp] at h
  simp only [Category.assoc] at h
  rw [← NatTrans.shift_app_comm b₂ n P] at h
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at h
  rw [← τ.naturality_assoc] at h
  apply (cancel_epi (H₁.map ((Q.commShiftIso n).hom.app P))).1
  apply (cancel_mono ((b₂.app P)⟦n⟧')).1
  simpa only [Category.assoc] using h.symm

private theorem kflat_shift
    {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{r}}
    (P : Complex R) (hp : P.IsKFlatIndependentCoefficients) (n : ℤ) :
    (P⟦n⟧).IsKFlatIndependentCoefficients := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  intro A ha
  have ht := hp A ha
  have hs : (CochainComplex.mapBifunctor A P (MonoidalCategory.curriedTensor _)⟦n⟧).Acyclic := by
    rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at ht ⊢
    rw [← HomotopyCategory.shift_quotient_obj]
    exact (HomotopyCategory.subcategoryAcyclic (Modules R)).le_shift n _ ht
  intro i
  exact (hs i).of_iso
    (CochainComplex.mapBifunctorShift₂Iso A P (MonoidalCategory.curriedTensor _) n).symm

private theorem exists_flat_model
    {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})
    [HasDerivedCategory.{w} (Modules R)] (K : DerivedCategory (Modules R)) :
    ∃ P : Complex R, P.IsKFlatIndependentCoefficients ∧
      (∀ i : ℤ, IsFlatOnSite (J := J) (R := R) (P.X i)) ∧
      Nonempty (DerivedCategory.Q.obj P ≅ K) := by
  classical
  have := Localization.essSurj DerivedCategory.Q
    (HomologicalComplex.quasiIso (Modules R) (.up ℤ))
  let A := DerivedCategory.Q.objPreimage K
  obtain ⟨P, p, hp, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) A
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  have hf' (i : ℤ) : IsFlatOnSite (J := J) (R := R) (P.X i) :=
    (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (P.X i)).symm (hf i)
  have := hq
  exact ⟨P, hp, hf', ⟨asIso (DerivedCategory.Q.map p) ≪≫
    DerivedCategory.Q.objObjPreimageIso K⟩⟩

/-- The canonical balanced ringed scalar/pullback comparison commutes with every
integer shift, for the composite shift convention of Mathlib.
Source: proper-base-change blueprint, scalar extension, operations shift clause;
Stacks Project, Tags 0G7E, 0D6D and 05SU
(blueprint: lem-weil-pbc-ringed-scalar-pullback-shift-normalization).

Proof:
1. Resolve a representative of K by a flat-term K-flat complex P. Ringed pullback
preserves flat terms and K-flatness, including scalar extension (identity topos).
Thus the two successive universal computation counits are invertible on P.
2. The existing scalarAssociation is the balanced map sending
(x tensor b) tensor e to (x tensor 1) tensor image(b)e. The commuting coefficient
square makes it well-defined; the inverse inserts the other coefficient unit.
3. On P[n] this is the same map in degree i+n. Both differentials carry (-1)^n,
and the coefficient factors have degree zero, so there is no extra Koszul sign.
Shifts preserve flat-term K-flatness by the total-tensor integer-shift comparison.
4. Scalar counits commute with the normalized shifts by coefficientScalarShifts;
the ringed counits do so by the coherent right-Kan shift construction. Whiskering
and composition give the same compatibility for the two successive counits.
5. Insert the representative normalization of theta for P and P[n], use steps 3
and 4, and cancel the invertible second computation map. Naturality transports
this equality along the resolution isomorphism Q(P) ≅ K. This gives the displayed
equation for every K and every integer n, without coefficient flatness or bounds.
-/
theorem ringedScalarPullbackShiftNormalization
    {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    {X : Type x} [Category.{z} X] [EssentiallySmall.{r} X]
    {J : GrothendieckTopology C} {T : GrothendieckTopology X}
    {R : Sheaf J CommRingCat.{r}} {S : Sheaf T CommRingCat.{r}}
    (f : RingedPullback R S) (k : Comparison f)
    (d : CoefficientSquare f) (k' : Comparison (changed f d))
    [HasDerivedCategory.{w} (Modules R)] [HasDerivedCategory.{w} (Modules S)]
    [HasDerivedCategory.{w} (Modules d.R')] [HasDerivedCategory.{w} (Modules d.S')]
    (CY : DerivedCategory (Modules R) ⥤ DerivedCategory (Modules d.R'))
    (CX : DerivedCategory (Modules S) ⥤ DerivedCategory (Modules d.S'))
    (LR : DerivedCategory (Modules R) ⥤ DerivedCategory (Modules S))
    (LS : DerivedCategory (Modules d.R') ⥤ DerivedCategory (Modules d.S'))
    (eY : DerivedCategory.Q ⋙ CY ⟶ extend d.sourceMap ⋙ DerivedCategory.Q)
    (eX : DerivedCategory.Q ⋙ CX ⟶ extend d.targetMap ⋙ DerivedCategory.Q)
    (eR : DerivedCategory.Q ⋙ LR ⟶ pull f ⋙ DerivedCategory.Q)
    (eS : DerivedCategory.Q ⋙ LS ⟶ pull (changed f d) ⋙ DerivedCategory.Q)
    [CY.IsLeftDerivedFunctor eY (HomologicalComplex.quasiIso (Modules R) (.up ℤ))]
    [CX.IsLeftDerivedFunctor eX (HomologicalComplex.quasiIso (Modules S) (.up ℤ))]
    [LR.IsLeftDerivedFunctor eR (HomologicalComplex.quasiIso (Modules R) (.up ℤ))]
    [LS.IsLeftDerivedFunctor eS (HomologicalComplex.quasiIso (Modules d.R') (.up ℤ))]
    [CY.CommShift ℤ] [CX.CommShift ℤ] [LR.CommShift ℤ] [LS.CommShift ℤ]
    [NatTrans.CommShift eY ℤ] [NatTrans.CommShift eX ℤ]
    [NatTrans.CommShift eR ℤ] [NatTrans.CommShift eS ℤ]
    (theta : CY ⋙ LS ≅ LR ⋙ CX)
    (normalized : ∀ P : Complex R,
      CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
      (∀ i : ℤ, IsFlatOnSite (J := J) (R := R) (P.X i)) →
      theta.hom.app (DerivedCategory.Q.obj P) ≫ CX.map (eR.app P) ≫
          eX.app ((pull f).obj P) =
        LS.map (eY.app P) ≫ eS.app ((extend d.sourceMap).obj P) ≫
          DerivedCategory.Q.map (kappa f k d k' P).hom)
    (K : DerivedCategory (Modules R)) (n : ℤ) :
    theta.hom.app (K⟦n⟧) ≫ ((LR ⋙ CX).commShiftIso n).hom.app K =
      ((CY ⋙ LS).commShiftIso n).hom.app K ≫ (theta.hom.app K)⟦n⟧' := by
  classical
  let F₁ := extend d.sourceMap ⋙ pull (changed f d)
  let F₂ := pull f ⋙ extend d.targetMap
  let β₀ := NatIso.mapHomologicalComplex (scalarAssociation f k d k') (.up ℤ)
  let i₁ := Functor.mapHomologicalComplexCompIso
    (Iso.refl (extensionFunctor d.sourceMap ⋙ (changed f d).L)) (.up ℤ)
  let i₂ := Functor.mapHomologicalComplexCompIso
    (Iso.refl (f.L ⋙ extensionFunctor d.targetMap)) (.up ℤ)
  let β : F₁ ⟶ F₂ := i₁.hom ≫ β₀.hom ≫ i₂.inv
  have hi₁ : NatTrans.CommShift i₁.hom ℤ := by dsimp [i₁]; infer_instance
  have hi₂ : NatTrans.CommShift i₂.inv ℤ := by dsimp [i₂]; infer_instance
  have hβ₀ : NatTrans.CommShift β₀.hom ℤ := by
    change NatTrans.CommShift
      (NatTrans.mapHomologicalComplex (scalarAssociation f k d k').hom (.up ℤ)) ℤ
    infer_instance
  have hβ : NatTrans.CommShift β ℤ := by dsimp only [β]; infer_instance
  let b₁ : DerivedCategory.Q ⋙ (CY ⋙ LS) ⟶ F₁ ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight eY LS ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft (extend d.sourceMap) eS ≫
      (Functor.associator _ _ _).inv
  let b₂ : DerivedCategory.Q ⋙ (LR ⋙ CX) ⟶ F₂ ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight eR CX ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft (pull f) eX ≫
      (Functor.associator _ _ _).inv
  have hb₁ : NatTrans.CommShift b₁ ℤ := by dsimp [b₁, F₁]; infer_instance
  have hb₂ : NatTrans.CommShift b₂ ℤ := by dsimp [b₂, F₂]; infer_instance
  let δ := Functor.whiskerRight β DerivedCategory.Q
  have hδ : NatTrans.CommShift δ ℤ := by dsimp [δ]; infer_instance
  have hnorm (P : Complex R) (hp : P.IsKFlatIndependentCoefficients)
      (hf : ∀ i : ℤ, IsFlatOnSite (J := J) (R := R) (P.X i)) :
      theta.hom.app (DerivedCategory.Q.obj P) ≫ b₂.app P = b₁.app P ≫ δ.app P := by
    have hβP : β.app P = (kappa f k d k' P).hom := by
      ext i : 1
      simp only [β, β₀, i₁, i₂, kappa, NatTrans.comp_app,
        HomologicalComplex.comp_f, Functor.mapHomologicalComplexCompIso_hom_app_f,
        Functor.mapHomologicalComplexCompIso_inv_app_f, NatIso.mapHomologicalComplex_hom_app_f]
      erw [Category.id_comp, Category.comp_id]
      rfl
    simpa [b₁, b₂, δ, hβP, Category.assoc] using normalized P hp hf
  have hmodel (P : Complex R) (hp : P.IsKFlatIndependentCoefficients)
      (hf : ∀ i : ℤ, IsFlatOnSite (J := J) (R := R) (P.X i)) :
      theta.hom.app ((DerivedCategory.Q.obj P)⟦n⟧) ≫
          ((LR ⋙ CX).commShiftIso n).hom.app (DerivedCategory.Q.obj P) =
        ((CY ⋙ LS).commShiftIso n).hom.app (DerivedCategory.Q.obj P) ≫
          (theta.hom.app (DerivedCategory.Q.obj P))⟦n⟧' := by
    have := f.finiteLimits
    have hpull := isKFlat_ringedToposPullback f.uInv f.uPush f.adj f.I f.coefficient
      f.L f.hobj f.hmap P hp hf
    have := pull_counit_isIso f LR eR P hp hf
    have := pull_counit_isIso (extensionPullback d.targetMap) CX eX
      ((pull f).obj P) hpull.1 hpull.2
    have hiso : IsIso (b₂.app P) := by dsimp [b₂]; infer_instance
    exact shift_on_model DerivedCategory.Q (CY ⋙ LS) (LR ⋙ CX)
      (F₁ ⋙ DerivedCategory.Q) (F₂ ⋙ DerivedCategory.Q) b₁ b₂ δ theta.hom P n
      (hnorm P hp hf) (hnorm (P⟦n⟧) (kflat_shift P hp n) (fun i ↦ hf (i + n)))
  let s : shiftFunctor _ n ⋙ (CY ⋙ LS) ⟶ (LR ⋙ CX) ⋙ shiftFunctor _ n :=
    Functor.whiskerLeft (shiftFunctor _ n) theta.hom ≫ ((LR ⋙ CX).commShiftIso n).hom
  let t : shiftFunctor _ n ⋙ (CY ⋙ LS) ⟶ (LR ⋙ CX) ⋙ shiftFunctor _ n :=
    ((CY ⋙ LS).commShiftIso n).hom ≫ Functor.whiskerRight theta.hom (shiftFunctor _ n)
  change s.app K = t.app K
  obtain ⟨P, hp, hf, ⟨e⟩⟩ := exists_flat_model R K
  let H := shiftFunctor _ n ⋙ (CY ⋙ LS)
  let G := (LR ⋙ CX) ⋙ shiftFunctor _ n
  calc
    s.app K = H.map e.inv ≫ s.app (DerivedCategory.Q.obj P) ≫ G.map e.hom := by
      dsimp only [H, G]
      rw [s.naturality_assoc]
      rw [← G.map_comp, e.inv_hom_id, G.map_id, Category.comp_id]
    _ = H.map e.inv ≫ t.app (DerivedCategory.Q.obj P) ≫ G.map e.hom := by
      rw [show s.app (DerivedCategory.Q.obj P) = t.app (DerivedCategory.Q.obj P)
        from hmodel P hp hf]
    _ = t.app K := by
      dsimp only [H, G]
      rw [t.naturality_assoc]
      rw [← G.map_comp, e.inv_hom_id, G.map_id, Category.comp_id]

end SheafOfModules
