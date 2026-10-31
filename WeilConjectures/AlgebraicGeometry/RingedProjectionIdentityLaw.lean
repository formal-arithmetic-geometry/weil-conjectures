/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RingedProjectionCoherenceData
import WeilConjectures.AlgebraicGeometry.RingedProjectionIdentityTotalTensor
import WeilConjectures.AlgebraicGeometry.RingedTensorEdgeRepresentativeEquation
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
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
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModelSupplement
import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions

/-! Field-level coherence law for normalized ringed projection tensor comparisons.
(blueprint: lem-sfb-ringed-projection-tensor-laws-identity-law) -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
namespace SheafOfModules.ProjectionCoherence

set_option synthInstance.maxSize 2048

private noncomputable abbrev tensorTotal (X : RingedTensorCorner.{u, w}) :=
  Functor.uncurry.obj ((@MonoidalCategory.curriedTensor X.mateModules _
    (monoidalCategory X.ring)).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ))

private noncomputable abbrev pull {X : RingedTensorCorner.{u, w}}
    (h : RingedTensorEdge X X) := h.pullback.mapHomologicalComplex (.up ℤ)

private theorem pull_good {X : RingedTensorCorner.{u, w}}
    (h : RingedTensorEdge X X) {P : CochainComplex X.mateModules ℤ} (hp : X.mateFlat P) :
    X.mateFlat ((pull h).obj P) := by
  have hp' : ∀ n, IsFlatOnSite (J := X.topology) (R := X.ring) (P.X n) := fun n ↦
    (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso X.ring _).symm (hp.2 n)
  obtain ⟨hk, hf⟩ := isKFlat_ringedToposPullback h.inverse h.direct h.adjunction
    h.algebraic h.ringMap h.pullback h.object_eq h.map_eq P hp.1 hp'
  exact ⟨hk, fun n ↦ (exactFunctor _ _).prop_of_iso
    (siteSheafTensorRightIso X.ring _) (hf n)⟩

private theorem total_good {X : RingedTensorCorner.{u, w}}
    {P Q : CochainComplex X.mateModules ℤ} (hp : X.mateFlat P) (hq : X.mateFlat Q) :
    X.mateFlat ((tensorTotal X).obj (P, Q)) := by
  have ht := KFlatTotalTensorModel.kFlat_total_tensor_model X.ring P Q hp.1 hq.1
    (fun n ↦ (exactFunctor _ _).prop_of_iso
      (siteSheafTensorRightIso X.ring _).symm (hp.2 n))
    (fun n ↦ (exactFunctor _ _).prop_of_iso
      (siteSheafTensorRightIso X.ring _).symm (hq.2 n))
  exact ⟨ht.1, fun n ↦ (exactFunctor _ _).prop_of_iso
    (siteSheafTensorRightIso X.ring _) (ht.2.1 n)⟩

private theorem tensor_map_comp {A B : Type*} [Category A] [Category B]
    (T : A × A ⥤ B) {P₁ P₂ P₃ Q₁ Q₂ Q₃ : A}
    (a : P₁ ⟶ P₂) (b : Q₁ ⟶ Q₂) (c : P₂ ⟶ P₃) (d : Q₂ ⟶ Q₃) :
    T.map (Prod.mkHom (a ≫ c) (b ≫ d)) =
      T.map (Prod.mkHom a b) ≫ T.map (Prod.mkHom c d) :=
  T.map_comp (Prod.mkHom a b) (Prod.mkHom c d)

private theorem identity_tensor_transport
    {C : Type*} [Category C] (T : C × C ⥤ C) (L : C ⥤ C)
    (t : T ⋙ L ⟶ (L.prod L) ⋙ T) (l : L ≅ 𝟭 C)
    {P Q P' Q' R R' R'' : C} (r : R ≅ T.obj (P, Q))
    (cp : L.obj P ⟶ P') (cq : L.obj Q ⟶ Q') (cr : L.obj R ⟶ R')
    (gp : P' ⟶ P) (gq : Q' ⟶ Q) (gr : R' ⟶ R)
    (d : R' ⟶ R'') (m : R'' ⟶ R) (b : R'' ⟶ T.obj (P', Q'))
    (np : l.hom.app P = cp ≫ gp) (nq : l.hom.app Q = cq ≫ gq)
    (nr : l.hom.app R = cr ≫ gr)
    (edge : L.map r.hom ≫ t.app (P, Q) ≫ T.map (Prod.mkHom cp cq) = cr ≫ d ≫ b)
    (rep : m ≫ r.hom = b ≫ T.map (Prod.mkHom gp gq)) (ordinary : d ≫ m = gr) :
    t.app (P, Q) ≫ T.map (Prod.mkHom (l.hom.app P) (l.hom.app Q)) =
      l.hom.app (T.obj (P, Q)) := by
  apply (cancel_epi (L.map r.hom)).mp
  have hn := l.hom.naturality r.hom
  dsimp only [Functor.id_map] at hn
  calc
    L.map r.hom ≫ (t.app (P, Q) ≫
        T.map (Prod.mkHom (l.hom.app P) (l.hom.app Q))) =
        (L.map r.hom ≫ t.app (P, Q) ≫ T.map (Prod.mkHom cp cq)) ≫
          T.map (Prod.mkHom gp gq) := by
      rw [np, nq, tensor_map_comp]
      simp only [Category.assoc]
    _ = (cr ≫ d ≫ b) ≫ T.map (Prod.mkHom gp gq) :=
      congrArg (fun z ↦ z ≫ T.map (Prod.mkHom gp gq)) edge
    _ = cr ≫ (d ≫ m) ≫ r.hom := by
      simp only [Category.assoc]
      rw [← rep]
    _ = cr ≫ gr ≫ r.hom := by rw [ordinary]
    _ = l.hom.app R ≫ r.hom := by rw [nr, Category.assoc]
    _ = L.map r.hom ≫ l.hom.app (T.obj (P, Q)) := hn.symm

attribute [local irreducible] monoidalCategory CanonicalRingedTensorComparison.totalIso
  RingedTensorEdge.tensorComparison ringedTopoiCanonicalDerivedTensorComparison
  derivedPullbackComplexComparison

set_option maxHeartbeats 800000 in
-- Keep both representative comparisons explicit during the derived transport.
private theorem identity_representative {X : RingedTensorCorner.{u, w}}
    (h : RingedTensorEdge X X) (a : RingedTensorModel X) (s : Identity h)
    (l : h.left ≅ 𝟭 X.mateDerived) (hnorm : s.Normalized l)
    (P Q : CochainComplex X.mateModules ℤ) (hp : X.mateFlat P) (hq : X.mateFlat Q) :
    (h.tensorComparison a a).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      X.tensor.map (Prod.mkHom (l.hom.app (DerivedCategory.Q.obj P))
        (l.hom.app (DerivedCategory.Q.obj Q))) =
      l.hom.app (X.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) := by
  let r := a.representative.app (⟨P, hp⟩, ⟨Q, hq⟩)
  let γ := (NatIso.mapHomologicalComplex s.modules (.up ℤ)).hom
  let δ := (h.ordinaryTensor.totalIso X.ring X.ring h.inverseRing h.inverse h.algebraic
    h.ringMap h.pullback h.object_eq h.pushforward h.moduleAdjunction P Q).inv
  have he := ringedTensorEdgeRepresentativeEquation h a a P Q hp hq
    (pull_good h hp) (pull_good h hq)
  have hrep : DerivedCategory.Q.map ((tensorTotal X).map
      (Prod.mkHom (γ.app P) (γ.app Q))) ≫ r.hom =
      a.representative.hom.app
        (⟨(pull h).obj P, pull_good h hp⟩, ⟨(pull h).obj Q, pull_good h hq⟩) ≫
        X.tensor.map (Prod.mkHom (DerivedCategory.Q.map (γ.app P))
          (DerivedCategory.Q.map (γ.app Q))) := by
    exact a.representative.hom.naturality (Prod.mkHom
      (ObjectProperty.homMk (X := ⟨(pull h).obj P, pull_good h hp⟩)
        (Y := ⟨P, hp⟩) (γ.app P))
      (ObjectProperty.homMk (X := ⟨(pull h).obj Q, pull_good h hq⟩)
        (Y := ⟨Q, hq⟩) (γ.app Q)))
  have ho : δ ≫ (tensorTotal X).map (Prod.mkHom (γ.app P) (γ.app Q)) =
      γ.app ((tensorTotal X).obj (P, Q)) := ringedProjectionIdentityTotalTensor h s P Q
  exact identity_tensor_transport X.tensor h.left (h.tensorComparison a a).hom l r
    (derivedPullbackComplexComparison h.pullback h.left h.epsilon P)
    (derivedPullbackComplexComparison h.pullback h.left h.epsilon Q)
    (derivedPullbackComplexComparison h.pullback h.left h.epsilon
      ((tensorTotal X).obj (P, Q)))
    (DerivedCategory.Q.map (γ.app P)) (DerivedCategory.Q.map (γ.app Q))
    (DerivedCategory.Q.map (γ.app ((tensorTotal X).obj (P, Q))))
    (DerivedCategory.Q.map δ)
    (DerivedCategory.Q.map ((tensorTotal X).map (Prod.mkHom (γ.app P) (γ.app Q))))
    (a.representative.hom.app
      (⟨(pull h).obj P, pull_good h hp⟩, ⟨(pull h).obj Q, pull_good h hq⟩))
    (hnorm P hp) (hnorm Q hq) (hnorm _ (total_good hp hq)) he hrep
    ((DerivedCategory.Q.map_comp _ _).symm.trans (congrArg DerivedCategory.Q.map ho))

private theorem natTrans_eq_at_iso
    {A B : Type*} [Category A] [Category B] {F G : A ⥤ B}
    (a b : F ⟶ G) {X Y : A} (i : X ≅ Y) (h : a.app X = b.app X) :
    a.app Y = b.app Y := by
  rw [← cancel_epi (F.map i.hom), a.naturality, b.naturality, h]


set_option maxHeartbeats 1000000 in
-- Elaborate faithful restriction with both derived tensor functors fixed.
/-- Identity law for a normalized ringed projection tensor comparison.
Source: Stacks Project, Tags 0D6D and 0FPI; normalized identity descent.
The proof uses the normalized representative square for the identity edge and
extends it by tensor naturality from flat K-flat representatives.
(blueprint: lem-sfb-ringed-projection-tensor-laws-identity-law) -/
theorem ringedProjectionIdentityLaw
    (constraints : ∀ (X : RingedTensorCorner.{u, w}) (a : RingedTensorModel X),
      TensorConstraints X a) :
    ∀ {X : RingedTensorCorner.{u, w}} (h : RingedTensorEdge X X)
      (a : RingedTensorModel X) (s : Identity h)
      (l : h.left ≅ 𝟭 X.mateDerived),
      s.Normalized l → ∀ E Q : X.mateDerived,
        (h.tensorComparison a a).hom.app (E, Q) ≫
            X.tensor.map (Prod.mkHom (l.hom.app E) (l.hom.app Q)) =
          l.hom.app (X.tensor.obj (E, Q)) := by
  intro X h a s l hnorm E Q
  have _ := constraints X a
  let lhs : X.tensor ⋙ h.left ⟶ X.tensor :=
    (h.tensorComparison a a).hom ≫
      Functor.whiskerRight (NatTrans.prod l.hom l.hom) X.tensor
  let rhs : X.tensor ⋙ h.left ⟶ X.tensor := Functor.whiskerLeft X.tensor l.hom
  have he : lhs = rhs := by
    obtain ⟨P, hP, _, _, hd⟩ :=
      site_derived_tensor_descent_independentCoefficients.{u, u, u, w, u + 1, w}
        X.topology X.ring
    apply (hd X.mateDerived inferInstance (X.tensor ⋙ h.left) X.tensor).injective
    apply NatTrans.ext
    funext Z
    obtain ⟨hp, hpf⟩ := (hP Z.1.obj).1 Z.1.property
    obtain ⟨hq, hqf⟩ := (hP Z.2.obj).1 Z.2.property
    have hp' : X.mateFlat Z.1.obj.as :=
      ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).mp hp,
        fun n ↦ (exactFunctor _ _).prop_of_iso
          (siteSheafTensorRightIso X.ring _) (hpf n)⟩
    have hq' : X.mateFlat Z.2.obj.as :=
      ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).mp hq,
        fun n ↦ (exactFunctor _ _).prop_of_iso
          (siteSheafTensorRightIso X.ring _) (hqf n)⟩
    have hz : lhs.app (DerivedCategory.Q.obj Z.1.obj.as,
        DerivedCategory.Q.obj Z.2.obj.as) = rhs.app
        (DerivedCategory.Q.obj Z.1.obj.as, DerivedCategory.Q.obj Z.2.obj.as) :=
      identity_representative h a s l hnorm Z.1.obj.as Z.2.obj.as hp' hq'
    exact natTrans_eq_at_iso lhs rhs
      (((DerivedCategory.quotientCompQhIso X.mateModules).app Z.1.obj.as).symm.prod
        ((DerivedCategory.quotientCompQhIso X.mateModules).app Z.2.obj.as).symm) hz
  exact congr_app he (E, Q)

end SheafOfModules.ProjectionCoherence
