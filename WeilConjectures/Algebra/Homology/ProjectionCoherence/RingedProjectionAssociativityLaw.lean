/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.ProjectionCoherence.RingedProjectionCoherenceData
import WeilConjectures.Algebra.Homology.Ringed.RingedTensorEdgeRepresentativeEquation
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
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
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
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.DerivedPullbackRepresentativeComputationSupplement
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel.KFlatTotalTensorModelSupplement
import WeilConjectures.SecSmoothPurity.CochainComparisonMonoidalEquationsSupplement

/-! Field-level coherence law for normalized ringed projection tensor comparisons.
(blueprint: lem-sfb-ringed-projection-tensor-laws-associativity-law) -/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u w
open CategoryTheory CategoryTheory.Functor
namespace SheafOfModules.ProjectionCoherence

private abbrev Modules (A : RingedTensorCorner.{u, w}) :=
  SheafOfModules.{u}
    ((sheafCompose A.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj A.ring)

private abbrev Complexes (A : RingedTensorCorner.{u, w}) := CochainComplex (Modules A) ℤ

private abbrev Good {A : RingedTensorCorner.{u, w}} (P : Complexes A) : Prop :=
  P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat

private noncomputable abbrev totalTensor (A : RingedTensorCorner.{u, w}) :=
  Functor.uncurry.obj ((@MonoidalCategory.curriedTensor (Modules A) _
    (monoidalCategory A.ring)).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ))

private noncomputable abbrev pull {A B : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge A B) := e.pullback.mapHomologicalComplex (.up ℤ)

private noncomputable abbrev comparison {A B : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge A B) (P : Complexes A) :=
  derivedPullbackComplexComparison e.pullback e.left e.epsilon P

private noncomputable abbrev delta {A B : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge A B) (P Q : Complexes A) :
    (pull e).obj ((totalTensor A).obj (P, Q)) ⟶
      (totalTensor B).obj ((pull e).obj P, (pull e).obj Q) :=
  (e.ordinaryTensor.totalIso A.ring B.ring e.inverseRing e.inverse e.algebraic e.ringMap
    e.pullback e.object_eq e.pushforward e.moduleAdjunction P Q).inv

private theorem pull_good {A B : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge A B) {P : Complexes A} (hp : Good P) :
    Good ((pull e).obj P) := by
  have hp' : ∀ n, IsFlatOnSite (J := A.topology) (R := A.ring) (P.X n) := fun n ↦
    (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso A.ring _).symm (hp.2 n)
  obtain ⟨hk, hf⟩ := isKFlat_ringedToposPullback e.inverse e.direct e.adjunction
    e.algebraic e.ringMap e.pullback e.object_eq e.map_eq P hp.1 hp'
  exact ⟨hk, fun n ↦ (exactFunctor _ _).prop_of_iso
    (siteSheafTensorRightIso B.ring _) (hf n)⟩

private theorem total_good {A : RingedTensorCorner.{u, w}}
    {P Q : Complexes A} (hp : Good P) (hq : Good Q) :
    Good ((totalTensor A).obj (P, Q)) := by
  have ht := KFlatTotalTensorModel.kFlat_total_tensor_model A.ring P Q hp.1 hq.1
    (fun n ↦ (exactFunctor _ _).prop_of_iso
      (siteSheafTensorRightIso A.ring _).symm (hp.2 n))
    (fun n ↦ (exactFunctor _ _).prop_of_iso
      (siteSheafTensorRightIso A.ring _).symm (hq.2 n))
  exact ⟨ht.1, fun n ↦ (exactFunctor _ _).prop_of_iso
    (siteSheafTensorRightIso A.ring _) (ht.2.1 n)⟩

private theorem comparison_isIso {A B : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge A B) {P : Complexes A} (hp : Good P) :
    IsIso (comparison e P) := by
  exact (CanonicalTensorPullbackOfUniverses.derivedPullback_kflat_tensor_computation
    e.inverse e.direct e.adjunction
    e.algebraic e.ringMap e.pullback e.object_eq e.map_eq e.left e.epsilon e.isLeftDerived).1
    P hp.1 (fun n ↦ (exactFunctor _ _).prop_of_iso
      (siteSheafTensorRightIso A.ring _).symm (hp.2 n))

set_option maxHeartbeats 800000 in
-- Elaborate the uniquely characterized comparison with both tensor models fixed.
private theorem edge_equation {A B : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge A B) (a : RingedTensorModel A) (b : RingedTensorModel B)
    (P Q : Complexes A) (hp : Good P) (hq : Good Q) :
    e.left.map (a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
      (e.tensorComparison a b).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      B.tensor.map (CategoryTheory.Prod.mkHom (comparison e P) (comparison e Q)) =
    comparison e ((totalTensor A).obj (P, Q)) ≫ DerivedCategory.Q.map (delta e P Q) ≫
      b.representative.hom.app
        (⟨(pull e).obj P, pull_good e hp⟩, ⟨(pull e).obj Q, pull_good e hq⟩) := by
  exact ringedTensorEdgeRepresentativeEquation e a b P Q hp hq
    (pull_good e hp) (pull_good e hq)

attribute [local irreducible] monoidalCategory
  RingedTensorEdge.tensorComparison ringedTopoiCanonicalDerivedTensorComparison
  derivedPullbackComplexComparison

private theorem comparison_naturality {A B : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge A B) {P Q : Complexes A} (a : P ⟶ Q) :
    e.left.map (DerivedCategory.Q.map a) ≫ comparison e Q =
      comparison e P ≫ DerivedCategory.Q.map ((pull e).map a) := by
  let eps : DerivedCategory.Q ⋙ e.left ⟶ pull e ⋙ DerivedCategory.Q :=
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso (Modules A)).inv e.left ≫
      Functor.whiskerLeft (HomotopyCategory.quotient (Modules A) (.up ℤ)) e.epsilon ≫
      Functor.whiskerRight (e.pullback.mapHomotopyCategoryFactors (.up ℤ)).hom
        DerivedCategory.Qh ≫
      Functor.whiskerLeft (pull e) (DerivedCategory.quotientCompQhIso (Modules B)).hom
  simpa only [eps, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.comp_map, comparison,
    derivedPullbackComplexComparison, Category.assoc] using eps.naturality a


private theorem nestedComparison_left
    {A B : Type*} [Category A] [Category B]
    (T : A × A ⥤ A) (V : B × B ⥤ B) (F : A ⥤ B)
    (m : T ⋙ F ⟶ (F.prod F) ⋙ V)
    {X Y Z N H : A} {X' Y' Z' N' H' : B}
    (i : N ⟶ T.obj (X, Y)) (j : H ⟶ T.obj (N, Z))
    (eX : F.obj X ⟶ X') (eY : F.obj Y ⟶ Y') (eZ : F.obj Z ⟶ Z')
    (eN : F.obj N ⟶ N') (eH : F.obj H ⟶ H')
    (i' : N' ⟶ V.obj (X', Y')) (j' : H' ⟶ V.obj (N', Z'))
    (hi : F.map i ≫ m.app (X, Y) ≫ V.map (Prod.mkHom eX eY) = eN ≫ i')
    (hj : F.map j ≫ m.app (N, Z) ≫ V.map (Prod.mkHom eN eZ) = eH ≫ j') :
    F.map (j ≫ T.map (Prod.mkHom i (𝟙 Z))) ≫ m.app (T.obj (X, Y), Z) ≫
        V.map (Prod.mkHom (m.app (X, Y)) (𝟙 (F.obj Z))) ≫
        V.map (Prod.mkHom (V.map (Prod.mkHom eX eY)) eZ) =
      eH ≫ j' ≫ V.map (Prod.mkHom i' (𝟙 Z')) := by
  have hn := m.naturality (Prod.mkHom i (𝟙 Z))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  simp only [F.map_id] at hn
  calc
    _ = F.map j ≫ m.app (N, Z) ≫ V.map
        (Prod.mkHom (F.map i ≫ m.app (X, Y) ≫ V.map (Prod.mkHom eX eY)) eZ) := by
      simp only [F.map_comp, Category.assoc]
      rw [reassoc_of% hn]
      simp only [← V.map_comp, CategoryTheory.prod_comp, Prod.mkHom,
        Category.id_comp]
    _ = F.map j ≫ m.app (N, Z) ≫ V.map (Prod.mkHom (eN ≫ i') eZ) := by rw [hi]
    _ = (F.map j ≫ m.app (N, Z) ≫ V.map (Prod.mkHom eN eZ)) ≫
        V.map (Prod.mkHom i' (𝟙 Z')) := by
      simp only [Category.assoc, ← V.map_comp, CategoryTheory.prod_comp, Prod.mkHom,
        Category.comp_id]
    _ = _ := by rw [hj]; simp only [Category.assoc]

private theorem nestedComparison_right
    {A B : Type*} [Category A] [Category B]
    (T : A × A ⥤ A) (V : B × B ⥤ B) (F : A ⥤ B)
    (m : T ⋙ F ⟶ (F.prod F) ⋙ V)
    {X Y Z N H : A} {X' Y' Z' N' H' : B}
    (i : N ⟶ T.obj (Y, Z)) (j : H ⟶ T.obj (X, N))
    (eX : F.obj X ⟶ X') (eY : F.obj Y ⟶ Y') (eZ : F.obj Z ⟶ Z')
    (eN : F.obj N ⟶ N') (eH : F.obj H ⟶ H')
    (i' : N' ⟶ V.obj (Y', Z')) (j' : H' ⟶ V.obj (X', N'))
    (hi : F.map i ≫ m.app (Y, Z) ≫ V.map (Prod.mkHom eY eZ) = eN ≫ i')
    (hj : F.map j ≫ m.app (X, N) ≫ V.map (Prod.mkHom eX eN) = eH ≫ j') :
    F.map (j ≫ T.map (Prod.mkHom (𝟙 X) i)) ≫ m.app (X, T.obj (Y, Z)) ≫
        V.map (Prod.mkHom (𝟙 (F.obj X)) (m.app (Y, Z))) ≫
        V.map (Prod.mkHom eX (V.map (Prod.mkHom eY eZ))) =
      eH ≫ j' ≫ V.map (Prod.mkHom (𝟙 X') i') := by
  have hn := m.naturality (Prod.mkHom (𝟙 X) i)
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  simp only [F.map_id] at hn
  calc
    _ = F.map j ≫ m.app (X, N) ≫ V.map
        (Prod.mkHom eX (F.map i ≫ m.app (Y, Z) ≫ V.map (Prod.mkHom eY eZ))) := by
      simp only [F.map_comp, Category.assoc]
      rw [reassoc_of% hn]
      simp only [← V.map_comp, CategoryTheory.prod_comp, Prod.mkHom,
        Category.id_comp]
    _ = F.map j ≫ m.app (X, N) ≫ V.map (Prod.mkHom eX (eN ≫ i')) := by rw [hi]
    _ = (F.map j ≫ m.app (X, N) ≫ V.map (Prod.mkHom eX eN)) ≫
        V.map (Prod.mkHom (𝟙 X') i') := by
      simp only [Category.assoc, ← V.map_comp, CategoryTheory.prod_comp, Prod.mkHom,
        Category.comp_id]
    _ = _ := by rw [hj]; simp only [Category.assoc]

private def comparisonLeft
    {A B : Type*} [Category A] [Category B]
    (T : A × A ⥤ A) (V : B × B ⥤ B) (F : A ⥤ B)
    (m : T ⋙ F ≅ (F.prod F) ⋙ V) :
    ((T.prod (𝟭 A)) ⋙ T) ⋙ F ≅
      ((F.prod F).prod F) ⋙ (V.prod (𝟭 B)) ⋙ V :=
  isoWhiskerLeft (T.prod (𝟭 A)) m ≪≫
    isoWhiskerRight (NatIso.prod m (Iso.refl F)) V

private def comparisonRight
    {A B : Type*} [Category A] [Category B]
    (T : A × A ⥤ A) (V : B × B ⥤ B) (F : A ⥤ B)
    (m : T ⋙ F ≅ (F.prod F) ⋙ V) :
    (CategoryTheory.prod.associator A A A ⋙ ((𝟭 A).prod T) ⋙ T) ⋙ F ≅
      ((F.prod F).prod F) ⋙ CategoryTheory.prod.associator B B B ⋙
        ((𝟭 B).prod V) ⋙ V :=
  isoWhiskerLeft (CategoryTheory.prod.associator A A A)
    (isoWhiskerLeft ((𝟭 A).prod T) m ≪≫
      isoWhiskerRight (NatIso.prod (Iso.refl F) m) V)

private theorem associativity_from_representatives
    {A B : Type*} [Category A] [Category B]
    (T : A × A ⥤ A) (V : B × B ⥤ B) (F : A ⥤ B)
    (m : T ⋙ F ≅ (F.prod F) ⋙ V)
    (alpha : (T.prod (𝟭 A)) ⋙ T ≅
      CategoryTheory.prod.associator A A A ⋙ ((𝟭 A).prod T) ⋙ T)
    (beta : (V.prod (𝟭 B)) ⋙ V ≅
      CategoryTheory.prod.associator B B B ⋙ ((𝟭 B).prod V) ⋙ V)
    {X Y Z W H : A} {X' Y' Z' W' H' : B}
    (l : W ≅ T.obj (T.obj (X, Y), Z)) (r : H ≅ T.obj (X, T.obj (Y, Z)))
    (a : W ⟶ H)
    (l' : W' ⟶ V.obj (V.obj (X', Y'), Z'))
    (r' : H' ⟶ V.obj (X', V.obj (Y', Z'))) (a' : W' ⟶ H')
    (eX : F.obj X ≅ X') (eY : F.obj Y ≅ Y') (eZ : F.obj Z ≅ Z')
    (eW : F.obj W ⟶ W') (eH : F.obj H ⟶ H')
    (hB : l.hom ≫ alpha.hom.app ((X, Y), Z) = a ≫ r.hom)
    (hA : l' ≫ beta.hom.app ((X', Y'), Z') = a' ≫ r')
    (hL : F.map l.hom ≫ (comparisonLeft T V F m).hom.app ((X, Y), Z) ≫
      V.map (Prod.mkHom (V.map (Prod.mkHom eX.hom eY.hom)) eZ.hom) = eW ≫ l')
    (hR : F.map r.hom ≫ (comparisonRight T V F m).hom.app ((X, Y), Z) ≫
      V.map (Prod.mkHom eX.hom (V.map (Prod.mkHom eY.hom eZ.hom))) = eH ≫ r')
    (hC : F.map a ≫ eH = eW ≫ a') :
    F.map (alpha.hom.app ((X, Y), Z)) ≫ (comparisonRight T V F m).hom.app ((X, Y), Z) =
      (comparisonLeft T V F m).hom.app ((X, Y), Z) ≫
        beta.hom.app ((F.obj X, F.obj Y), F.obj Z) := by
  have : IsIso (Prod.mkHom eY.hom eZ.hom) :=
    (inferInstance : IsIso (Iso.prod eY eZ).hom)
  have : IsIso (Prod.mkHom eX.hom (V.map (Prod.mkHom eY.hom eZ.hom))) :=
    (inferInstance : IsIso (Iso.prod eX (V.mapIso (Iso.prod eY eZ))).hom)
  apply (cancel_epi (F.map l.hom)).1
  apply (cancel_mono (V.map
    (Prod.mkHom eX.hom (V.map (Prod.mkHom eY.hom eZ.hom))))).1
  have hnat := beta.hom.naturality
    (Prod.mkHom (Prod.mkHom eX.hom eY.hom) eZ.hom)
  change V.map (Prod.mkHom (V.map (Prod.mkHom eX.hom eY.hom)) eZ.hom) ≫
      beta.hom.app ((X', Y'), Z') = beta.hom.app ((F.obj X, F.obj Y), F.obj Z) ≫
      V.map (Prod.mkHom eX.hom (V.map (Prod.mkHom eY.hom eZ.hom))) at hnat
  calc
    _ = F.map a ≫ F.map r.hom ≫ (comparisonRight T V F m).hom.app ((X, Y), Z) ≫
        V.map (Prod.mkHom eX.hom (V.map (Prod.mkHom eY.hom eZ.hom))) := by
      rw [← F.map_comp_assoc, hB, F.map_comp]
      simp only [Category.assoc]
    _ = F.map a ≫ eH ≫ r' := by rw [hR]
    _ = eW ≫ a' ≫ r' := by rw [reassoc_of% hC]
    _ = eW ≫ l' ≫ beta.hom.app ((X', Y'), Z') := by rw [hA]
    _ = F.map l.hom ≫ (comparisonLeft T V F m).hom.app ((X, Y), Z) ≫
        V.map (Prod.mkHom (V.map (Prod.mkHom eX.hom eY.hom)) eZ.hom) ≫
        beta.hom.app ((X', Y'), Z') := by rw [reassoc_of% hL]
    _ = _ := by rw [hnat]; simp only [Category.assoc]


private noncomputable def edgePullback {A B : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge A B) :
    CategoryTheory.CochainPullback.RingedPullback.{u, u, u, u, u} A.ring B.ring where
  uInv := e.inverse
  uPush := e.direct
  adj := e.adjunction
  finiteLimits := e.finiteLimits
  RI := e.inverseRing
  I := e.algebraic
  coefficient := e.ringMap
  L := e.pullback
  hobj := e.object_eq
  hmap := e.map_eq
  V := e.pushforward
  moduleAdj := e.moduleAdjunction

private noncomputable def edgeComparison {A B : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge A B) :
    CategoryTheory.CochainPullback.Comparison.{u, u, u, u, u} (edgePullback e) where
  q := e.ordinaryTensor.q
  q_one := e.ordinaryTensor.q_one
  mu := e.ordinaryTensor.mu
  naturality := e.ordinaryTensor.naturality
  pure := e.ordinaryTensor.pure

private theorem totalTensor_map {A : RingedTensorCorner.{u, w}}
    {P P' Q Q' : Complexes A} (x : P ⟶ P') (y : Q ⟶ Q') :
    (totalTensor A).map (Prod.mkHom x y) =
      HomologicalComplex.mapBifunctorMap x y A.mateTensor (.up ℤ) := by
  simp [totalTensor, Functor.map₂HomologicalComplex, HomologicalComplex.mapBifunctorMap,
    ← HomologicalComplex₂.total.map_comp]

set_option maxHeartbeats 1600000 in
-- Elaborate the nested tensor presentations with their specified representative data.
private theorem delta_associativity {A B : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge A B) (P Q N : Complexes A) :
    (pull e).map (totalAssociator A P Q N).hom ≫ delta e P (total A Q N) ≫
        (totalTensor B).map (Prod.mkHom (𝟙 _) (delta e Q N)) =
      delta e (total A P Q) N ≫
        (totalTensor B).map (Prod.mkHom (delta e P Q) (𝟙 _)) ≫
        (totalAssociator B ((pull e).obj P) ((pull e).obj Q) ((pull e).obj N)).hom := by
  let := monoidalCategory A.ring
  let := monoidalCategory B.ring
  let := symmetricCategory A.ring
  let := symmetricCategory B.ring
  let := ringedTensorPreadditive A.ring
  let := ringedTensorPreadditive B.ring
  let : MonoidalClosed A.mateModules := Classical.choice (tensorClosed A.ring).2.1
  let : MonoidalClosed B.mateModules := Classical.choice (tensorClosed B.ring).2.1
  let : Limits.HasColimitsOfSize.{0, 0} A.mateModules :=
    Limits.hasColimitsOfSizeShrink.{0, 0, u, u} _
  let : Limits.HasColimitsOfSize.{0, 0} B.mateModules :=
    Limits.hasColimitsOfSizeShrink.{0, 0, u, u} _
  have hc (P Q : Complexes A) :
      (CategoryTheory.CochainPullback.comparison (edgePullback e) (edgeComparison e) P Q).hom =
        delta e P Q := by
    unfold delta CategoryTheory.CochainPullback.comparison
      CochainTensorComparison.CanonicalRingedTensorComparison.totalIso
      CanonicalRingedTensorComparison.totalIso
      CochainTensorComparison.CanonicalRingedTensorComparison.total
      CanonicalRingedTensorComparison.total
    rfl
  have h := (CategoryTheory.CochainPullback.cochainComparison_monoidal
    (edgePullback e) (edgeComparison e)).2.1 P Q N
  simp only [hc] at h
  simp only [totalTensor_map]
  exact h

private noncomputable def associatorIso (A : RingedTensorCorner.{u, w})
    (a : RingedTensorModel A) (c : TensorConstraints A a) :
    (A.tensor.prod (𝟭 _)) ⋙ A.tensor ≅
      CategoryTheory.prod.associator _ _ _ ⋙ ((𝟭 _).prod A.tensor) ⋙ A.tensor :=
  NatIso.ofComponents (fun z ↦ c.associator z.1.1 z.1.2 z.2)
    (fun f ↦ c.associator_naturality f.1.1 f.1.2 f.2)

private noncomputable def totalModel (A : RingedTensorCorner.{u, w})
    (p q : A.mateFlat.FullSubcategory) : A.mateFlat.FullSubcategory :=
  ⟨total A p.obj q.obj, total_good p.property q.property⟩

private noncomputable def leftRepresentative (A : RingedTensorCorner.{u, w})
    (a : RingedTensorModel A) (p q n : A.mateFlat.FullSubcategory) :
    DerivedCategory.Q.obj (total A (total A p.obj q.obj) n.obj) ≅
      A.tensor.obj (A.tensor.obj (DerivedCategory.Q.obj p.obj, DerivedCategory.Q.obj q.obj),
        DerivedCategory.Q.obj n.obj) :=
  a.representative.app (totalModel A p q, n) ≪≫
    A.tensor.mapIso (Iso.prod (a.representative.app (p, q)) (Iso.refl _))

private noncomputable def rightRepresentative (A : RingedTensorCorner.{u, w})
    (a : RingedTensorModel A) (p q n : A.mateFlat.FullSubcategory) :
    DerivedCategory.Q.obj (total A p.obj (total A q.obj n.obj)) ≅
      A.tensor.obj (DerivedCategory.Q.obj p.obj,
        A.tensor.obj (DerivedCategory.Q.obj q.obj, DerivedCategory.Q.obj n.obj)) :=
  a.representative.app (p, totalModel A q n) ≪≫
    A.tensor.mapIso (Iso.prod (Iso.refl _) (a.representative.app (q, n)))

private theorem representative_associativity (A : RingedTensorCorner.{u, w})
    (a : RingedTensorModel A) (c : TensorConstraints A a)
    (p q n : A.mateFlat.FullSubcategory) :
    (leftRepresentative A a p q n).hom ≫
        (c.associator (DerivedCategory.Q.obj p.obj) (DerivedCategory.Q.obj q.obj)
          (DerivedCategory.Q.obj n.obj)).hom =
      DerivedCategory.Q.map (totalAssociator A p.obj q.obj n.obj).hom ≫
        (rightRepresentative A a p q n).hom := by
  obtain ⟨hpq, hqn, h⟩ := c.associator_representative p.obj q.obj n.obj
    p.property q.property n.property
  dsimp only [leftRepresentative, rightRepresentative, Iso.trans_hom,
    Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom]
  erw [Category.assoc]
  exact h

set_option maxHeartbeats 1600000 in
-- Elaborate the nested tensor presentations with their specified representative data.
private theorem associativity_model {X Y : RingedTensorCorner.{u, w}}
    (f : RingedTensorEdge Y X) (a : RingedTensorModel X) (b : RingedTensorModel Y)
    (ca : TensorConstraints X a) (cb : TensorConstraints Y b)
    (p q n : Y.mateFlat.FullSubcategory) :
    f.left.map ((associatorIso Y b cb).hom.app
        ((DerivedCategory.Q.obj p.obj, DerivedCategory.Q.obj q.obj),
          DerivedCategory.Q.obj n.obj)) ≫
        (comparisonRight Y.tensor X.tensor f.left (f.tensorComparison b a)).hom.app
          ((DerivedCategory.Q.obj p.obj, DerivedCategory.Q.obj q.obj),
            DerivedCategory.Q.obj n.obj) =
      (comparisonLeft Y.tensor X.tensor f.left (f.tensorComparison b a)).hom.app
          ((DerivedCategory.Q.obj p.obj, DerivedCategory.Q.obj q.obj),
            DerivedCategory.Q.obj n.obj) ≫
        (associatorIso X a ca).hom.app
          ((f.left.obj (DerivedCategory.Q.obj p.obj), f.left.obj (DerivedCategory.Q.obj q.obj)),
            f.left.obj (DerivedCategory.Q.obj n.obj)) := by
  let T := Y.tensor
  let V := X.tensor
  let U := f.left
  let m := f.tensorComparison b a
  let pm : Y.mateFlat.FullSubcategory → X.mateFlat.FullSubcategory :=
    fun E ↦ ⟨(pull f).obj E.obj, pull_good f E.property⟩
  let pq := totalModel Y p q
  let qn := totalModel Y q n
  let pp := pm p
  let qq := pm q
  let nn := pm n
  let apq := totalModel X pp qq
  let aqn := totalModel X qq nn
  let bPQ := b.representative.app (p, q)
  let bQN := b.representative.app (q, n)
  let bL := b.representative.app (pq, n)
  let bR := b.representative.app (p, qn)
  let aPQ := a.representative.app (pp, qq)
  let aQN := a.representative.app (qq, nn)
  let aL := a.representative.app (apq, nn)
  let aR := a.representative.app (pp, aqn)
  let aL₀ := a.representative.app (pm pq, nn)
  let aR₀ := a.representative.app (pp, pm qn)
  let lB := leftRepresentative Y b p q n
  let rB := rightRepresentative Y b p q n
  let lA := leftRepresentative X a pp qq nn
  let rA := rightRepresentative X a pp qq nn
  let cPQ := delta f p.obj q.obj
  let cQN := delta f q.obj n.obj
  let cL := delta f pq.obj n.obj
  let cR := delta f p.obj qn.obj
  let eL := comparison f (total Y pq.obj n.obj) ≫
    DerivedCategory.Q.map cL ≫
      DerivedCategory.Q.map ((totalTensor X).map (Prod.mkHom cPQ (𝟙 nn.obj)))
  let eR := comparison f (total Y p.obj qn.obj) ≫
    DerivedCategory.Q.map cR ≫
      DerivedCategory.Q.map ((totalTensor X).map (Prod.mkHom (𝟙 pp.obj) cQN))
  have hm (E F : Y.mateFlat.FullSubcategory) :
      U.map (b.representative.app (E, F)).hom ≫
        m.hom.app (DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj) ≫
        V.map (Prod.mkHom (comparison f E.obj) (comparison f F.obj)) =
      comparison f (total Y E.obj F.obj) ≫
        DerivedCategory.Q.map (delta f E.obj F.obj) ≫
        (a.representative.app (pm E, pm F)).hom :=
    edge_equation f b a E.obj F.obj E.property F.property
  have hB := representative_associativity Y b cb p q n
  have hA := representative_associativity X a ca pp qq nn
  have hnL := a.representative.hom.naturality
    (Prod.mkHom (ObjectProperty.homMk cPQ : pm pq ⟶ apq) (𝟙 nn))
  have hnR := a.representative.hom.naturality
    (Prod.mkHom (𝟙 pp) (ObjectProperty.homMk cQN : pm qn ⟶ aqn))
  simp only [Functor.comp_map, Functor.prod_map, ObjectProperty.ι_map,
    ObjectProperty.FullSubcategory.id_hom, ObjectProperty.homMk_hom] at hnL hnR
  erw [DerivedCategory.Q.map_id] at hnL
  erw [DerivedCategory.Q.map_id] at hnR
  change DerivedCategory.Q.map ((totalTensor X).map (Prod.mkHom cPQ (𝟙 nn.obj))) ≫
      aL.hom = aL₀.hom ≫ V.map (Prod.mkHom (DerivedCategory.Q.map cPQ) (𝟙 _)) at hnL
  change DerivedCategory.Q.map ((totalTensor X).map (Prod.mkHom (𝟙 pp.obj) cQN)) ≫
      aR.hom = aR₀.hom ≫ V.map (Prod.mkHom (𝟙 _) (DerivedCategory.Q.map cQN)) at hnR
  have hL₀ := nestedComparison_left T V U m.hom bPQ.hom bL.hom
    (comparison f p.obj) (comparison f q.obj) (comparison f n.obj) (comparison f pq.obj)
    (comparison f (total Y pq.obj n.obj))
    (DerivedCategory.Q.map cPQ ≫ aPQ.hom) (DerivedCategory.Q.map cL ≫ aL₀.hom)
    (hm p q) (hm pq n)
  have hR₀ := nestedComparison_right T V U m.hom bQN.hom bR.hom
    (comparison f p.obj) (comparison f q.obj) (comparison f n.obj) (comparison f qn.obj)
    (comparison f (total Y p.obj qn.obj))
    (DerivedCategory.Q.map cQN ≫ aQN.hom) (DerivedCategory.Q.map cR ≫ aR₀.hom)
    (hm q n) (hm p qn)
  have hL : U.map lB.hom ≫ (comparisonLeft T V U m).hom.app
      ((DerivedCategory.Q.obj p.obj, DerivedCategory.Q.obj q.obj),
        DerivedCategory.Q.obj n.obj) ≫
      V.map (Prod.mkHom (V.map (Prod.mkHom (comparison f p.obj) (comparison f q.obj)))
        (comparison f n.obj)) = eL ≫ lA.hom := by
    simp only [comparisonLeft, Iso.trans_hom, NatTrans.comp_app,
      isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
      NatIso.prod_hom, NatTrans.prod, Iso.refl_hom, NatTrans.id_app, Functor.prod_obj,
      Functor.id_obj, Functor.comp_obj, Category.assoc]
    calc
      _ = comparison f (total Y pq.obj n.obj) ≫ (DerivedCategory.Q.map cL ≫ aL₀.hom) ≫
          V.map (Prod.mkHom (DerivedCategory.Q.map cPQ ≫ aPQ.hom) (𝟙 _)) := hL₀
      _ = _ := by
        rw [show V.map (Prod.mkHom (DerivedCategory.Q.map cPQ ≫ aPQ.hom) (𝟙 _)) =
          V.map (Prod.mkHom (DerivedCategory.Q.map cPQ) (𝟙 _)) ≫
            V.map (Prod.mkHom aPQ.hom (𝟙 _)) by
            simp only [← V.map_comp, CategoryTheory.prod_comp, Prod.mkHom, Category.id_comp]]
        simp only [Category.assoc]
        erw [← reassoc_of% hnL]
        simp only [eL, lA, leftRepresentative, Iso.trans_hom,
          Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom, Category.assoc]
        rfl
  have hR : U.map rB.hom ≫ (comparisonRight T V U m).hom.app
      ((DerivedCategory.Q.obj p.obj, DerivedCategory.Q.obj q.obj),
        DerivedCategory.Q.obj n.obj) ≫
      V.map (Prod.mkHom (comparison f p.obj)
        (V.map (Prod.mkHom (comparison f q.obj) (comparison f n.obj)))) = eR ≫ rA.hom := by
    simp only [comparisonRight, Iso.trans_hom, NatTrans.comp_app,
      isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
      NatIso.prod_hom, NatTrans.prod, Iso.refl_hom, NatTrans.id_app, Functor.prod_obj,
      Functor.id_obj, Functor.comp_obj, CategoryTheory.prod.associator, Category.assoc]
    calc
      _ = comparison f (total Y p.obj qn.obj) ≫ (DerivedCategory.Q.map cR ≫ aR₀.hom) ≫
          V.map (Prod.mkHom (𝟙 _) (DerivedCategory.Q.map cQN ≫ aQN.hom)) := hR₀
      _ = _ := by
        rw [show V.map (Prod.mkHom (𝟙 _) (DerivedCategory.Q.map cQN ≫ aQN.hom)) =
          V.map (Prod.mkHom (𝟙 _) (DerivedCategory.Q.map cQN)) ≫
            V.map (Prod.mkHom (𝟙 _) aQN.hom) by
            simp only [← V.map_comp, CategoryTheory.prod_comp, Prod.mkHom, Category.id_comp]]
        simp only [Category.assoc]
        erw [← reassoc_of% hnR]
        simp only [eR, rA, rightRepresentative, Iso.trans_hom,
          Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom, Category.assoc]
        rfl
  have hC : U.map (DerivedCategory.Q.map (totalAssociator Y p.obj q.obj n.obj).hom) ≫ eR =
      eL ≫ DerivedCategory.Q.map (totalAssociator X pp.obj qq.obj nn.obj).hom := by
    have hf := comparison_naturality f (totalAssociator Y p.obj q.obj n.obj).hom
    dsimp only [eL, eR]
    erw [reassoc_of% hf]
    simpa only [Functor.map_comp, Category.assoc, cPQ, cQN, cL, cR,
      pp, qq, nn, pm, pq, qn, totalModel] using
      congrArg (fun z ↦ comparison f (total Y pq.obj n.obj) ≫ DerivedCategory.Q.map z)
        (delta_associativity f p.obj q.obj n.obj)
  have ip : IsIso (comparison f p.obj) := comparison_isIso f p.property
  have iq : IsIso (comparison f q.obj) := comparison_isIso f q.property
  have ih : IsIso (comparison f n.obj) := comparison_isIso f n.property
  exact associativity_from_representatives T V U m (associatorIso Y b cb)
    (associatorIso X a ca) lB rB (DerivedCategory.Q.map (totalAssociator Y p.obj q.obj n.obj).hom)
    lA.hom rA.hom (DerivedCategory.Q.map (totalAssociator X pp.obj qq.obj nn.obj).hom)
    (asIso (comparison f p.obj)) (asIso (comparison f q.obj)) (asIso (comparison f n.obj))
    eL eR hB hA hL hR hC

private theorem flat_representative (A : RingedTensorCorner.{u, w}) (E : A.mateDerived) :
    ∃ p : A.mateFlat.FullSubcategory, Nonempty (DerivedCategory.Q.obj p.obj ≅ E) := by
  obtain ⟨P, f, hp, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := A.ring) (DerivedCategory.Q.objPreimage E)
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hq
  exact ⟨⟨P, hp, hf⟩, ⟨asIso (DerivedCategory.Q.map f) ≪≫
    DerivedCategory.Q.objObjPreimageIso E⟩⟩

set_option maxHeartbeats 1600000 in
-- Elaborate the nested tensor presentations with their specified representative data.
private theorem associativity_all {X Y : RingedTensorCorner.{u, w}}
    (f : RingedTensorEdge Y X) (a : RingedTensorModel X) (b : RingedTensorModel Y)
    (ca : TensorConstraints X a) (cb : TensorConstraints Y b) (E Q N : Y.mateDerived) :
    f.left.map (cb.associator E Q N).hom ≫
        (f.tensorComparison b a).hom.app (E, Y.tensor.obj (Q, N)) ≫
        X.tensor.map (Prod.mkHom (𝟙 _) ((f.tensorComparison b a).hom.app (Q, N))) =
      (f.tensorComparison b a).hom.app (Y.tensor.obj (E, Q), N) ≫
        X.tensor.map (Prod.mkHom ((f.tensorComparison b a).hom.app (E, Q)) (𝟙 _)) ≫
        (ca.associator (f.left.obj E) (f.left.obj Q) (f.left.obj N)).hom := by
  let U := f.left
  let T := Y.tensor
  let V := X.tensor
  let m := f.tensorComparison b a
  let s := associatorIso Y b cb
  let t := associatorIso X a ca
  let lhs := isoWhiskerRight s U ≪≫ comparisonRight T V U m
  let rhs := comparisonLeft T V U m ≪≫ isoWhiskerLeft ((U.prod U).prod U) t
  have h : lhs.hom.app ((E, Q), N) = rhs.hom.app ((E, Q), N) := by
    obtain ⟨p, ⟨ep⟩⟩ := flat_representative Y E
    obtain ⟨q, ⟨eq⟩⟩ := flat_representative Y Q
    obtain ⟨n, ⟨en⟩⟩ := flat_representative Y N
    let e := Iso.prod (Iso.prod ep eq) en
    apply (cancel_epi ((((T.prod (𝟭 _)) ⋙ T) ⋙ U).map e.hom)).1
    rw [lhs.hom.naturality, rhs.hom.naturality]
    apply congrArg (fun z ↦ z ≫ _)
    exact associativity_model f a b ca cb p q n
  simpa only [lhs, rhs, s, t, associatorIso, comparisonLeft, comparisonRight,
    Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    whiskerLeft_app, whiskerRight_app, NatIso.prod_hom, NatTrans.prod,
    Functor.prod_obj, Functor.id_obj, CategoryTheory.prod.associator,
    Functor.comp_obj, Iso.refl_hom, NatTrans.id_app, Category.assoc,
    NatIso.ofComponents_hom_app, T, V, U, m] using h

set_option maxHeartbeats 1600000 in
-- The three nested tensor comparison components require additional elaboration heartbeats.
/-- Associativity law for a normalized ringed projection tensor comparison.
Source: Stacks Project, Tags 06YS, 06YU and 07A4; flat K-flat tensor descent.
The proof restricts to flat K-flat representatives, applies the signed cochain
pullback tensor equation, and descends the equality through the localization.
(blueprint: lem-sfb-ringed-projection-tensor-laws-associativity-law) -/
theorem ringedProjectionAssociativityLaw
    (constraints : ∀ (X : RingedTensorCorner.{u, w}) (a : RingedTensorModel X),
      TensorConstraints X a) :
    ∀ {X Y : RingedTensorCorner.{u, w}} (f : RingedTensorEdge Y X)
      (a : RingedTensorModel X) (b : RingedTensorModel Y) (E Q N : Y.mateDerived),
      f.left.map ((constraints Y b).associator E Q N).inv ≫
          (f.tensorComparison b a).hom.app (Y.tensor.obj (E, Q), N) ≫
          X.tensor.map (Prod.mkHom ((f.tensorComparison b a).hom.app (E, Q))
            (𝟙 (f.left.obj N))) =
        (f.tensorComparison b a).hom.app (E, Y.tensor.obj (Q, N)) ≫
          X.tensor.map (Prod.mkHom (𝟙 (f.left.obj E))
            ((f.tensorComparison b a).hom.app (Q, N))) ≫
          ((constraints X a).associator (f.left.obj E) (f.left.obj Q)
            (f.left.obj N)).inv := by
  intro X Y f a b E Q N
  have h := associativity_all f a b (constraints X a) (constraints Y b) E Q N
  apply (cancel_epi (f.left.map ((constraints Y b).associator E Q N).hom)).1
  apply (cancel_mono ((constraints X a).associator (f.left.obj E) (f.left.obj Q)
    (f.left.obj N)).hom).1
  simp only [Category.assoc]
  erw [← f.left.map_comp_assoc, Iso.hom_inv_id, f.left.map_id, Category.id_comp]
  erw [Iso.inv_hom_id, Category.comp_id]
  exact h.symm

end SheafOfModules.ProjectionCoherence
