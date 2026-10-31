/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CommonQuotientPullbackData
import WeilConjectures.AlgebraicGeometry.CommonQuotientOrdinaryInsertion
import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
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
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
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
import all WeilConjectures.AlgebraicGeometry.RingedCoefficientPullbackComparisonSupplement

/-! # Invertibility of scalar insertion after common-quotient reduction

Source: Stacks Project, Tags 06YY, 0G7E, 03EK, 03EL.
(blueprint: lem-weil-pbc-common-quotient-insertion-finite).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SemilinearSections (Mod D)
open SheafOfModules.RingedCoefficientProjection
open SheafOfModules.SuccessiveDerivedQuotient (restriction sectionTensor)
namespace SheafOfModules.CommonQuotientPullback

variable {C X : Type c} [Category.{v} C] [Category.{v} X]
  [EssentiallySmall.{r} C] [EssentiallySmall.{r} X]
  {J : GrothendieckTopology C} {K : GrothendieckTopology X}
  {uInv : Sheaf J (Type r) ⥤ Sheaf K (Type r)}
  {uPush : Sheaf K (Type r) ⥤ Sheaf J (Type r)} {adj : uInv ⊣ uPush}
  (g : Geometry uInv uPush adj)
  {pY : Scalars.{c, v, r} J} {pX : Scalars.{c, v, r} K}
  (nY : SuccessiveDerivedQuotient.Normalization (J := J) pY)
  (nX : SuccessiveDerivedQuotient.Normalization (J := K) pX)
  {R B : Sheaf J CommRingCat.{r}} (φ : R ⟶ B)
  {B' : Sheaf K CommRingCat.{r}} (a : g.rings.obj B ⟶ B')


variable (Q : CommonQuotientTowerPresentation φ)
  (b : (Functor.const ℕᵒᵖ).obj B' ⟶ Q.S ⋙ g.rings)


/-- Reduction to a compatible common quotient makes the normalized scalar insertion
invertible, retaining the actual quotient-module action.

Source: Stacks Project, sites-cohomology.tex, Tags 06YY, 0G7E;
sites-modules.tex, Tags 03EK, 03EL.
(blueprint: lem-weil-pbc-common-quotient-insertion-finite).

Proof: the ordinary common-quotient insertion theorem makes extension of the
ordinary insertion an isomorphism on every module. Choose a flat-term K-flat
B-complex P resolving the input. Flatness of B/R makes restriction K-flat with
flat terms, and inverse image preserves this property. Ringed pullback sends P
to a K-flat complex with flat terms; flatness of Bprime over g(R) makes its
restriction K-flat with flat terms as well. The normalized quotient counits
therefore compute both reductions by ordinary scalar extension on these
complexes. Apply derived quotient extension to the Insertion representative
square and paste it with naturality of the quotient computation counit. Its
ordinary term is a degreewise chain isomorphism by the first step. The source
and target computation maps and quotient counits are invertible, so cancellation
makes the reduced derived insertion invertible on P. Naturality along the chosen
resolution isomorphism transfers invertibility to every derived object. No
identity or composition coherence is used in this finite assertion. -/
theorem insertion_finite_isIso [PreservesFiniteLimits uInv]
    (hflat : IsFlatOnSite (J := J) (R := R)
      ((restriction φ).obj (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))))
    (hflat' : IsFlatOnSite (J := K) (R := g.rings.obj R)
      ((restriction (g.rings.map φ ≫ a)).obj
        (unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B'))))
    (hquotient : ∀ n : ℕ, IsPushout (g.rings.map φ ≫ a)
      (quotient g φ Q n) (b.app (op n)) (𝟙 _))
    (hcompatible : ∀ n : ℕ, a ≫ b.app (op n) = g.rings.map (Q.extensionProjection n))
    (i : Insertion g nY nX φ a) (n : ℕ) :
    IsIso (Functor.whiskerRight i.derived (pX (quotient g φ Q n)).derived) := by
  have ho := ordinary_insertion_reduction_isIso g nY nX φ a Q b
    hquotient hcompatible i.ordinary i.sections n
  let q := quotient g φ Q n
  let E := (pX q).derived
  let F := (pX q).ordinary
  have rep (P : CochainComplex (Mod J B) ℤ) (hk : P.IsKFlatIndependentCoefficients)
      (hf : ∀ j : ℤ, IsFlatOnSite (J := J) (R := B) (P.X j)) :
      IsIso (E.map (i.derived.app (DerivedCategory.Q.obj P))) := by
    let H := (HomotopyCategory.quotient (Mod J B) (.up ℤ)).obj P
    let S := ((ordinarySource g φ).mapHomologicalComplex (.up ℤ)).obj P
    let T := ((ordinaryTarget g (pX := pX) φ a).mapHomologicalComplex (.up ℤ)).obj P
    obtain ⟨hs, hsf⟩ := isKFlat_restrictScalars_of_flat φ hflat P hk
    have hS := inverse_preserves_flat g nX R
      (((restriction φ).mapHomologicalComplex (.up ℤ)).obj P) hs (hsf hf)
    have hF := isKFlat_ringedToposPullback uInv uPush adj (g.inverse B) a
      (ordinaryPullback g (pX := pX) a)
      (fun M ↦ (pX a).obj_eq ((g.inverse B).modules.obj M))
      (fun f ↦ (pX a).map_eq ((g.inverse B).modules.map f)) P hk hf
    have hT := isKFlat_restrictScalars_of_flat (g.rings.map φ ≫ a) hflat'
      (((ordinaryPullback g (pX := pX) a).mapHomologicalComplex (.up ℤ)).obj P) hF.1
    have hSc := nX.computed q S hS.1 hS.2
    have hTc := nX.computed q T hT.1 (hT.2 hF.2)
    change IsIso ((pX q).counit.app
      (((ordinarySource g φ).mapHomotopyCategory (.up ℤ)).obj H)) at hSc
    change IsIso ((pX q).counit.app
      (((ordinaryTarget g (pX := pX) φ a).mapHomotopyCategory (.up ℤ)).obj H)) at hTc
    have hsc : IsIso (sourceComputation g nY φ H) := by
      dsimp only [sourceComputation]
      infer_instance
    have htc : IsIso (targetComputation g nX φ a H) := by
      obtain ⟨hi, ht⟩ := inverse_preserves_flat g nX B P hk hf
      have hc := nX.computed a
        (((g.inverse B).modules.mapHomologicalComplex (.up ℤ)).obj P) hi ht
      change IsIso ((pX a).counit.app
        (((g.inverse B).modules.mapHomotopyCategory (.up ℤ)).obj H)) at hc
      dsimp only [targetComputation, pullbackComputation]
      infer_instance
    let α := (NatTrans.mapHomotopyCategory i.ordinary (.up ℤ)).app H
    have hα : IsIso ((F.mapHomotopyCategory (.up ℤ)).map α) := by
      let f := ((F.mapHomologicalComplex (.up ℤ))).map
        ((NatTrans.mapHomologicalComplex i.ordinary (.up ℤ)).app P)
      have hfj (j : ℤ) : IsIso (f.f j) := by
        change IsIso ((Functor.whiskerRight i.ordinary F).app (P.X j))
        infer_instance
      have : IsIso f := HomologicalComplex.Hom.isIso_of_components f
      change IsIso ((HomotopyCategory.quotient
        (Mod K (g.rings.obj (Q.S.obj (op n)))) (.up ℤ)).map f)
      infer_instance
    have hnat := (pX q).counit.naturality α
    dsimp only [Functor.comp_map] at hnat
    have hr := congrArg E.map (i.representative P hk hf)
    simp only [Functor.map_comp] at hr
    have he : E.map (i.derived.app (DerivedCategory.Q.obj P)) ≫
        E.map (targetComputation g nX φ a H) ≫
        (pX q).counit.app (((ordinaryTarget g (pX := pX) φ a).mapHomotopyCategory
          (.up ℤ)).obj H) =
      E.map (sourceComputation g nY φ H) ≫
        (pX q).counit.app (((ordinarySource g φ).mapHomotopyCategory (.up ℤ)).obj H) ≫
          DerivedCategory.Qh.map ((F.mapHomotopyCategory (.up ℤ)).map α) := by
      rw [← Category.assoc]
      erw [hr]
      rw [Category.assoc]
      erw [hnat]
    have ht : IsIso (E.map (targetComputation g nX φ a H) ≫
        (pX q).counit.app (((ordinaryTarget g (pX := pX) φ a).mapHomotopyCategory
          (.up ℤ)).obj H)) := by infer_instance
    have : IsIso (E.map (i.derived.app (DerivedCategory.Q.obj P)) ≫
        (E.map (targetComputation g nX φ a H) ≫
          (pX q).counit.app (((ordinaryTarget g (pX := pX) φ a).mapHomotopyCategory
            (.up ℤ)).obj H))) := by
      rw [he]
      infer_instance
    exact IsIso.of_isIso_comp_right (E.map (i.derived.app (DerivedCategory.Q.obj P)))
      (E.map (targetComputation g nX φ a H) ≫
        (pX q).counit.app (((ordinaryTarget g (pX := pX) φ a).mapHomotopyCategory
          (.up ℤ)).obj H))
  have happ (M : D J B) :
      IsIso ((Functor.whiskerRight i.derived (pX (quotient g φ Q n)).derived).app M) := by
    let A := flatHomotopy (J := J) B
    let L := A.ι ⋙ (DerivedCategory.Qh : HomotopyCategory (Mod J B) (.up ℤ) ⥤ D J B)
    let W := (HomotopyCategory.quasiIso (Mod J B) (.up ℤ)).inverseImage A.ι
    have : L.IsLocalization W := flat_localization (J := J) B
    have : L.EssSurj := Localization.essSurj L W
    obtain ⟨H, ⟨eP⟩⟩ := Functor.EssSurj.mem_essImage L M
    let P := H.obj.as
    let τ := Functor.whiskerRight i.derived E
    have hrep := rep P H.property.1 H.property.2
    change IsIso (τ.app (L.obj H)) at hrep
    have h := τ.naturality eP.hom
    have h' : IsIso (τ.app (L.obj H) ≫ (target g nX φ a ⋙ E).map eP.hom) := by
      infer_instance
    have : IsIso ((source g nY φ ⋙ E).map eP.hom ≫ τ.app M) := by
      rw [h]
      exact h'
    exact IsIso.of_isIso_comp_left ((source g nY φ ⋙ E).map eP.hom) (τ.app M)
  have : ∀ M, IsIso
      ((Functor.whiskerRight i.derived (pX (quotient g φ Q n)).derived).app M) := happ
  exact NatIso.isIso_of_isIso_app _

end SheafOfModules.CommonQuotientPullback
