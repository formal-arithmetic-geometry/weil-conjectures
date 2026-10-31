/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.Logic.Small.Defs
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.FiniteRestrictionPinnedTotalSquare
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.FiniteRestrictionRepresentativeSquare
import WeilConjectures.Algebra.Homology.CochainTensorModelRigidity
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
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
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses

/-! # Finite tensor restriction coherence

(blueprint: lem-sf-finite-tensor-restriction-coherence)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
namespace SheafOfModules.OpenTensorNormalization

set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048
attribute [local implicit_reducible] CategoryTheory.Functor.mapHomologicalComplex
  CategoryTheory.Functor.map₂HomologicalComplex

private theorem resolving_of_iso {X : Scheme.{u}}
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    {P Q : CochainComplex (Mod R) ℤ} (a : P ≅ Q) (hQ : resolving R Q) :
    resolving R P := by
  let := SheafOfModules.monoidalCategory R
  constructor
  · intro F hF
    exact HomologicalComplex.Acyclic.of_iso (hQ.1 F hF)
      ((total R).mapIso (Iso.prod (Iso.refl F) a.symm))
  · intro n
    have hcat : exactFunctor _ _ (tensorRight (Q.X n)) :=
      (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (Q.X n)) (hQ.2 n)
    have hcat' : exactFunctor _ _ (tensorRight (P.X n)) :=
      (exactFunctor _ _).prop_of_iso
        ((curriedTensor (Mod R)).flip.mapIso
          ((HomologicalComplex.eval _ _ n).mapIso a.symm)) hcat
    exact (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (P.X n)).symm hcat'

private theorem natTrans_app_eq_of_iso
    {C D : Type*} [Category* C] [Category* D] {F G : C ⥤ D}
    (a b : F ⟶ G) {X Y : C} (i : X ≅ Y) (h : a.app X = b.app X) :
    a.app Y = b.app Y := by
  apply (cancel_epi (F.map i.hom)).1
  rw [a.naturality, b.naturality, h]

private theorem finite_representatives_ext
    {A : Type (u + 1)} [CommRing A] {X : Scheme.{u}}
    {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {i : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
    (e : FiniteRealization A X R i)
    {E : Type*} [Category* E] {F G : FiniteD A X × FiniteD A X ⥤ E}
    (a b : F ⟶ G)
    (h : ∀ (P Q : CochainComplex (FiniteModules A X) ℤ),
      resolving R ((finiteComplexRealization e).obj P) →
      resolving R ((finiteComplexRealization e).obj Q) →
      a.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
        b.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) : a = b := by
  let eC := e.equivalence.mapHomologicalComplex (.up ℤ)
  let eD := e.equivalence.mapDerivedCategory
  have hinv : eD.inverse.IsEquivalence := inferInstance
  have heq : Functor.whiskerLeft (eD.inverse.prod eD.inverse) a =
      Functor.whiskerLeft (eD.inverse.prod eD.inverse) b := by
    obtain ⟨_, _, _, hdesc⟩ := cochain_tensor_model_rigidity (ProEt.topology X) R
    apply (hdesc E inferInstance _ _).1
    apply NatTrans.ext
    funext Z
    let P := eC.inverse.obj Z.1.obj
    let Q := eC.inverse.obj Z.2.obj
    have hp : resolving R ((finiteComplexRealization e).obj P) :=
      resolving_of_iso R (eC.counitIso.app Z.1.obj) Z.1.property
    have hq : resolving R ((finiteComplexRealization e).obj Q) :=
      resolving_of_iso R (eC.counitIso.app Z.2.obj) Z.2.property
    let p : DerivedCategory.Q.obj P ≅ eD.inverse.obj (DerivedCategory.Q.obj Z.1.obj) :=
      eD.unitIso.app _ ≪≫ eD.inverse.mapIso
        (e.equivalence.functor.mapDerivedCategoryFactors.app P ≪≫
          DerivedCategory.Q.mapIso (eC.counitIso.app Z.1.obj))
    let q : DerivedCategory.Q.obj Q ≅ eD.inverse.obj (DerivedCategory.Q.obj Z.2.obj) :=
      eD.unitIso.app _ ≪≫ eD.inverse.mapIso
        (e.equivalence.functor.mapDerivedCategoryFactors.app Q ≪≫
          DerivedCategory.Q.mapIso (eC.counitIso.app Z.2.obj))
    exact natTrans_app_eq_of_iso a b (Iso.prod p q) (h P Q hp hq)
  apply NatTrans.ext
  funext Z
  exact natTrans_app_eq_of_iso a b
    (Iso.prod (eD.unitIso.app Z.1).symm (eD.unitIso.app Z.2).symm)
    (congrArg (fun t ↦ t.app (eD.functor.obj Z.1, eD.functor.obj Z.2)) heq)

/-- Restriction of the derived tensor product commutes with the pinned finite
realizations, with exact restriction in the first variable and total left-derived
restriction in the second. No extension-by-zero comparison or projection arrow
occurs in this square.

Source: Stacks 03EK, 06YN, 06YU and 0GL1; the tensor step in the proof of
lem-sf-finite-compatibility-transport.
Proof: on a pair of resolving complexes, evaluate both routes at each bidegree
summand. The open pin's section normalization and each tensor pin's pure-summand
equation identify the two images of a pure tensor with the same pair of
restricted sections. Operations.restrictionTensor preserves these pure tensors.
Bilinearity and sheafification extend equality to every tensor summand; the
coproduct universal property extends it to the signed total complex. Naturality
makes this a chain-map equality, with identical signs on both differentials.
Use the tensor pins' model equations and the exact restriction model equations
to descend the equality on resolving pairs. The universal properties of the
derived bifunctors extend it to all objects; the canonical exact/left-derived
comparison in the second variable gives precisely the displayed mixed square.
(blueprint: lem-sf-finite-tensor-restriction-coherence) -/
theorem finite_tensor_restriction_coherence
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) (sq : OpenImmersionSquare gU j' j g)
    [IsOpenImmersion j] [IsOpenImmersion j']
    {t : SiteSquare (finiteInput A gU j' j g sq)}
    (o : Operations (finiteInput A gU j' j g sq) t)
    (e : FiniteComparisons A o) :
    let r := Functor.isoWhiskerRight
      (ProEtale.upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctorIsoMapDerivedCategory.symm
      e.realizeU.derived ≪≫ e.openPull
    ∀ M N : FiniteD A X,
      e.realizeU.derived.map
          (((ProEtale.mapDerivedCategoryUpperStarDerivedTensorIso
            (ModuleCat.{u + 1} A) j).hom.app M).app N) ≫
        r.hom.app ((finiteTensor A X).obj (M, N)) ≫
        o.opens.jStar.map (e.tensorX.hom.app (M, N)) =
      e.tensorU.hom.app ((finitePull A j).obj M,
          (ProEtale.upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor.obj N) ≫
        o.tensorU.functor.map
          (CategoryTheory.Prod.mkHom (r.hom.app M) (e.openPull.hom.app N)) ≫
        o.tensorComparison.comparison.inv.app
          (e.realizeX.derived.obj M, e.realizeX.derived.obj N) := by
  dsimp only
  let F := ProEtale.upperStar (ModuleCat.{u + 1} A) j
  let r := Functor.isoWhiskerRight F.leftDerivedFunctorIsoMapDerivedCategory.symm
    e.realizeU.derived ≪≫ e.openPull
  let delta : (F.mapDerivedCategory.prod F.leftDerivedFunctor) ⋙ finiteTensor A U ⟶
      finiteTensor A X ⋙ F.mapDerivedCategory := by
    let d := Functor.uncurry.map
      (ProEtale.mapDerivedCategoryUpperStarDerivedTensorIso (ModuleCat.{u + 1} A) j).hom
    refine { app := fun Z ↦ d.app Z, naturality := ?_ }
    intro Z W f
    have hd := d.naturality f
    dsimp [finiteTensor, F, Functor.whiskeringLeft₂, Functor.postcompose₂,
      Functor.whiskeringLeft, Functor.whiskeringRight] at hd ⊢
    simpa only [Functor.map_comp] using hd
  let a : (F.mapDerivedCategory.prod F.leftDerivedFunctor) ⋙ finiteTensor A U ⋙
      e.realizeU.derived ⟶
      (e.realizeX.derived.prod e.realizeX.derived) ⋙ o.tensorX.functor ⋙ o.opens.jStar :=
    Functor.whiskerRight delta e.realizeU.derived ≫
      Functor.whiskerLeft (finiteTensor A X) r.hom ≫
        Functor.whiskerRight e.tensorX.hom o.opens.jStar
  let b : (F.mapDerivedCategory.prod F.leftDerivedFunctor) ⋙ finiteTensor A U ⋙
      e.realizeU.derived ⟶
      (e.realizeX.derived.prod e.realizeX.derived) ⋙ o.tensorX.functor ⋙ o.opens.jStar :=
    Functor.whiskerLeft (F.mapDerivedCategory.prod F.leftDerivedFunctor) e.tensorU.hom ≫
      Functor.whiskerRight (NatTrans.prod r.hom e.openPull.hom) o.tensorU.functor ≫
        Functor.whiskerLeft (e.realizeX.derived.prod e.realizeX.derived)
          o.tensorComparison.comparison.inv
  have hab : a = b := by
    apply finite_representatives_ext e.realizeX a b
    intro P Q hp hq
    simpa [a, b, F, r, delta, finiteTensor, finitePull, NatTrans.prod] using
      (finite_restriction_representative_square A gU j' j g sq o e
        (finite_restriction_pinned_total_square A gU j' j g sq o e) P Q hp hq)
  intro M N
  simpa [a, b, F, r, delta, finiteTensor, finitePull, NatTrans.prod] using
    congrArg (fun c ↦ c.app (M, N)) hab

end SheafOfModules.OpenTensorNormalization
