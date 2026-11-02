/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ComponentDerivedSquare.ComponentDerivedSquareData
import all WeilConjectures.CategoryTheory.Exact.ExactDerivedTensorSquare
import WeilConjectures.CategoryTheory.ZetaWeil.RestrictedSquareMonoidal
import WeilConjectures.CategoryTheory.ZetaWeil.RestrictedTransportBraiding
import WeilConjectures.CategoryTheory.SiteInverseImageModuleFlat.SiteInverseImageModuleFlat
import WeilConjectures.AlgebraicGeometry.ComponentDerivedSquare.ComponentOrdinaryAbelianSquare
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalLeftDerived
import all WeilConjectures.CategoryTheory.Exact.ExactClosedDerivedHom
import all WeilConjectures.CategoryTheory.ExactMonoidalEquivalenceDerived.ExactMonoidalEquivalenceDerived
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure

/-! # Tensor descent for an ordinary component square -/

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ComponentDerivedSquare

section ExactTensor
universe a
variable {A : Type a} [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalClosed A]
  [MonoidalPreadditive A] [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A]
  {B : Type a} [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalClosed B]
  [MonoidalPreadditive B] [BraidedCategory B] [Abelian.HasFunctorialFlatResolution B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.Braided] [F.PreservesFlat] [F.IsLeftAdjoint]

end ExactTensor

section NormalizedInverse
universe a b v w
variable {A : Type a} [Category.{v} A] [MonoidalCategory A] [BraidedCategory A]
  {B : Type b} [Category.{w} B] [MonoidalCategory B] [BraidedCategory B]

end NormalizedInverse

end AlgebraicGeometry.ProEtale.ComponentDerivedSquare
end

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.ComponentDerivedSquare

end AlgebraicGeometry.ProEtale.ComponentDerivedSquare

namespace AlgebraicGeometry.ProEtale.ComponentDerivedSquare

private theorem exact_factors_monoidal :
    let := F.exactClosedDerivedMonoidal
    NatTrans.IsMonoidal F.mapDerivedCategoryFactors.hom := by
  let := F.exactClosedDerivedMonoidal
  let := CategoryTheory.Functor.mapHomotopyMonoidal F
  have := CategoryTheory.Functor.mapHomotopyFactors_monoidal F
  have := CategoryTheory.Functor.derivedFactorsh_monoidal F
  have hc : NatTrans.IsMonoidal (DerivedCategory.quotientCompQhIso A).hom :=
    ExactMonoidalEquivalenceDerived.quotientCompQh_monoidal
  have hd : NatTrans.IsMonoidal (DerivedCategory.quotientCompQhIso B).hom :=
    ExactMonoidalEquivalenceDerived.quotientCompQh_monoidal
  let e := ExactMonoidalEquivalenceDerived.composeFactors
    (DerivedCategory.quotientCompQhIso A) (DerivedCategory.quotientCompQhIso B)
    (F.mapHomotopyCategoryFactors (.up ℤ)) F.mapDerivedCategoryFactorsh
  have he : e.hom = F.mapDerivedCategoryFactors.hom := by
    apply NatTrans.ext
    funext K
    rw [ExactMonoidalEquivalenceDerived.composeFactors_hom_app]
    rw [Functor.mapDerivedCategoryFactorsh_hom_app]
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
    simp only [DerivedCategory.quotientCompQhIso,
      HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift_hom,
      Category.id_comp]
    exact Category.comp_id _
  rw [← he]
  exact ExactMonoidalEquivalenceDerived.composeFactors_monoidal
    (DerivedCategory.quotientCompQhIso A) (DerivedCategory.quotientCompQhIso B)
    (F.mapHomotopyCategoryFactors (.up ℤ)) F.mapDerivedCategoryFactorsh

private def exact_tensor_lift : TensorLift F := by
  letI := F.exactClosedDerivedMonoidal
  refine {
    colimits := inferInstance
    monoidal := F.exactClosedDerivedMonoidal
    localization := exact_factors_monoidal F
    triangulated := inferInstance
    symmetric := ?_ }
  let := DerivedCategory.braidedCategory' A
  let := DerivedCategory.braidedCategory' B
  have hδ (X Y : A) : F.map (β_ X Y).hom ≫ Functor.OplaxMonoidal.δ F Y X =
      Functor.OplaxMonoidal.δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom := by
    rw [← cancel_epi (Functor.LaxMonoidal.μ F X Y)]
    rw [← Category.assoc, Functor.LaxBraided.braided, Category.assoc,
      Functor.Monoidal.μ_δ, Category.comp_id, Functor.Monoidal.μ_δ_assoc]
  let := F.residueDerivedMonoidal
  let hb : F.leftDerivedFunctor.LaxBraided := {
    toLaxMonoidal := (F.residueDerivedMonoidal).toLaxMonoidal
    braided := fun K L ↦ Functor.Monoidal.μ_comp_map_braiding_hom_of_δ _ K L
      (F.leftDerivedFunctor_map_braiding_hom_δ hδ K L) }
  let := hb
  let : F.mapDerivedCategory.Monoidal :=
    Functor.Monoidal.transport F.leftDerivedFunctorIsoMapDerivedCategory
  unfold Functor.exactClosedDerivedMonoidal
  change ∀ K L, Functor.LaxMonoidal.μ F.mapDerivedCategory K L ≫
    F.mapDerivedCategory.map (β_ K L).hom =
    (β_ (F.mapDerivedCategory.obj K) (F.mapDerivedCategory.obj L)).hom ≫
      Functor.LaxMonoidal.μ F.mapDerivedCategory L K
  let : NatTrans.IsMonoidal F.leftDerivedFunctorIsoMapDerivedCategory.hom :=
    Functor.Monoidal.natTransIsMonoidal_of_transport
      F.leftDerivedFunctorIsoMapDerivedCategory
  exact (Functor.LaxBraided.ofNatIso F.leftDerivedFunctorIsoMapDerivedCategory).braided

private theorem square_abelian_monoidal
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] {f : Y ⟶ X}
    {sX : Corner Λ X} {sY : Corner Λ Y} {sh : Slice Λ (affineComponentMap f)}
    (sq : Square Λ f sX sY sh) : NatTrans.IsMonoidal sq.abelian.hom := by
  obtain ⟨n⟩ := component_ordinary_abelian_square Λ f sX sY sh
  have he : sq.abelian = n.abelian := by
    apply (conjugateIsoEquiv (sh.adjunction.comp sY.adjunction)
      (sX.adjunction.comp (upperStarLowerStarAdjunction Ab.{u + 1} f))).injective
    apply Iso.ext
    apply NatTrans.ext
    funext G
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext E
    rw [sq.abelian_mate, n.abelian_mate]
    have ht : sq.tests.hom.app E.unop = n.tests.hom.app E.unop := by
      apply MorphismProperty.Over.Hom.ext
      exact (sq.tests_eq _).trans (n.tests_eq _).symm
    rw [ht]
  rw [he]
  infer_instance

private def scheme_module_iso
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y : Scheme.{u}} (f : Y ⟶ X) :
    CondensedRing.upperStar Λ.X f ≅ (upperStar Ab.{u + 1} f).mapMod
      (condensedRingObj Λ.X X) ⋙ Mod.comap (asIso (condensedPullbackHom Λ.X f)).inv :=
  Functor.isoWhiskerLeft ((upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ.X X))
    (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ.X f))

private instance scheme_module_iso_monoidal
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y : Scheme.{u}} (f : Y ⟶ X) :
    NatTrans.IsMonoidal (scheme_module_iso Λ f).hom := by
  let i := Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ.X f)
  have : NatTrans.IsMonoidal i.symm.hom :=
    Functor.Monoidal.natTransIsMonoidal_of_transport i.symm
  have hi : NatTrans.IsMonoidal i.hom :=
    inferInstanceAs (NatTrans.IsMonoidal i.symm.inv)
  change NatTrans.IsMonoidal (Functor.whiskerLeft
    ((upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ.X X)) i.hom)
  infer_instance

private theorem square_ordinary_monoidal
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] {f : Y ⟶ X}
    {sX : Corner Λ X} {sY : Corner Λ Y} {sh : Slice Λ (affineComponentMap f)}
    (sq : Square Λ f sX sY sh) : NatTrans.IsMonoidal sq.ordinary.hom := by
  let := square_abelian_monoidal Λ sq
  let es := scheme_module_iso Λ f
  have hes : NatTrans.IsMonoidal es.hom := scheme_module_iso_monoidal Λ f
  let ν := Functor.isoWhiskerLeft (sX.modules Λ X) es.symm ≪≫ sq.ordinary
  have hν (M) : (ν.hom.app M).hom = sq.abelian.hom.app M.X := by
    change (es.inv.app ((sX.modules Λ X).obj M)).hom ≫
      (sq.ordinary.hom.app M).hom = _
    rw [sq.ordinary_underlying]
    change (es.inv.app ((sX.modules Λ X).obj M)).hom ≫
      (es.hom.app ((sX.modules Λ X).obj M)).hom ≫ sq.abelian.hom.app M.X = _
    have hi := congrArg Mod.Hom.hom (es.inv_hom_id_app ((sX.modules Λ X).obj M))
    rw [Mod.comp_hom', Mod.id_hom'] at hi
    rw [← Category.assoc, hi, Category.id_comp]
  have hn : NatTrans.IsMonoidal ν.hom :=
    CategoryTheory.restrictedModuleSquare_monoidal
      sX.inverse (upperStar Ab.{u + 1} f) sh.inverse sY.inverse
      sX.coefficient.inv.hom (asIso (condensedPullbackHom Λ.X f)).inv
      sh.coefficient.inv.hom sY.coefficient.inv.hom sq.abelian ν hν
  let := hn
  have he : (Functor.isoWhiskerLeft (sX.modules Λ X) es).hom ≫ ν.hom =
      sq.ordinary.hom := by
    apply NatTrans.ext
    funext M
    change es.hom.app ((sX.modules Λ X).obj M) ≫
      es.inv.app ((sX.modules Λ X).obj M) ≫ sq.ordinary.hom.app M = _
    simp only [Iso.hom_inv_id_app_assoc]
  rw [← he]
  change NatTrans.IsMonoidal (Functor.whiskerLeft (sX.modules Λ X) es.hom ≫ ν.hom)
  infer_instance

/-- Exact component inverse images have normalized derived tensors, and their specified
square respects them. Source: HRS Section 3, construction (4.1); Stacks 07A4 and 0FPI
(blueprint: lem-zl-component-derived-tensor-lifts).

Proof: every edge is an actual geometric inverse image with coefficient transport
along an isomorphism. Such module inverse images preserve colimits and flat objects:
their right adjoints are restriction with the transported module action. The
internal-to-section-module equivalence and the explicit algebraic inverse-image
comparison transport the standard inverse-image flatness theorem to these functors.
Apply termwise pullback to flat-term K-flat representatives. Preservation
of coproducts identifies the total tensor of their images with the image of their
total tensor. Exactness preserves quasi-isomorphisms, giving the canonical invertible
derived tensor and coefficient-unit comparisons.

Descend the pentagon, unit and symmetry equations from those of the ordinary pullback;
the comparison with localization is monoidal by construction. Exact-functor
localization is triangulated. For the square, its ordinary comparison is the mate of
the restriction comparison, hence monoidal for the adjunction-normalized tensor maps.
The underlying module comparison respects balanced tensors; strong monoidality
then determines its unit compatibility. Apply these equations
termwise and descend them along localization. With the canonical composition maps
inserted, the resulting two equations are precisely `Square.monoidal` for `Square.theta`.
The localization equation uniquely fixes each derived tensor structure, so the edge
structures may be chosen simultaneously and the argument applies to the supplied
ordinary system. No boundedness, discreteness or henselian hypothesis is used. -/
theorem component_derived_tensor_lifts
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (s : OrdinarySystem Λ) :
    Nonempty (TensorSystem Λ s) := by
  classical
  let tx : ∀ (X : Scheme.{u}) [IsAffine X], TensorLift ((s.corner X).modules Λ X) :=
    fun X _ ↦ exact_tensor_lift ((s.corner X).modules Λ X)
  let th : ∀ {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X),
      TensorLift ((s.slice f).modules Λ) :=
    fun f ↦ exact_tensor_lift ((s.slice f).modules Λ)
  let tf : ∀ {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X),
      TensorLift (CondensedRing.upperStar Λ.X f) :=
    fun f ↦ exact_tensor_lift (CondensedRing.upperStar Λ.X f)
  refine ⟨{ corner := tx, slice := th, scheme := tf, monoidal := ?_ }⟩
  intro X Y _ _ f
  let := square_ordinary_monoidal Λ (s.square f)
  unfold Square.monoidal Square.theta leftPath rightPath Corner.derived Slice.derived
    tensorSquareMonoidal
  exact Functor.exactDerivedSquare_monoidal ((s.slice f).modules Λ)
    ((s.corner Y).modules Λ Y) ((s.corner X).modules Λ X)
    (CondensedRing.upperStar Λ.X f) (s.square f).ordinary

end AlgebraicGeometry.ProEtale.ComponentDerivedSquare
