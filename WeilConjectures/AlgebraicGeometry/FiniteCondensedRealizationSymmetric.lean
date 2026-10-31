/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.FiniteNativeTensorComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
import all WeilConjectures.CategoryTheory.ConstantScalarRestrictionTensorSupplement
import all WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import all WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import all WeilConjectures.CategoryTheory.SheafTensor
import all WeilConjectures.CategoryTheory.SheafTensorStructure
import all Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.CategoryTheory.Abelian.Basic
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all WeilConjectures.CategoryTheory.SheafificationTensorLocalIso
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.CategoryTheory.Sites.Sheafification
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
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
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import all WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import all WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-! # Symmetry for normalized finite realization

Source: latest blueprint, `det-pd-biduality-coefficients.proof.md`, paragraph (i).
The specified tensorator is compared with the canonical derived Koszul braidings.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.scalarReductionSiteSmall
universe u c d v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry
open scoped CategoryTheory.Obj TensorProduct

namespace CategoryTheory
private def finiteBraidingCondition
    {C : Type c} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    {D : Type d} [Category.{w} D] [MonoidalCategory D] [BraidedCategory D]
    (F : C ⥤ D) [F.LaxMonoidal] : Prop :=
  ∀ X Y, Functor.LaxMonoidal.μ F X Y ≫ F.map (β_ X Y).hom =
    (β_ (F.obj X) (F.obj Y)).hom ≫ Functor.LaxMonoidal.μ F Y X

private theorem finiteBraidingTransport
    {C : Type c} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    {D : Type d} [Category.{w} D] [MonoidalCategory D] [BraidedCategory D]
    (F G : C ⥤ D) [m : F.Monoidal] (e : F ≅ G)
    (hF : ∀ X Y, Functor.LaxMonoidal.μ F X Y ≫ F.map (β_ X Y).hom =
      (β_ (F.obj X) (F.obj Y)).hom ≫ Functor.LaxMonoidal.μ F Y X) :
    let : G.Monoidal := Functor.Monoidal.transport e
    ∀ X Y, Functor.LaxMonoidal.μ G X Y ≫ G.map (β_ X Y).hom =
      (β_ (G.obj X) (G.obj Y)).hom ≫ Functor.LaxMonoidal.μ G Y X := by
  let : F.LaxBraided := { toLaxMonoidal := m.toLaxMonoidal, braided := hF }
  let : G.Monoidal := Functor.Monoidal.transport e
  let : NatTrans.IsMonoidal e.hom := Functor.Monoidal.natTransIsMonoidal_of_transport e
  exact (Functor.LaxBraided.ofNatIso e).braided

private theorem finiteBraidingOplax
    {C : Type c} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    {D : Type d} [Category.{w} D] [MonoidalCategory D] [BraidedCategory D]
    (F : C ⥤ D) [F.Monoidal]
    (hF : ∀ X Y, Functor.LaxMonoidal.μ F X Y ≫ F.map (β_ X Y).hom =
      (β_ (F.obj X) (F.obj Y)).hom ≫ Functor.LaxMonoidal.μ F Y X)
    (X Y : C) :
    F.map (β_ X Y).hom ≫ Functor.OplaxMonoidal.δ F Y X =
      Functor.OplaxMonoidal.δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom := by
  apply (cancel_epi (Functor.LaxMonoidal.μ F X Y)).mp
  rw [← Category.assoc, hF, Category.assoc, Functor.Monoidal.μ_δ,
    Category.comp_id, Functor.Monoidal.μ_δ_assoc]
private theorem finiteBraidingInverse
    {C : Type c} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    {D : Type d} [Category.{w} D] [MonoidalCategory D] [BraidedCategory D]
    (e : C ≌ D) [m : e.functor.Monoidal]
    (hF : ∀ X Y, Functor.LaxMonoidal.μ e.functor X Y ≫ e.functor.map (β_ X Y).hom =
      (β_ (e.functor.obj X) (e.functor.obj Y)).hom ≫
        Functor.LaxMonoidal.μ e.functor Y X) :
    let := e.inverseMonoidal
    ∀ X Y, Functor.LaxMonoidal.μ e.inverse X Y ≫ e.inverse.map (β_ X Y).hom =
      (β_ (e.inverse.obj X) (e.inverse.obj Y)).hom ≫
        Functor.LaxMonoidal.μ e.inverse Y X := by
  let : e.functor.Braided := { toMonoidal := m, braided := hF }
  exact e.toAdjunction.rightAdjointLaxMonoidal_μ_comp_map_braiding

private theorem finiteBraidingComp
    {C : Type c} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    {D : Type d} [Category.{w} D] [MonoidalCategory D] [BraidedCategory D]
    {E : Type*} [Category* E] [MonoidalCategory E] [BraidedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) [mF : F.Monoidal] [mG : G.Monoidal]
    (hF : ∀ X Y, Functor.LaxMonoidal.μ F X Y ≫ F.map (β_ X Y).hom =
      (β_ (F.obj X) (F.obj Y)).hom ≫ Functor.LaxMonoidal.μ F Y X)
    (hG : ∀ X Y, Functor.LaxMonoidal.μ G X Y ≫ G.map (β_ X Y).hom =
      (β_ (G.obj X) (G.obj Y)).hom ≫ Functor.LaxMonoidal.μ G Y X) :
    ∀ X Y, Functor.LaxMonoidal.μ (F ⋙ G) X Y ≫ (F ⋙ G).map (β_ X Y).hom =
      (β_ ((F ⋙ G).obj X) ((F ⋙ G).obj Y)).hom ≫
        Functor.LaxMonoidal.μ (F ⋙ G) Y X := by
  let : F.LaxBraided := { toLaxMonoidal := mF.toLaxMonoidal, braided := hF }
  let : G.LaxBraided := { toLaxMonoidal := mG.toLaxMonoidal, braided := hG }
  exact (inferInstance : (F ⋙ G).LaxBraided).braided

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
attribute [local instance 20000] sheafBraidedCategory sheafSymmetricCategory
  sheafMonoidalCategory sheafMonoidalClosed
attribute [local irreducible] Mod.monoidalClosed
attribute [local irreducible] Sheaf.monoidalCategory SheafOfModules.monoidalCategory
variable (A : Type u) [CommRing A] [Finite A]
  [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
omit [Finite A] [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A] in
private theorem fixedPure_braiding (T : Scheme.{u})
    (M N : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    (V : T.ProEtᵒᵖ) (x : M.obj.obj V) (y : N.obj.obj V) :
    ((β_ M N).hom.hom.app V)
        (ConstantScalarRestriction.fixedPure (Scheme.ProEt.topology T)
          (ULift.{u + 1} A) M N V x y) =
      ConstantScalarRestriction.fixedPure (Scheme.ProEt.topology T)
        (ULift.{u + 1} A) N M V y x := by
  rw [← ConstantScalarRestriction.fixedPure_inclusion,
    ← ConstantScalarRestriction.fixedPure_inclusion]
  let I := sheafToPresheaf (Scheme.ProEt.topology T)
    (ModuleCat.{u + 1} (ULift.{u + 1} A))
  exact congrArg (fun f ↦ (f.app V) (x ⊗ₜ[ULift.{u + 1} A] y))
    (Functor.LaxBraided.braided (F := I) M N)

private abbrev normalizedHeart (T : Scheme.{u})
    (c : realizationRing (Scheme.ProEt.topology T) (ULift.{u + 1} A) ≅ sectionRing A T) :=
  Mod.comap (coefficientMap (Iso.refl (Mon.mk (coefficient A))).inv.hom T) ⋙
    (sectionEncoding A T c ⋙ fixedRestriction A T)

omit [Finite A] [DiscreteTopology A] in
private theorem normalizedHeart_map_apply (T : Scheme.{u})
    (c : realizationRing (Scheme.ProEt.topology T) (ULift.{u + 1} A) ≅ sectionRing A T)
    {M N : Internal A T} (f : M ⟶ N) (V : T.ProEtᵒᵖ) (x : M.X.obj.obj V) :
    (((normalizedHeart A T c).map f).hom.app V) x = (f.hom.hom.app V).hom x := by
  rfl

omit [Finite A] [DiscreteTopology A] in
private theorem normalizedHeart_braiding (T : Scheme.{u})
    (c : realizationRing (Scheme.ProEt.topology T) (ULift.{u + 1} A) ≅ sectionRing A T)
    [m : (normalizedHeart A T c).LaxMonoidal]
    (hm : ∀ (M N : Internal A T) (V : T.ProEtᵒᵖ)
      (x : M.X.obj.obj V) (y : N.X.obj.obj V),
      ((Functor.LaxMonoidal.μ (normalizedHeart A T c) M N).hom.app V)
        (ConstantScalarRestriction.fixedPure (Scheme.ProEt.topology T)
          (ULift.{u + 1} A) ((normalizedHeart A T c).obj M)
          ((normalizedHeart A T c).obj N) V x y) =
        InternalAbelianSheafModule.comparison_internalTmul (Scheme.ProEt.topology T)
          (condensedRingObj (coefficient A) T) M N V x y)
    (M N : Internal A T) :
    Functor.LaxMonoidal.μ (normalizedHeart A T c) M N ≫
        (normalizedHeart A T c).map (β_ M N).hom =
      (β_ ((normalizedHeart A T c).obj M) ((normalizedHeart A T c).obj N)).hom ≫
        Functor.LaxMonoidal.μ (normalizedHeart A T c) N M := by
  let H := normalizedHeart A T c
  apply ConstantScalarRestriction.fixedTensor_ext
    (Scheme.ProEt.topology T) (ULift.{u + 1} A) (H.obj M) (H.obj N) (H.obj (N ⊗ M))
  intro V x y
  change ((H.map (β_ M N).hom).hom.app V)
      (((Functor.LaxMonoidal.μ H M N).hom.app V)
        (ConstantScalarRestriction.fixedPure (Scheme.ProEt.topology T)
          (ULift.{u + 1} A) (H.obj M) (H.obj N) V x y)) =
    ((Functor.LaxMonoidal.μ H N M).hom.app V)
      (((β_ (H.obj M) (H.obj N)).hom.hom.app V)
        (ConstantScalarRestriction.fixedPure (Scheme.ProEt.topology T)
          (ULift.{u + 1} A) (H.obj M) (H.obj N) V x y))
  rw [hm, fixedPure_braiding, hm]
  rw [normalizedHeart_map_apply]
  exact InternalAbelianSheafModule.comparison_internalTmul_braiding
    (Scheme.ProEt.topology T) (condensedRingObj (coefficient A) T) M N V x y
set_option maxHeartbeats 2000000 in
-- Transported monoidal data contain two dependent functor-equality casts.
omit [Finite A] [DiscreteTopology A] in
private theorem heart_braiding (T : Scheme.{u}) (enc : Encoding A T) :
    let : (enc.ordinary.trans enc.fixed).functor.Monoidal :=
      FiniteNativeTensor.heartMonoidal A T enc
    let : (enc.ordinary.trans enc.fixed).functor.LaxMonoidal :=
      (FiniteNativeTensor.heartMonoidal A T enc).toLaxMonoidal
    ∀ M N : Internal A T,
      Functor.LaxMonoidal.μ (enc.ordinary.trans enc.fixed).functor M N ≫
          (enc.ordinary.trans enc.fixed).functor.map (β_ M N).hom =
        (β_ ((enc.ordinary.trans enc.fixed).functor.obj M)
          ((enc.ordinary.trans enc.fixed).functor.obj N)).hom ≫
            Functor.LaxMonoidal.μ (enc.ordinary.trans enc.fixed).functor N M := by
  let H := coefficientHeartEncoding A (Iso.refl (Mon.mk (coefficient A))) T enc
  have hH :
      let : H.Monoidal := by
        unfold H coefficientHeartEncoding
        rw [enc.ordinary_functor, enc.fixed_functor]
        exact Classical.choose
          (coefficientSectionTensor_normalized A (Iso.refl (Mon.mk (coefficient A)))
            T enc.ringIso)
      CategoryTheory.finiteBraidingCondition H := by
    have aux : ∀ (O : Internal A T ⥤ Ordinary A T)
        (Q : Ordinary A T ⥤ Sheaf (Scheme.ProEt.topology T)
          (ModuleCat.{u + 1} (ULift.{u + 1} A)))
        (ho : O = sectionEncoding A T enc.ringIso) (hq : Q = fixedRestriction A T),
        let F := Mod.comap
          (coefficientMap (Iso.refl (Mon.mk (coefficient A))).inv.hom T) ⋙ (O ⋙ Q)
        let : F.Monoidal := by
          unfold F
          rw [ho, hq]
          exact Classical.choose (coefficientSectionTensor_normalized A
            (Iso.refl (Mon.mk (coefficient A))) T enc.ringIso)
        CategoryTheory.finiteBraidingCondition F := by
      intro O Q ho hq
      subst O Q
      let : (normalizedHeart A T enc.ringIso).LaxMonoidal :=
        (Classical.choose (coefficientSectionTensor_normalized A
          (Iso.refl (Mon.mk (coefficient A))) T enc.ringIso)).toLaxMonoidal
      exact normalizedHeart_braiding A T enc.ringIso
        (Classical.choose_spec (coefficientSectionTensor_normalized A
          (Iso.refl (Mon.mk (coefficient A))) T enc.ringIso))
    exact aux enc.ordinary.functor enc.fixed.functor enc.ordinary_functor enc.fixed_functor
  let : H.Monoidal := by
    unfold H coefficientHeartEncoding
    rw [enc.ordinary_functor, enc.fixed_functor]
    exact Classical.choose
      (coefficientSectionTensor_normalized A (Iso.refl (Mon.mk (coefficient A)))
        T enc.ringIso)
  exact CategoryTheory.finiteBraidingTransport H (enc.ordinary.trans enc.fixed).functor
    (FiniteNativeTensor.heartIdentityIso A T enc) hH

omit [Finite A] [DiscreteTopology A] in
private theorem encoding_braiding (T : Scheme.{u}) (enc : Encoding A T) :
    let := _root_.DerivedCategory.braidedCategory' (Internal A T)
    let := _root_.DerivedCategory.braidedCategory'
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    let := FiniteNativeTensor.encodingMonoidal A T enc
    ∀ K L : _root_.DerivedCategory (Internal A T),
      Functor.LaxMonoidal.μ enc.fixedDerived.functor K L ≫
          enc.fixedDerived.functor.map (β_ K L).hom =
        (β_ (enc.fixedDerived.functor.obj K) (enc.fixedDerived.functor.obj L)).hom ≫
          Functor.LaxMonoidal.μ enc.fixedDerived.functor L K := by
  let F := (enc.ordinary.trans enc.fixed).functor
  let : F.Monoidal := FiniteNativeTensor.heartMonoidal A T enc
  let : F.Additive := inferInstanceAs (enc.ordinary.functor ⋙ enc.fixed.functor).Additive
  let : F.PreservesFlat := Functor.preservesFlat_of_isEquivalence F
  have hF := CategoryTheory.finiteBraidingOplax F (heart_braiding A T enc)
  let : BraidedCategory (_root_.DerivedCategory (Internal A T)) :=
    _root_.DerivedCategory.braidedCategory' _
  let : BraidedCategory (_root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A)))) :=
    _root_.DerivedCategory.braidedCategory' _
  let : F.leftDerivedFunctor.Monoidal := F.leftDerivedFunctorMonoidal
  exact CategoryTheory.finiteBraidingTransport F.leftDerivedFunctor F.mapDerivedCategory
    F.leftDerivedFunctorIsoMapDerivedCategory (F.leftDerivedFunctor_μ_map_braiding_hom hF)

omit [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A] in
private theorem site_braiding (T : Scheme.{u}) :
    let := _root_.DerivedCategory.braidedCategory'
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    let := _root_.DerivedCategory.braidedCategory'
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    let := FiniteNativeTensor.siteMonoidal A T
    let F := (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T
      ).mapDerivedCategory
    ∀ K L, Functor.LaxMonoidal.μ F K L ≫ F.map (β_ K L).hom =
      (β_ (F.obj K) (F.obj L)).hom ≫ Functor.LaxMonoidal.μ F L K := by
  let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
  let F := comparisonUpperStar B T
  let G := comparisonLowerStar B T
  let : G.LaxBraided := by unfold G comparisonLowerStar; infer_instance
  have hF (X Y : Sheaf T.smallEtaleTopology B) :
      F.map (β_ X Y).hom ≫ Functor.OplaxMonoidal.δ F Y X =
        Functor.OplaxMonoidal.δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom :=
    (comparisonAdjunction B T).map_braiding_comp_δ X Y
  let : BraidedCategory (_root_.DerivedCategory (Sheaf T.smallEtaleTopology B)) :=
    _root_.DerivedCategory.braidedCategory' _
  let : BraidedCategory (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) B)) :=
    _root_.DerivedCategory.braidedCategory' _
  let : F.leftDerivedFunctor.Monoidal := F.leftDerivedFunctorMonoidal
  exact CategoryTheory.finiteBraidingTransport F.leftDerivedFunctor F.mapDerivedCategory
    F.leftDerivedFunctorIsoMapDerivedCategory (F.leftDerivedFunctor_μ_map_braiding_hom hF)
/-- The specified normalized realization tensorator preserves the canonical derived
symmetry on all ambient objects.
Source: latest blueprint, `det-pd-biduality-coefficients.proof.md`, paragraph (i)
(blueprint: lem-sf-finite-condensed-realization-symmetric).

Proof: the heart tensorator is normalized on balanced pure tensors. Both composites
in the symmetry square send x tensor y to the same tensor with reversed factors;
the relative tensor universal property proves their equality. Derive this equality
on K-flat complexes, where it is the Koszul symmetry square. Descend through the
homotopy localization and transport along the exact/left-derived identification.
The same construction for site inverse image is braided. Compose its symmetry square
with that of the inverse encoding. The resulting monoidal structure is precisely
realizationMonoidal, so this proves the displayed equation without changing tensorators.
The argument also applies to zero rings, empty schemes and unbounded complexes. -/
theorem finiteCondensedRealizationSymmetric
    (A : Type u) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
    (T : Scheme.{u}) (enc : Encoding A T) :
    let F := internalEtaleRealization A T enc
    let := FiniteNativeTensor.realizationMonoidal A T enc
    ∀ K L : Etale.DerivedCategoryModule (ULift.{u + 1} A) T,
      (Functor.Monoidal.μIso F K L).hom ≫
          F.map ((_root_.DerivedCategory.braidedCategory'
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A)))).braiding K L).hom =
        ((_root_.DerivedCategory.braidedCategory' (Internal A T)).braiding
          (F.obj K) (F.obj L)).hom ≫ (Functor.Monoidal.μIso F L K).hom := by
  dsimp only
  let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
  let S := (comparisonUpperStar B T).mapDerivedCategory
  let : BraidedCategory (_root_.DerivedCategory (Sheaf T.smallEtaleTopology B)) :=
    _root_.DerivedCategory.braidedCategory' _
  let : BraidedCategory (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) B)) :=
    _root_.DerivedCategory.braidedCategory' _
  let : BraidedCategory (_root_.DerivedCategory (Internal A T)) :=
    _root_.DerivedCategory.braidedCategory' _
  let : S.Monoidal := FiniteNativeTensor.siteMonoidal A T
  let : enc.fixedDerived.functor.Monoidal := FiniteNativeTensor.encodingMonoidal A T enc
  have hInv := CategoryTheory.finiteBraidingInverse enc.fixedDerived
    (encoding_braiding A T enc)
  let : enc.fixedDerived.inverse.Monoidal := enc.fixedDerived.inverseMonoidal
  have h := CategoryTheory.finiteBraidingComp S enc.fixedDerived.inverse
    (site_braiding A T) hInv
  intro K L
  simpa only [Functor.Monoidal.μIso_hom, internalEtaleRealization,
    FiniteNativeTensor.realizationMonoidal, S, B] using h K L

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
