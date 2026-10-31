/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleLevelInverseTransport
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleOpenOrdinaryCalculation
import all WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Localization.Construction
import all Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import all Mathlib.CategoryTheory.Functor.Currying
import all Mathlib.CategoryTheory.Whiskering
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
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
import all WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleInverseTensorCoherence
import all WeilConjectures.Algebra.Homology.ProjectionCoherence.RingedProjectionPullbackComparisons
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageExact

/-! # Deriving a normalized finite inverse-image comparison

Source: Zheng, Construction 5.15; Stacks Tags 0D6D and 0G7E.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived

private def finiteFlatComplex (S : Scheme.{u}) (O : Type (u + 1)) [CommRing O]
    (ell : O) (n : ℕ) : ObjectProperty (CochainComplex (strictEtaleLevel S O ell n) ℤ) :=
  fun P ↦ P.IsKFlatIndependentCoefficients ∧
    ∀ i : ℤ, IsFlatOnSite (J := S.smallEtaleTopology)
      (R := coefficientQuotientSheaf (J := S.smallEtaleTopology) O ell n) (P.X i)

private def finiteFlatHomotopy (S : Scheme.{u}) (O : Type (u + 1)) [CommRing O]
    (ell : O) (n : ℕ) : ObjectProperty (HomotopyCategory (strictEtaleLevel S O ell n) (.up ℤ)) :=
  fun P ↦ finiteFlatComplex S O ell n P.as

private def finiteFlatQuotient (S : Scheme.{u}) (O : Type (u + 1)) [CommRing O]
    (ell : O) (n : ℕ) :
    (finiteFlatComplex S O ell n).FullSubcategory ⥤
      (finiteFlatHomotopy S O ell n).FullSubcategory where
  obj P := ⟨(HomotopyCategory.quotient _ _).obj P.obj, P.property⟩
  map f := ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map f.hom)

private theorem finiteFlatQuotient_full (S : Scheme.{u}) (O : Type (u + 1)) [CommRing O]
    (ell : O) (n : ℕ) : (finiteFlatQuotient S O ell n).Full :=
  { map_surjective := fun f ↦ ⟨ObjectProperty.homMk f.hom.out, by
      apply ObjectProperty.hom_ext
      exact HomotopyCategory.quotient_map_out f.hom⟩ }

private theorem finiteFlatQuotient_essSurj (S : Scheme.{u}) (O : Type (u + 1)) [CommRing O]
    (ell : O) (n : ℕ) : (finiteFlatQuotient S O ell n).EssSurj :=
  { mem_essImage := fun P ↦ ⟨⟨P.obj.as, P.property⟩, ⟨Iso.refl _⟩⟩ }

private theorem finiteFlat_localization (S : Scheme.{u}) (O : Type (u + 1)) [CommRing O]
    (ell : O) (n : ℕ) :
    ((finiteFlatHomotopy S O ell n).ι ⋙ DerivedCategory.Qh).IsLocalization
      ((HomotopyCategory.quasiIso (strictEtaleLevel S O ell n) (.up ℤ)).inverseImage
        (finiteFlatHomotopy S O ell n).ι) := by
  apply SheafOfModules.restriction_localization
    (HomotopyCategory.quasiIso (strictEtaleLevel S O ell n) (.up ℤ))
      DerivedCategory.Qh (finiteFlatHomotopy S O ell n)
  intro H
  obtain ⟨P, f, hk, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients H.as
  have hs : ∀ i, IsFlatOnSite (J := S.smallEtaleTopology)
      (R := coefficientQuotientSheaf (J := S.smallEtaleTopology) O ell n) (P.X i) :=
    fun i ↦ (exactFunctor _ _).prop_of_iso
      (siteSheafTensorRightIso _ (P.X i)).symm (hf i)
  refine ⟨⟨(HomotopyCategory.quotient _ _).obj P, hk, hs⟩,
    (HomotopyCategory.quotient _ _).map f, ?_⟩
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hq

private theorem finiteFlat_iso_descent (S : Scheme.{u}) (O : Type (u + 1)) [CommRing O]
    (ell : O) (n : ℕ) {E : Type*} [Category E]
    (U V : DerivedCategory (strictEtaleLevel S O ell n) ⥤ E)
    (e : ((finiteFlatComplex S O ell n).ι ⋙ DerivedCategory.Q) ⋙ U ≅
      ((finiteFlatComplex S O ell n).ι ⋙ DerivedCategory.Q) ⋙ V) :
    ∃ t : U ≅ V,
      Functor.isoWhiskerLeft ((finiteFlatComplex S O ell n).ι ⋙ DerivedCategory.Q) t = e := by
  let P := finiteFlatHomotopy S O ell n
  let F := finiteFlatQuotient S O ell n
  let : F.Full := finiteFlatQuotient_full S O ell n
  let : F.EssSurj := finiteFlatQuotient_essSurj S O ell n
  let L := P.ι ⋙ DerivedCategory.Qh
  let K := (finiteFlatComplex S O ell n).ι ⋙ DerivedCategory.Q
  let eK : F ⋙ L ≅ K := NatIso.ofComponents
    (fun X ↦ (DerivedCategory.quotientCompQhIso (strictEtaleLevel S O ell n)).app X.obj)
    (fun f ↦ (DerivedCategory.quotientCompQhIso (strictEtaleLevel S O ell n)).hom.naturality
      f.hom)
  let W := (HomotopyCategory.quasiIso (strictEtaleLevel S O ell n) (.up ℤ)).inverseImage P.ι
  have : L.IsLocalization W := finiteFlat_localization S O ell n
  exact SheafOfModules.ProjectionCoherence.localization_iso_descent F L W K eK U V e

section
variable {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O O' ell mu phi index)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (SA : StrictEtaleCompactSupport O ell c) (SB : StrictEtaleCompactSupport O' mu c)
    (TX : StrictEtaleCoefficientTransport a X SA.PX SB.PX)
    (TZ : StrictEtaleCoefficientTransport a c.Z SA.PZ SB.PZ)
    (n : ℕ)

private def inverseLeftComputation :
    DerivedCategory.Q ⋙ ((TZ.level n).derived ⋙ (SB.openDerived.level n).inverse) ⟶
      ((siteCoefficientTensor.{u + 1, u, u + 1}
        (a.sheaf c.Z n)).mapHomologicalComplex (.up ℤ) ⋙
        (SB.openImage.lift n).modules.mapHomologicalComplex (.up ℤ)) ⋙
        DerivedCategory.Q :=
  Functor.whiskerRight (TZ.level n).counit (SB.openDerived.level n).inverse ≫
    Functor.whiskerLeft ((siteCoefficientTensor.{u + 1, u, u + 1}
      (a.sheaf c.Z n)).mapHomologicalComplex (.up ℤ))
      (SB.openDerived.level n).inverseFactors.hom

private def inverseRightComputation :
    DerivedCategory.Q ⋙ ((SA.openDerived.level (index n)).inverse ⋙
      (TX.level n).derived) ⟶
      ((SA.openImage.lift (index n)).modules.mapHomologicalComplex (.up ℤ) ⋙
        (siteCoefficientTensor.{u + 1, u, u + 1}
          (a.sheaf X n)).mapHomologicalComplex (.up ℤ)) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (SA.openDerived.level (index n)).inverseFactors.hom
      (TX.level n).derived ≫
    Functor.whiskerLeft ((SA.openImage.lift (index n)).modules.mapHomologicalComplex
      (.up ℤ)) (TX.level n).counit

end

/-- A finite ordinary square descends on the flat-term K-flat subcategory.
The chosen inverse-image factorization maps and scalar counits are retained.
Source: Zheng, Construction 5.15; Stacks Tags 0D6D and 0G7E.
(blueprint: lem-pur-strict-etale-level-inverse-construction).

Proof: use the ordinary tensor-unit normalized square. On flat-term K-flat
complexes the left computation is invertible by scalar computation, and the right
computation is invertible because inverse image preserves this class. Conjugate
the ordinary cochain isomorphism by those computations. Descent from the full
flat-term K-flat subcategory gives a derived natural isomorphism: its homotopy
subcategory localizes to the derived category since every complex has such a
resolution. The descent equation, followed by cancellation of the right computation,
is exactly the required representative equation. -/
theorem nonempty_strictEtaleLevelInverseTransport
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O O' ell mu phi index)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (SA : StrictEtaleCompactSupport O ell c) (SB : StrictEtaleCompactSupport O' mu c)
    (TX : StrictEtaleCoefficientTransport a X SA.PX SB.PX)
    (TZ : StrictEtaleCoefficientTransport a c.Z SA.PZ SB.PZ)
    (n : ℕ) :
    Nonempty (StrictEtaleLevelInverseTransport TX TZ SA.openImage SB.openImage
      SA.openDerived.level SB.openDerived.level n) := by
  classical
  obtain ⟨ordinary, hu⟩ := inverseCoefficient_ordinary_exists a c.i SA.openImage
    SB.openImage n
  let P := finiteFlatComplex c.Z O ell (index n)
  let l := Functor.whiskerLeft P.ι
    (inverseLeftComputation (a := a) (c := c) (SA := SA) (SB := SB) (TZ := TZ) (n := n))
  let r := Functor.whiskerLeft P.ι
    (inverseRightComputation (a := a) (c := c) (SA := SA) (SB := SB) (TX := TX) (n := n))
  have hl (K : P.FullSubcategory) : IsIso (l.app K) := by
    have := (TZ.level n).computes K.obj K.property.1
    dsimp only [l, inverseLeftComputation, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, NatTrans.comp_app, ObjectProperty.ι_obj]
    infer_instance
  have hr (K : P.FullSubcategory) : IsIso (r.app K) := by
    have : PreservesFiniteLimits (Scheme.etaleSetPullback c.i) :=
      (etaleSetInverseImage_exact c.i).2.2.1
    obtain ⟨hk, hf⟩ := inverse_good (PV := SA.PX) (A := SA.openImage)
      (index n) K.obj K.property.1 K.property.2
    have := (TX.level n).computes
      (((SA.openImage.lift (index n)).modules.mapHomologicalComplex (.up ℤ)).obj K.obj)
      hk
    dsimp only [r, inverseRightComputation, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, NatTrans.comp_app, ObjectProperty.ι_obj]
    infer_instance
  let : ∀ K, IsIso (l.app K) := hl
  let : ∀ K, IsIso (r.app K) := hr
  let : IsIso l := NatIso.isIso_of_isIso_app l
  let : IsIso r := NatIso.isIso_of_isIso_app r
  let cochain :
      (siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf c.Z n)).mapHomologicalComplex
          (.up ℤ) ⋙ (SB.openImage.lift n).modules.mapHomologicalComplex (.up ℤ) ≅
        (SA.openImage.lift (index n)).modules.mapHomologicalComplex (.up ℤ) ⋙
          (siteCoefficientTensor.{u + 1, u, u + 1}
            (a.sheaf X n)).mapHomologicalComplex (.up ℤ) :=
    Functor.mapHomologicalComplexCompIso ordinary (.up ℤ)
  let middle := Functor.isoWhiskerLeft P.ι
    (Functor.isoWhiskerRight cochain DerivedCategory.Q)
  obtain ⟨derived, hd⟩ := finiteFlat_iso_descent c.Z O ell (index n)
    ((TZ.level n).derived ⋙ (SB.openDerived.level n).inverse)
    ((SA.openDerived.level (index n)).inverse ⋙ (TX.level n).derived)
    (Functor.associator P.ι DerivedCategory.Q _ ≪≫
      asIso l ≪≫ middle ≪≫ (asIso r).symm ≪≫
        (Functor.associator P.ι DerivedCategory.Q _).symm)
  refine ⟨⟨ordinary, derived, hu, ?_⟩⟩
  intro K hk hf
  let KP : P.FullSubcategory := ⟨K, hk, hf⟩
  have h := NatTrans.congr_app (congrArg Iso.hom hd) KP
  have h : derived.hom.app (DerivedCategory.Q.obj K) =
      l.app KP ≫ middle.hom.app KP ≫ (asIso r).inv.app KP := by
    simp only [Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
      Iso.symm_hom, Functor.associator_inv_app, Category.comp_id, asIso_hom] at h
    dsimp only [Functor.comp_obj, ObjectProperty.ι_obj] at h
    erw [Category.id_comp] at h
    exact h
  have hc : cochain.hom.app K =
      (NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app K := by
    ext i
    rfl
  have hm : middle.hom.app KP = DerivedCategory.Q.map
      ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app K) := by
    change DerivedCategory.Q.map (cochain.hom.app K) = _
    rw [hc]
  have h' := congrArg (fun z ↦ z ≫ (asIso r).hom.app KP) h
  simp only [Category.assoc, Iso.inv_hom_id_app] at h'
  erw [Category.comp_id] at h'
  rw [asIso_hom] at h'
  change derived.hom.app (DerivedCategory.Q.obj K) ≫
      ((TX.level n).derived.map
        ((SA.openDerived.level (index n)).inverseFactors.hom.app K) ≫
        (TX.level n).counit.app
          (((SA.openImage.lift (index n)).modules.mapHomologicalComplex (.up ℤ)).obj K)) =
    ((SB.openDerived.level n).inverse.map ((TZ.level n).counit.app K) ≫
      (SB.openDerived.level n).inverseFactors.hom.app
        (((siteCoefficientTensor.{u + 1, u, u + 1}
          (a.sheaf c.Z n)).mapHomologicalComplex (.up ℤ)).obj K)) ≫
      middle.hom.app KP at h'
  simpa only [Category.assoc, hm] using h'

end AlgebraicGeometry
