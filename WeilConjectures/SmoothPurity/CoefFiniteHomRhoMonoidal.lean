/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CoefFiniteHom
import WeilConjectures.SmoothPurity.FiniteCoefficientSiteEquationDescent

/-! # Monoidality of the specified scalar/site mate

Source: thm-coef-finite-hom.proof.md, final paragraph, tensor/site transport.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u v w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.CoefficientScalarRepresentatives
namespace WeilConjectures

local instance finiteHomRhoMonoidalProSmall (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

private theorem proAdjNative
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (X : Scheme.{u}) (φ : A →+* B) :
    letI : Algebra A B := φ.toAlgebra
    AlgebraicGeometry.ProEtale.leftDerivedSheafExtendScalarsAdjunction A B X =
      finiteHomScalarAdjunction (ProEt.topology X) φ := by
  unfold finiteHomScalarAdjunction scalarDerivedAdjunction
    AlgebraicGeometry.ProEtale.leftDerivedSheafExtendScalarsAdjunction
    AlgebraicGeometry.ProEtale.sheafExtendScalarsAdjunction ordinaryAdjunction
    AlgebraicGeometry.ProEtale.sheafExtendScalars ordinaryExtension
  rfl

private theorem monoidalTransportRefl
    {C D : Type*} [Category C] [MonoidalCategory C] [Category D] [MonoidalCategory D]
    (F : C ⥤ D) [h : F.Monoidal] :
    (Functor.Monoidal.coreMonoidalTransport (Iso.refl F)).toMonoidal = h := by
  change Functor.Monoidal.transport (Iso.refl F) = h
  ext <;> simp [Functor.Monoidal.transport_ε, Functor.Monoidal.transport_η,
    Functor.Monoidal.transport_μ, Functor.Monoidal.transport_δ]



private theorem nativeDerivedCore_eq
    {V : Type v} [Category.{u + 1} V] [Abelian V]
    [IsGrothendieckAbelian.{u + 1} V] [MonoidalCategory V] [MonoidalPreadditive V]
    [MonoidalClosed V] [BraidedCategory V] [Abelian.HasFunctorialFlatResolution V]
    {W : Type w} [Category.{u + 1} W] [Abelian W]
    [IsGrothendieckAbelian.{u + 1} W] [MonoidalCategory W] [MonoidalPreadditive W]
    [MonoidalClosed W] [BraidedCategory W] [Abelian.HasFunctorialFlatResolution W]
    (F : V ⥤ W) [F.Additive] [F.PreservesKFlatQuasiIso] [F.PreservesFlat]
    [F.IsLeftAdjoint] [F.Monoidal] :
    (finiteHomNativeDerivedCore F).toMonoidal = F.leftDerivedFunctorMonoidal := by
  unfold finiteHomNativeDerivedCore Functor.leftDerivedFunctorMonoidal
  rfl

private theorem proScalarPreservesFlat
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (X : Scheme.{u}) (φ : A →+* B) :
    (ordinaryExtension (ProEt.topology X) φ).PreservesFlat := by
  exact ⟨fun h ↦ CategoryTheory.Sheaf.flat_extendScalars_obj (ProEt.topology X) φ h⟩

private theorem proNative
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (X : Scheme.{u}) (φ : A →+* B) :
    letI : Algebra A B := φ.toAlgebra
    letI := AlgebraicGeometry.ProEtale.preservesKFlatQuasiIso_sheafExtendScalars A B X
    letI : (ordinaryExtension (ProEt.topology X) φ).Monoidal :=
      finiteHomOrdinaryMonoidal (ProEt.topology X) φ
    letI : (ordinaryExtension (ProEt.topology X) φ).IsLeftAdjoint :=
      (ordinaryAdjunction (ProEt.topology X) φ).isLeftAdjoint
    letI : (ordinaryExtension (ProEt.topology X) φ).PreservesFlat :=
      proScalarPreservesFlat X φ
    (proCore X φ).toMonoidal =
      (finiteHomNativeDerivedCore (ordinaryExtension (ProEt.topology X) φ)).toMonoidal := by
  let : Algebra A B := φ.toAlgebra
  let := AlgebraicGeometry.ProEtale.preservesKFlatQuasiIso_sheafExtendScalars A B X
  let : (ordinaryExtension (ProEt.topology X) φ).Monoidal :=
    finiteHomOrdinaryMonoidal (ProEt.topology X) φ
  let : (ordinaryExtension (ProEt.topology X) φ).IsLeftAdjoint :=
    (ordinaryAdjunction (ProEt.topology X) φ).isLeftAdjoint
  let : (ordinaryExtension (ProEt.topology X) φ).PreservesFlat :=
    proScalarPreservesFlat X φ
  have he :
      (AlgebraicGeometry.ProEtale.leftDerivedSheafExtendScalarsAdjunction A B X).leftAdjointUniq
        (finiteHomScalarAdjunction (ProEt.topology X) φ) = Iso.refl _ := by
    rw [proAdjNative]
    apply Iso.ext
    exact Adjunction.leftAdjointUniq_refl _
  unfold proCore
  dsimp only
  rw [he]
  trans AlgebraicGeometry.ProEtale.leftDerivedSheafExtendScalarsMonoidal
    (R := A) (S := B) X
  · exact monoidalTransportRefl
      (h := AlgebraicGeometry.ProEtale.leftDerivedSheafExtendScalarsMonoidal
        (R := A) (S := B) X)
      (AlgebraicGeometry.ProEtale.sheafExtendScalars (algebraMap A B) X).leftDerivedFunctor
  · unfold AlgebraicGeometry.ProEtale.leftDerivedSheafExtendScalarsMonoidal
    exact (nativeDerivedCore_eq _).symm

@[instance_reducible]
private def nativeScalarMonoidal
    {S : Type (u + 1)} [Category.{u} S] [EssentiallySmall.{u + 1} S]
    (J : GrothendieckTopology S) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) : (finiteHomScalar J φ).Monoidal := by
  let : (ordinaryExtension J φ).Monoidal := finiteHomOrdinaryMonoidal J φ
  let : (ordinaryExtension J φ).IsLeftAdjoint := (ordinaryAdjunction J φ).isLeftAdjoint
  let : (ordinaryExtension J φ).PreservesFlat :=
    ⟨fun h ↦ CategoryTheory.Sheaf.flat_extendScalars_obj J φ h⟩
  exact (finiteHomNativeDerivedCore (ordinaryExtension J φ)).toMonoidal

private theorem fixedScalarMonoidal_eq
    {S : Type (u + 1)} [Category.{u} S] [EssentiallySmall.{u + 1} S]
    (J : GrothendieckTopology S) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) :
    letI : (finiteHomScalar J φ).Monoidal := nativeScalarMonoidal J φ
    finiteCoefficientScalarMonoidal J φ =
      Functor.Monoidal.transport (finiteHomScalarFixedIso J φ) := by
  unfold nativeScalarMonoidal
  rw [nativeDerivedCore_eq]
  unfold finiteCoefficientScalarMonoidal finiteHomScalarFixedIso
    finiteHomScalarAdjunction scalarDerivedAdjunction finiteHomOrdinaryMonoidal
  rfl


private theorem scalarFixed_isMonoidal
    {S : Type (u + 1)} [Category.{u} S] [EssentiallySmall.{u + 1} S]
    (J : GrothendieckTopology S) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) :
    letI : (finiteHomScalar J φ).Monoidal := nativeScalarMonoidal J φ
    letI : (extension J φ).Monoidal := finiteCoefficientScalarMonoidal J φ
    NatTrans.IsMonoidal (finiteHomScalarFixedIso J φ).hom := by
  let : (finiteHomScalar J φ).Monoidal := nativeScalarMonoidal J φ
  have h := Functor.Monoidal.natTransIsMonoidal_of_transport (finiteHomScalarFixedIso J φ)
  rw [← fixedScalarMonoidal_eq] at h
  exact h

/-- Monoidality for the specified native scalar tensorators and comparison pullbacks.
Source: thm-coef-finite-hom.proof.md, final paragraph
(blueprint: lem-coef-finite-hom-rho-monoidal). -/
def FiniteHomRhoMonoidal
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (X : Scheme.{u}) (φ : A →+* B) : Prop :=
  letI : (etaleScalar X φ).Monoidal := (etaleCore X φ).toMonoidal
  letI : (proEtaleScalar X φ).Monoidal := (proCore X φ).toMonoidal
  letI : (comparisonNu (R := A) X).Monoidal :=
    AlgebraicGeometry.ProEtale.siteComparisonDerivedMonoidal (ModuleCat A) X
  letI : (comparisonNu (R := B) X).Monoidal :=
    AlgebraicGeometry.ProEtale.siteComparisonDerivedMonoidal (ModuleCat B) X
  NatTrans.IsMonoidal (finiteHomRhoIso X φ).inv

/-- The canonical scalar/site mate preserves the specified tensor and unit maps.
Source: thm-coef-finite-hom.proof.md, final paragraph
(blueprint: lem-coef-finite-hom-rho-monoidal).

Proof: use the existing balanced scalar/site comparison theorem
finiteCoefficientSiteComparison_isMonoidal, which states monoidality for the
fixed-adjoint scalar structures. Its stated proof is K-flat tensor normalization. Identify those
structures with transport of the native generic derived scalar tensor structure
along finiteHomScalarFixedIso. On the etale side the native structure is etaleCore
by definition. On the pro-etale side the side-framework scalar adjunction equals
the native scalar adjunction, so its uniqueness isomorphism is identity;
coreMonoidalTransport therefore recovers exactly proCore. The canonical
native-to-fixed isomorphisms are monoidal for the transported structures.
Whisker their hom and inverse with the site functors and compose with the fixed
balanced comparison. This composite is precisely finiteHomRhoIso.inv.
Monoidality is preserved by these operations, giving the tensor and unit equations
for the specified cores without choosing any new comparison. -/
theorem coefFiniteHomRhoMonoidal
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (X : Scheme.{u}) (φ : A →+* B) : FiniteHomRhoMonoidal X φ := by
  have he : (etaleCore X φ).toMonoidal = nativeScalarMonoidal X.smallEtaleTopology φ := by
    unfold etaleCore nativeScalarMonoidal
    rfl
  have hp : (proCore X φ).toMonoidal = nativeScalarMonoidal (ProEt.topology X) φ := by
    exact proNative X φ
  unfold FiniteHomRhoMonoidal
  rw [he, hp]
  let : (finiteHomScalar X.smallEtaleTopology φ).Monoidal :=
    nativeScalarMonoidal X.smallEtaleTopology φ
  let : (finiteHomScalar (ProEt.topology X) φ).Monoidal :=
    nativeScalarMonoidal (ProEt.topology X) φ
  let : (extension X.smallEtaleTopology φ).Monoidal :=
    finiteCoefficientScalarMonoidal X.smallEtaleTopology φ
  let : (extension (ProEt.topology X) φ).Monoidal :=
    finiteCoefficientScalarMonoidal (ProEt.topology X) φ
  let : (comparisonNu (R := A) X).Monoidal :=
    AlgebraicGeometry.ProEtale.siteComparisonDerivedMonoidal (ModuleCat A) X
  let : (comparisonNu (R := B) X).Monoidal :=
    AlgebraicGeometry.ProEtale.siteComparisonDerivedMonoidal (ModuleCat B) X
  let : ((AlgebraicGeometry.ProEtale.comparisonUpperStar
      (ModuleCat A) X).mapDerivedCategory).Monoidal :=
    AlgebraicGeometry.ProEtale.siteComparisonDerivedMonoidal (ModuleCat A) X
  let : ((AlgebraicGeometry.ProEtale.comparisonUpperStar
      (ModuleCat B) X).mapDerivedCategory).Monoidal :=
    AlgebraicGeometry.ProEtale.siteComparisonDerivedMonoidal (ModuleCat B) X
  let het := scalarFixed_isMonoidal X.smallEtaleTopology φ
  let hpro := scalarFixed_isMonoidal (ProEt.topology X) φ
  let hfixed : NatTrans.IsMonoidal (comparisonIso X φ).inv := by
    exact finiteCoefficientSiteComparison_isMonoidal X φ
  simp only [finiteHomRhoIso, Iso.trans_inv, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Iso.symm_inv]
  infer_instance

end WeilConjectures
