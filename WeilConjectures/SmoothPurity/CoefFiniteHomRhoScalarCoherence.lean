/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CoefFiniteHom
import all WeilConjectures.AlgebraicGeometry.CoefficientScalarRepresentatives.CoefficientScalarRepresentatives
import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars

/-! # Scalar composition and identity for the specified site mate

Source: thm-coef-finite-hom.proof.md, final paragraph, successive coefficient change.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.CoefficientScalarRepresentatives
open scoped CategoryTheory.Functor CategoryTheory.TwoSquare
namespace WeilConjectures

local instance finiteHomRhoScalarProSmall (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

private theorem rhoNative
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (X : Scheme.{u}) (φ : A →+* B) :
    (finiteHomRhoIso X φ).hom =
      Adjunction.pushHomOfComapIso (finiteHomScalarAdjunction X.smallEtaleTopology φ)
        (finiteHomScalarAdjunction (ProEt.topology X) φ)
        (derivedComparisonRestriction X φ) := by
  let a := finiteHomScalarAdjunction X.smallEtaleTopology φ
  let b := finiteHomScalarAdjunction (ProEt.topology X) φ
  let af := adjunction X.smallEtaleTopology φ
  let bf := adjunction (ProEt.topology X) φ
  let w := TwoSquare.mk _ _ _ _ (comparisonMap X φ)
  have h := mateEquiv_leftAdjointUniq a af b bf w
  have hw : mateEquiv af bf w =
      TwoSquare.mk _ _ _ _ (derivedComparisonRestriction X φ).inv :=
    (mateEquiv af bf).apply_symm_apply _
  rw [hw] at h
  have hh : mateEquiv a b (TwoSquare.mk _ _ _ _ (finiteHomRhoIso X φ).hom) =
      TwoSquare.mk _ _ _ _ (derivedComparisonRestriction X φ).inv := by
    simpa only [finiteHomRhoIso, finiteHomScalarFixedIso, comparisonIso,
      Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, asIso_hom, a, b, af, bf, w,
      comparisonNu, TwoSquare.mk, TwoSquare.natTrans] using h
  exact congrArg TwoSquare.natTrans ((mateEquiv a b).injective
    (hh.trans ((mateEquiv a b).apply_symm_apply _).symm))

private theorem restrictionSiteUnit
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (X : Scheme.{u}) (φ : A →+* B)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) X).unit.app
      ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj M) ≫
      (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} A) X).map
        ((comparisonRestriction X φ).inv.app M) =
    (Sheaf.restrictScalars X.smallEtaleTopology φ).map
      ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B) X).unit.app M) := by
  have h := unit_mateEquiv (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B) X)
    (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) X)
    (TwoSquare.mk _ _ _ _ (comparisonRestriction X φ).inv) M
  have hm := comparison_restrict_mate X φ
  dsimp only [TwoSquare.natTrans] at hm
  rw [hm] at h
  simpa using h.symm

private theorem restrictionSiteChain
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (X : Scheme.{u}) (φ : A →+* B) (ψ : B →+* C)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} C)) :
    (comparisonRestriction X (ψ.comp φ)).inv.app M =
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).map
        ((Sheaf.restrictScalarsCompIso X.smallEtaleTopology φ ψ (ψ.comp φ) rfl).inv.app M) ≫
      (comparisonRestriction X φ).inv.app
        ((Sheaf.restrictScalars X.smallEtaleTopology ψ).obj M) ≫
      (Sheaf.restrictScalars (ProEt.topology X) φ).map
        ((comparisonRestriction X ψ).inv.app M) ≫
      (Sheaf.restrictScalarsCompIso (ProEt.topology X) φ ψ (ψ.comp φ) rfl).hom.app
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} C) X).obj M) := by
  apply ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) X).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [restrictionSiteUnit]
  erw [← (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) X).unit.naturality_assoc]
  erw [reassoc_of% (restrictionSiteUnit X φ
    ((Sheaf.restrictScalars X.smallEtaleTopology ψ).obj M))]
  change _ = _ ≫ (Sheaf.restrictScalars X.smallEtaleTopology φ).map
    ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B) X).unit.app
      ((Sheaf.restrictScalars X.smallEtaleTopology ψ).obj M)) ≫
    (Sheaf.restrictScalars X.smallEtaleTopology φ).map
      ((ProEtale.comparisonLowerStar (ModuleCat.{u + 1} B) X).map
        ((comparisonRestriction X ψ).inv.app M)) ≫ _
  rw [← Functor.map_comp_assoc, restrictionSiteUnit]
  ext U x
  rfl
private theorem derivedRestrictionSiteChain
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (X : Scheme.{u}) (φ : A →+* B) (ψ : B →+* C)
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} C))) :
    (derivedComparisonRestriction X (ψ.comp φ)).inv.app M =
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map
        ((Sheaf.derivedRestrictScalarsCompIso X.smallEtaleTopology rfl
          (f := φ) (g := ψ)).inv.app M) ≫
      (derivedComparisonRestriction X φ).inv.app
        ((Sheaf.derivedRestrictScalars X.smallEtaleTopology ψ).obj M) ≫
      (Sheaf.derivedRestrictScalars (ProEt.topology X) φ).map
        ((derivedComparisonRestriction X ψ).inv.app M) ≫
      (Sheaf.derivedRestrictScalarsCompIso (ProEt.topology X) rfl
        (f := φ) (g := ψ)).hom.app
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} C) X).mapDerivedCategory.obj M) := by
  have h := derive_chain.{u + 1}
    (Sheaf.restrictScalars X.smallEtaleTopology φ)
    (Sheaf.restrictScalars X.smallEtaleTopology ψ)
    (Sheaf.restrictScalars X.smallEtaleTopology (ψ.comp φ))
    (Sheaf.restrictScalars (ProEt.topology X) φ)
    (Sheaf.restrictScalars (ProEt.topology X) ψ)
    (Sheaf.restrictScalars (ProEt.topology X) (ψ.comp φ))
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X)
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X)
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} C) X)
    (comparisonRestriction X φ).symm (comparisonRestriction X ψ).symm
    (comparisonRestriction X (ψ.comp φ)).symm
    (Sheaf.restrictScalarsCompIso X.smallEtaleTopology φ ψ (ψ.comp φ) rfl)
    (Sheaf.restrictScalarsCompIso (ProEt.topology X) φ ψ (ψ.comp φ) rfl)
    (restrictionSiteChain X φ ψ) M
  simpa only [derivedComparisonRestriction, Sheaf.derivedRestrictScalarsCompIso,
    Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryNatIso_symm,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, Category.assoc] using h

section AbstractPasting
variable {A B C D E F : Type*}
  [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
  {LX : A ⥤ B} {UX : B ⥤ A} {MX : B ⥤ C} {VX : C ⥤ B}
  {LY : D ⥤ E} {UY : E ⥤ D} {MY : E ⥤ F} {VY : F ⥤ E}
  {NX : A ⥤ C} {WX : C ⥤ A} {NY : D ⥤ F} {WY : F ⥤ D}
  (ax : LX ⊣ UX) (bx : MX ⊣ VX) (cx : NX ⊣ WX)
  (ay : LY ⊣ UY) (by' : MY ⊣ VY) (cy : NY ⊣ WY)
  {G : A ⥤ D} {H : B ⥤ E} {I : C ⥤ F}
  (ka : H ⋙ UY ≅ UX ⋙ G) (kb : I ⋙ VY ≅ VX ⋙ H)
  (kc : I ⋙ WY ≅ WX ⋙ G)
  (rx : WX ≅ VX ⋙ UX) (ry : WY ≅ VY ⋙ UY)

-- Conjugate the restriction compositors and paste the two extension mates.
end AbstractPasting

private theorem derivedRestrictionSiteChainHom
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (X : Scheme.{u}) (φ : A →+* B) (ψ : B →+* C)
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} C))) :
    (Sheaf.derivedRestrictScalars (ProEt.topology X) φ).map
        ((derivedComparisonRestriction X ψ).hom.app M) ≫
      (derivedComparisonRestriction X φ).hom.app
        ((Sheaf.derivedRestrictScalars X.smallEtaleTopology ψ).obj M) ≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map
        ((Sheaf.derivedRestrictScalarsCompIso X.smallEtaleTopology rfl
          (f := φ) (g := ψ)).hom.app M) =
    (Sheaf.derivedRestrictScalarsCompIso (ProEt.topology X) rfl
      (f := φ) (g := ψ)).hom.app
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} C) X).mapDerivedCategory.obj M) ≫
      (derivedComparisonRestriction X (ψ.comp φ)).hom.app M := by
  let e :=
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.mapIso
      ((Sheaf.derivedRestrictScalarsCompIso X.smallEtaleTopology rfl
        (f := φ) (g := ψ)).symm.app M) ≪≫
    (derivedComparisonRestriction X φ).symm.app
      ((Sheaf.derivedRestrictScalars X.smallEtaleTopology ψ).obj M) ≪≫
    (Sheaf.derivedRestrictScalars (ProEt.topology X) φ).mapIso
      ((derivedComparisonRestriction X ψ).symm.app M) ≪≫
    (Sheaf.derivedRestrictScalarsCompIso (ProEt.topology X) rfl
      (f := φ) (g := ψ)).app
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} C) X).mapDerivedCategory.obj M)
  have he : (derivedComparisonRestriction X (ψ.comp φ)).symm.app M = e :=
    Iso.ext (derivedRestrictionSiteChain X φ ψ M)
  have hi := congrArg Iso.inv he
  simp only [e, Iso.app_inv, Iso.symm_inv, Iso.trans_inv,
    Functor.mapIso_inv] at hi
  have hh := congrArg
    ((Sheaf.derivedRestrictScalarsCompIso (ProEt.topology X) rfl
      (f := φ) (g := ψ)).hom.app
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} C) X).mapDerivedCategory.obj M) ≫ ·) hi
  simpa only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp] using hh.symm

private theorem nativeRhoChain
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (X : Scheme.{u}) (φ : A →+* B) (ψ : B →+* C) (K : EtaleDerived A X) :
    (finiteHomScalarComp (ProEt.topology X) φ ψ).hom.app ((comparisonNu X).obj K) ≫
        canonicalRho X (ψ.comp φ) K =
      (proEtaleScalar X ψ).map (canonicalRho X φ K) ≫
        canonicalRho X ψ ((etaleScalar X φ).obj K) ≫
        (comparisonNu X).map ((finiteHomScalarComp X.smallEtaleTopology φ ψ).hom.app K) := by
  have hc :
      Functor.whiskerRight (derivedComparisonRestriction X ψ).hom
          (Sheaf.derivedRestrictScalars (ProEt.topology X) φ) ≫
        Functor.whiskerLeft (Sheaf.derivedRestrictScalars X.smallEtaleTopology ψ)
          (derivedComparisonRestriction X φ).hom ≫
        Functor.whiskerRight
          (Sheaf.derivedRestrictScalarsCompIso X.smallEtaleTopology rfl
            (f := φ) (g := ψ)).hom (comparisonNu (R := A) X) =
      Functor.whiskerLeft (comparisonNu (R := C) X)
          (Sheaf.derivedRestrictScalarsCompIso (ProEt.topology X) rfl
            (f := φ) (g := ψ)).hom ≫
        (derivedComparisonRestriction X (ψ.comp φ)).hom := by
    ext M
    exact derivedRestrictionSiteChainHom X φ ψ M
  have h := push_pasting_canonical
    (finiteHomScalarAdjunction X.smallEtaleTopology φ)
    (finiteHomScalarAdjunction X.smallEtaleTopology ψ)
    (finiteHomScalarAdjunction X.smallEtaleTopology (ψ.comp φ))
    (finiteHomScalarAdjunction (ProEt.topology X) φ)
    (finiteHomScalarAdjunction (ProEt.topology X) ψ)
    (finiteHomScalarAdjunction (ProEt.topology X) (ψ.comp φ))
    (derivedComparisonRestriction X φ) (derivedComparisonRestriction X ψ)
    (derivedComparisonRestriction X (ψ.comp φ))
    (Sheaf.derivedRestrictScalarsCompIso X.smallEtaleTopology rfl).symm
    (Sheaf.derivedRestrictScalarsCompIso (ProEt.topology X) rfl).symm hc K
  simp only [scalarComp_eq_conjugate] at h
  simpa only [finiteHomScalarComp, Adjunction.leftAdjointCompIso, canonicalRho,
    rhoNative, comparisonNu] using h

private theorem nativeScalarCompUnit
    {D : Type (u + 1)} [Category.{u} D] [EssentiallySmall.{u + 1} D]
    (J : GrothendieckTopology D) (A : Type (u + 1)) [CommRing A] :
    finiteHomScalarComp J (RingHom.id A) (RingHom.id A) =
      Functor.isoWhiskerLeft (finiteHomScalar J (RingHom.id A))
        (finiteHomScalarId J A) ≪≫ (finiteHomScalar J (RingHom.id A)).rightUnitor := by
  unfold finiteHomScalarComp finiteHomScalarId
  apply Adjunction.leftAdjointCompIso_comp_id
  exact derived_comp_unit _ _ _ (by
    apply Iso.ext
    ext M U x
    rfl)

private theorem mateIdentityFromComposition
    {D P : Type*} [Category D] [Category P]
    (F : D ⥤ D) (G : P ⥤ P) (U : D ⥤ P)
    (ρ : U ⋙ G ≅ F ⋙ U) (i : F ≅ 𝟭 D) (j : G ≅ 𝟭 P)
    (h : ∀ K, G.map (j.hom.app (U.obj K)) ≫ ρ.hom.app K =
      G.map (ρ.hom.app K) ≫ ρ.hom.app (F.obj K) ≫ U.map (F.map (i.hom.app K)))
    (K : D) : ρ.hom.app K ≫ U.map (i.hom.app K) = j.hom.app (U.obj K) := by
  let : G.Faithful := Functor.Faithful.of_iso j.symm
  have hn := ρ.hom.naturality (i.hom.app K)
  dsimp only [Functor.comp_map, Functor.id_obj] at hn
  have hh := h K
  rw [← hn, ← G.map_comp_assoc] at hh
  exact (G.map_injective ((cancel_mono (ρ.hom.app K)).mp hh)).symm

private theorem isoToIdSelf
    {D : Type*} [Category D] (F : D ⥤ D) (i : F ≅ 𝟭 D) (K : D) :
    i.hom.app (F.obj K) = F.map (i.hom.app K) := by
  apply (cancel_mono (i.hom.app K)).mp
  exact (i.hom.naturality (i.hom.app K)).symm

private theorem nativeRhoId
    {A : Type (u + 1)} [CommRing A] [Finite A] (X : Scheme.{u})
    (K : EtaleDerived A X) :
    canonicalRho X (RingHom.id A) K ≫
        (comparisonNu X).map ((finiteHomScalarId X.smallEtaleTopology A).hom.app K) =
      (finiteHomScalarId (ProEt.topology X) A).hom.app ((comparisonNu X).obj K) := by
  apply mateIdentityFromComposition (etaleScalar X (RingHom.id A))
    (proEtaleScalar X (RingHom.id A)) (comparisonNu X)
    (finiteHomRhoIso X (RingHom.id A))
    (finiteHomScalarId X.smallEtaleTopology A) (finiteHomScalarId (ProEt.topology X) A)
  intro M
  have h := nativeRhoChain X (RingHom.id A) (RingHom.id A) M
  simp only [nativeScalarCompUnit, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    Functor.comp_obj, Functor.id_obj, Category.comp_id, isoToIdSelf, canonicalRho, etaleScalar,
    proEtaleScalar] at h
  convert h using 1
  rfl

/-- The scalar/site mate respects the prescribed scalar compositor and scalar unitor.
Source: thm-coef-finite-hom.proof.md, final paragraph
(blueprint: lem-coef-finite-hom-rho-scalar-coherence).

Proof: work first with the exact restriction functors and comparison inverse image.
The ordinary restriction/site square is the conjugate of the sectionwise identity
between coextension followed by direct image and direct image followed by coextension.
Restriction transitivity and identity are sectionwise the usual restriction maps.
Their composition squares therefore paste. Exact localization
preserves those natural-transformation equalities and its composition constraints.
Take inverse mates with respect to the scalar adjunctions. Horizontal pasting of
mates carries restriction transitivity to the scalar compositor and carries
the identity restriction isomorphism to the scalar unitor. Change the fixed scalar
adjunction to the native one using its unique unit-compatible isomorphism.
These isomorphisms are precisely the two factors in finiteHomRhoIso, and
uniqueness of adjoint comparisons cancels them in the pasted square. The resulting
component equation is the first clause below. For identity scalar maps, the
restriction compositor is the whiskered restriction unitor, first on sections and
then under exact localization. The canonical left adjoint compositor is therefore
the scalar functor applied to its unitor. Substitute identity maps in the first
clause, use naturality of the unitor and of the site mate, and cancel. The scalar
functor is faithful because its canonical unitor identifies it with identity.
This gives the second clause. No tensor equation, Hom comparison, or
invertibility of a Hom comparison enters either argument. -/
theorem coefFiniteHomRhoScalarCoherence
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (X : Scheme.{u}) (φ : A →+* B) (ψ : B →+* C) :
    (∀ K : EtaleDerived A X,
      (finiteHomScalarComp (ProEt.topology X) φ ψ).hom.app ((comparisonNu X).obj K) ≫
          canonicalRho X (ψ.comp φ) K =
        (proEtaleScalar X ψ).map (canonicalRho X φ K) ≫
          canonicalRho X ψ ((etaleScalar X φ).obj K) ≫
          (comparisonNu X).map
            ((finiteHomScalarComp X.smallEtaleTopology φ ψ).hom.app K)) ∧
      (∀ K : EtaleDerived A X,
        canonicalRho X (RingHom.id A) K ≫
            (comparisonNu X).map
              ((finiteHomScalarId X.smallEtaleTopology A).hom.app K) =
          (finiteHomScalarId (ProEt.topology X) A).hom.app ((comparisonNu X).obj K)) := by
  exact ⟨nativeRhoChain X φ ψ, nativeRhoId X⟩

end WeilConjectures
