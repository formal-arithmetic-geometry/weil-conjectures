/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement

/-! # Section-normalized encoding and restriction

(blueprint: lem-pur-normalized-section-encoding-restriction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.CompactSupportCondensedRealization

/-- Restriction along an internal coefficient map commutes with section encoding
and any two ring charts, by the unique isomorphism acting identically on sections.
Source: Stacks 00YV; the encoding step of blueprint sk-thm-purity-transport.
(blueprint: lem-pur-normalized-section-encoding-restriction).
Proof: the chart equations make the conjugated ring square commute. Consequently
the identity of underlying sections is linear for both restricted module actions.
These identities form a natural isomorphism; sectionwise extensionality proves
uniqueness. The argument applies to zero rings and empty sites as well. -/
theorem normalizedEncodingRestriction (W : Scheme.{u})
    (R S : Sheaf (ProEt.topology W) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ]
    (ψ : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (ProEt.topology W) R ⟶
        InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (ProEt.topology W) S) (hφ : ψ = CondensedRing.sectionRingMap W φ)
    (A B : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (eR : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (ProEt.topology W) R ≅ A)
    (eS : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (ProEt.topology W) S ≅ B) :
    let ER := (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (ProEt.topology W) R).functor ⋙
        (CondensedRing.ringModuleEquivalenceOfIso W ((adicLisseForget W).mapIso eR).symm).functor
    let ES := (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (ProEt.topology W) S).functor ⋙
        (CondensedRing.ringModuleEquivalenceOfIso W ((adicLisseForget W).mapIso eS).symm).functor
    ∃! d : Mod.comap φ ⋙ ER ≅
        ES ⋙ pbcRestrict (eR.inv ≫ ψ ≫ eS.hom),
      ∀ (M : Mod (Sheaf (ProEt.topology W) Ab.{u + 1}) S) (U : W.ProEtᵒᵖ)
        (x : (((Mod.comap φ ⋙ ER).obj M).val.obj U)),
        HEq ((d.hom.app M).val.app U x) x := by
  dsimp only
  let H := sheafCompose (ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let q := H.map (CondensedRing.sectionRingMap W φ)
  let t := H.map eR.inv
  let c := H.map eS.inv
  let π := H.map ((eR.inv ≫ ψ ≫ eS.hom))
  have hs : t ≫ q = π ≫ c := by
    dsimp only [t, q, π, c]
    rw [hφ]
    rw [← H.map_comp, ← H.map_comp]
    apply congrArg H.map
    simp only [Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  let GE := (CondensedRing.ringModuleEquivalenceOfIso W
    ((adicLisseForget W).mapIso eR).symm).functor
  let GF := (CondensedRing.ringModuleEquivalenceOfIso W
    ((adicLisseForget W).mapIso eS).symm).functor
  let VF := (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (ProEt.topology W) S).functor
  let e₂ : SheafOfModules.restrictScalars q ⋙ GE ≅
      GF ⋙ pbcRestrict ((eR.inv ≫ ψ ≫ eS.hom)) := by
    refine NatIso.ofComponents (fun M ↦ ?_) ?_
    · apply (SheafOfModules.fullyFaithfulForget _).preimageIso
      refine PresheafOfModules.isoMk (fun U ↦ ?_) ?_
      · refine ModuleCat.isoMk (Iso.refl _) ?_
        intro r
        ext m
        have hh := congrArg (fun f ↦ f.hom.app U r) hs
        let L := M.val.obj U
        change (c.hom.app U (π.hom.app U r)) • (show L from m) =
          (q.hom.app U (t.hom.app U r)) • (show L from m)
        exact congrArg (fun z ↦ z • (show L from m)) hh.symm
      · intro U V f
        ext x
        rfl
    · intro M N f
      ext U x
      rfl
  let a := CondensedRing.sectionModuleComapIso W φ
  let e : Mod.comap φ ⋙ ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
        (ProEt.topology W) R).functor ⋙ GE) ≅
      (VF ⋙ GF) ⋙
        pbcRestrict ((eR.inv ≫ ψ ≫ eS.hom)) :=
    NatIso.ofComponents (fun M ↦ GE.mapIso (a.app M) ≪≫ e₂.app (VF.obj M)) (by
      intro M N f
      ext U x
      rfl)
  have he : ∀ M U x, HEq ((e.hom.app M).val.app U x) x := by
    intro M U x
    rfl
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  ext M U x
  exact eq_of_heq ((he' M U x).trans (he M U x).symm)

end WeilConjectures.CompactSupportCondensedRealization
