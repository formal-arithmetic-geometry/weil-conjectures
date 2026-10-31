/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportCoefficientChange
import all WeilConjectures.AlgebraicGeometry.Etale.Restriction.EtaleRestrictionBaseChange

/-! # Scalar restriction and compactification comparisons

Source: Stacks Project, Tags 0F7J and 0GL6.
(blueprint: lem-sf-etale-restriction-compactification).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale

private theorem scalar_leftUnitor_inv
    {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
    {R : C' ⥤ C} {S : D' ⥤ D} {F : C ⥤ D} {F' : C' ⥤ D'}
    (q : R ⋙ F ≅ F' ⋙ S) :
    CoeffCompatible q
      (pasteTwoSquaresIso (Functor.rightUnitor R ≪≫ (Functor.leftUnitor R).symm) q)
      (Functor.leftUnitor F).inv (Functor.leftUnitor F').inv := by
  intro K
  simp [pasteTwoSquaresIso_hom_app]

private theorem scalar_refinement_paste
    (FA FB : CompactSupportFormalism) [FA.HasBaseChange] [FB.HasBaseChange]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d) (hr : IsPullback c.i (𝟙 X) r.hom d.i)
    (s : ∀ W : Scheme.{u}, FB.obj W ⥤ FA.obj W)
    (ci : s X ⋙ FA.sh c.i ≅ FB.sh c.i ⋙ s c.Z)
    (di : s X ⋙ FA.sh d.i ≅ FB.sh d.i ⋙ s d.Z)
    (q : s d.Z ⋙ FA.pb r.hom ≅ FB.pb r.hom ⋙ s c.Z)
    (p : s c.Z ⋙ FA.pf r.hom ≅ FB.pf r.hom ⋙ s d.Z)
    (dg : s d.Z ⋙ FA.pf d.g ≅ FB.pf d.g ⋙ s Y)
    (cg : s c.Z ⋙ FA.pf c.g ≅ FB.pf c.g ⋙ s Y)
    (qi : s X ⋙ FA.pb (𝟙 X) ≅ FB.pb (𝟙 X) ⋙ s X)
    (hi : CoeffCompatible qi
      (Functor.rightUnitor (s X) ≪≫ (Functor.leftUnitor (s X)).symm)
      (FA.pbId X).hom (FB.pbId X).hom)
    (hb : CoeffCompatible (pasteTwoSquaresIso qi ci) (pasteTwoSquaresIso di q)
      (FA.baseChange (𝟙 X) c.i d.i r.hom hr.flip.w).natTrans
      (FB.baseChange (𝟙 X) c.i d.i r.hom hr.flip.w).natTrans)
    (hm : (mateEquiv (FB.adj r.hom) (FA.adj r.hom)
      (TwoSquare.mk _ _ _ _ q.hom)).natTrans = p.inv)
    (hp : CoeffCompatible (pasteTwoSquaresIso p dg) cg
      (FA.pfComp' r.hom d.g c.g r.hom_g).inv
      (FB.pfComp' r.hom d.g c.g r.hom_g).inv) :
    CoeffCompatible (pasteTwoSquaresIso di dg) (pasteTwoSquaresIso ci cg)
      (FA.refinementComparison r hr) (FB.refinementComparison r hr) := by
  have := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := FA) hr.flip
  have := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := FB) hr.flip
  let βA : FA.sh c.i ≅ FA.sh d.i ⋙ FA.pb r.hom :=
    (Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight (FA.pbId X).symm _ ≪≫
      asIso (FA.baseChange (𝟙 X) c.i d.i r.hom hr.flip.w).natTrans
  let βB : FB.sh c.i ≅ FB.sh d.i ⋙ FB.pb r.hom :=
    (Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight (FB.pbId X).symm _ ≪≫
      asIso (FB.baseChange (𝟙 X) c.i d.i r.hom hr.flip.w).natTrans
  have hβA : (FA.baseChange (𝟙 X) c.i d.i r.hom hr.flip.w).natTrans =
      Functor.whiskerRight (FA.pbId X).hom (FA.sh c.i) ≫
        (Functor.leftUnitor _).hom ≫ βA.hom := by
    dsimp only [βA, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_hom, asIso_hom]
    rw [Iso.hom_inv_id_assoc, ← Functor.whiskerRight_comp_assoc,
      Iso.hom_inv_id, Functor.whiskerRight_id', Category.id_comp]
  have hβB : (FB.baseChange (𝟙 X) c.i d.i r.hom hr.flip.w).natTrans =
      Functor.whiskerRight (FB.pbId X).hom (FB.sh c.i) ≫
        (Functor.leftUnitor _).hom ≫ βB.hom := by
    dsimp only [βB, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_hom, asIso_hom]
    rw [Iso.hom_inv_id_assoc, ← Functor.whiskerRight_comp_assoc,
      Iso.hom_inv_id, Functor.whiskerRight_id', Category.id_comp]
  have hh := ((scalar_leftUnitor_inv ci).comp
    ((CoeffCompatible.inv (e := FA.pbId X) (e' := FB.pbId X) hi).whiskerRight ci)).comp hb
  have hbc : CoeffCompatible ci (pasteTwoSquaresIso di q) βA.hom βB.hom := by
    simpa only [βA, βB, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_hom, asIso_hom, Category.assoc] using hh
  rw [FA.refinementComparison_eq_of_baseChange r hr βA hβA,
    FB.refinementComparison_eq_of_baseChange r hr βB hβB]
  intro K
  simp only [pasteTwoSquaresIso_hom_app]
  exact Adjunction.comparison_restrict (FA.adj r.hom) (FB.adj r.hom) βA βB
    (FA.pfComp' r.hom d.g c.g r.hom_g).symm
    (FB.pfComp' r.hom d.g c.g r.hom_g).symm ci di q p dg cg hm
    (fun N ↦ by simpa only [pasteTwoSquaresIso_hom_app, Category.assoc] using hbc N)
    (fun N ↦ by
      simpa only [Iso.symm_hom, pasteTwoSquaresIso_hom_app, Functor.comp_obj,
        Category.assoc] using hp N) K

private theorem scalarRestrictionPlus_refinement
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (hr : IsPullback c.i (𝟙 X) r.hom d.i) :
    CoeffCompatible (compactSupportCoefficientRestrictionPlus φ d)
      (compactSupportCoefficientRestrictionPlus φ c)
      ((derivedPlusFormalism (ModuleCat.{u + 1} A)).refinementComparison r hr)
      ((derivedPlusFormalism (ModuleCat.{u + 1} B)).refinementComparison r hr) := by
  exact scalar_refinement_paste
    (derivedPlusFormalism (ModuleCat.{u + 1} A))
    (derivedPlusFormalism (ModuleCat.{u + 1} B)) r hr
    (fun W ↦ scalarRestrictionPlus φ W)
    (scalarOpenPlus φ c.i) (scalarOpenPlus φ d.i)
    (scalarPullbackPlus φ r.hom) (scalarPushforwardPlus φ r.hom)
    (scalarPushforwardPlus φ d.g) (scalarPushforwardPlus φ c.g)
    (scalarPullbackPlus φ (𝟙 X)) (scalarPullbackPlus_id φ X)
    (compactSupportRestrictionPlus_openBaseChange φ (𝟙 X) c.i d.i r.hom hr.flip.w)
    (congrArg TwoSquare.natTrans (scalarPushforwardPlus_mate φ r.hom))
    (scalarPushforwardPlus_comp φ r.hom d.g c.g r.hom_g)

/-- Scalar restriction respects the canonical comparison between two compactifications.
Source: Stacks Project, Tag 0F7J (independence of compactification), and Tag 0GL6.
(blueprint: lem-sf-etale-restriction-compactification).

Proof: form the common refinement of c and d with its two cartesian refinement
squares. For each leg, normalize the open base-change map by the inverse pullback
identity isomorphism. The scalar pullback identity equation and the open
base-change compatibility give the scalar square for this normalized map.
The refinement comparison is the unit of pullback/direct-image adjunction,
followed by the inverse normalized open base-change map and the proper
composition isomorphism. Apply comparison_restrict, using the normalized
derived mate identity and the proper composition square. This gives compatibility
for each refinement leg. Invert the second leg and paste the two squares.
The resulting isomorphism is exactly the canonical compactification comparison.
The common refinement requires only quasi-compactness of f. For c = d the
comparison is the identity and the equation reduces to the identity square. -/
theorem compactSupportRestrictionPlus_compactification
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (rightDerivedLowerShriekOfCompactificationPlusIso A c d).hom.app
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.obj L) ≫
      (compactSupportCoefficientRestrictionPlus φ d).hom.app L =
    (compactSupportCoefficientRestrictionPlus φ c).hom.app L ≫
      (Sheaf.restrictScalars Y.smallEtaleTopology φ).mapDerivedCategoryPlus.map
        ((rightDerivedLowerShriekOfCompactificationPlusIso B c d).hom.app L) := by
  let FA := derivedPlusFormalism (ModuleCat.{u + 1} A)
  let FB := derivedPlusFormalism (ModuleCat.{u + 1} B)
  have h₁ := scalarRestrictionPlus_refinement φ (Compactification.infFst c d)
    (Compactification.isPullback_infFst c d)
  have h₂ := CoeffCompatible.inv
    (e := asIso (FA.refinementComparison (Compactification.infSnd c d)
      (Compactification.isPullback_infSnd c d)))
    (e' := asIso (FB.refinementComparison (Compactification.infSnd c d)
      (Compactification.isPullback_infSnd c d)))
    (scalarRestrictionPlus_refinement φ (Compactification.infSnd c d)
      (Compactification.isPullback_infSnd c d))
  have h := h₁.comp h₂
  change CoeffCompatible (compactSupportCoefficientRestrictionPlus φ c)
    (compactSupportCoefficientRestrictionPlus φ d) (FA.shriekIso c d).hom
    (FB.shriekIso c d).hom at h
  rw [derivedPlusFormalism_shriekIso, derivedPlusFormalism_shriekIso] at h
  exact (h L).symm
end AlgebraicGeometry.Etale
