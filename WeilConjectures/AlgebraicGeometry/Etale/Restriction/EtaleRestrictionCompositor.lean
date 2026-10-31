/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportCoefficientChange
import WeilConjectures.AlgebraicGeometry.Etale.Restriction.EtaleRestrictionCompactification
import WeilConjectures.AlgebraicGeometry.Etale.Restriction.EtaleRestrictionTriangle
import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeExchange

/-! # Scalar restriction and the canonical etale compositor

Source: Stacks Project, more-etale.tex, Tags 0F7J and 0GL6.
(blueprint: lem-sf-etale-restriction-compositor).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale

private theorem scalar_paste_component_iff
    {C C' D D' E E' : Type*}
    [Category C] [Category C'] [Category D] [Category D'] [Category E] [Category E']
    {R : C' ⥤ C} {S : D' ⥤ D} {U : E' ⥤ E}
    {F : C ⥤ D} {F' : C' ⥤ D'} {G : D ⥤ E} {G' : D' ⥤ E'}
    {H : C ⥤ E} {H' : C' ⥤ E'}
    (cF : R ⋙ F ≅ F' ⋙ S) (cG : S ⋙ G ≅ G' ⋙ U) (cH : R ⋙ H ≅ H' ⋙ U)
    (α : F ⋙ G ⟶ H) (β : F' ⋙ G' ⟶ H') :
    CoeffCompatible (pasteTwoSquaresIso cF cG) cH α β ↔
      ∀ K : C', α.app (R.obj K) ≫ cH.hom.app K =
        G.map (cF.hom.app K) ≫ cG.hom.app (F'.obj K) ≫ U.map (β.app K) := by
  constructor
  · intro h K
    simpa only [pasteTwoSquaresIso_hom_app, Category.assoc] using (h K).symm
  · intro h K
    simpa only [pasteTwoSquaresIso_hom_app, Category.assoc] using (h K).symm

private theorem scalar_canonical_paste
    (FA FB : CompactSupportFormalism) [FA.HasProperExchange] [FB.HasProperExchange]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (s : ∀ W : Scheme.{u}, FB.obj W ⥤ FA.obj W)
    (cf : s X ⋙ FA.lowerShriek f ≅ FB.lowerShriek f ⋙ s Y)
    (cg : s Y ⋙ FA.lowerShriek g ≅ FB.lowerShriek g ⋙ s Z)
    (cfg : s X ⋙ FA.lowerShriek (f ≫ g) ≅ FB.lowerShriek (f ≫ g) ⋙ s Z) :
    let T := Compactification.Triangle.ofHasCompactification f g
    ∀ (ct : s X ⋙ FA.shriek T.cf ≅ FB.shriek T.cf ⋙ s Y)
      (ctfg : s X ⋙ FA.shriek T.cfg ≅ FB.shriek T.cfg ⋙ s Z),
    CoeffCompatible cf ct
        (FA.shriekIso (HasCompactification.compactification f) T.cf).hom
        (FB.shriekIso (HasCompactification.compactification f) T.cf).hom →
      CoeffCompatible (pasteTwoSquaresIso ct cg) ctfg
        (FA.compIso T).hom (FB.compIso T).hom →
      CoeffCompatible ctfg cfg
        (FA.shriekIso T.cfg (HasCompactification.compactification (f ≫ g))).hom
        (FB.shriekIso T.cfg (HasCompactification.compactification (f ≫ g))).hom →
      CoeffCompatible (pasteTwoSquaresIso cf cg) cfg
        (FA.lowerShriekCompIso f g).hom (FB.lowerShriekCompIso f g).hom := by
  dsimp only
  intro ct ctfg hf ht hfg
  exact (hf.whiskerRight cg).comp (ht.comp hfg)

private theorem scalar_compactification_comparison
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f) :
    CoeffCompatible (compactSupportCoefficientRestrictionPlus φ c)
      (compactSupportCoefficientRestrictionPlus φ d)
      ((derivedPlusFormalism (ModuleCat.{u + 1} A)).shriekIso c d).hom
      ((derivedPlusFormalism (ModuleCat.{u + 1} B)).shriekIso c d).hom := by
  rw [derivedPlusFormalism_shriekIso, derivedPlusFormalism_shriekIso]
  intro K
  exact (compactSupportRestrictionPlus_compactification φ c d K).symm

private theorem scalar_triangle_comparison
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T : Compactification.Triangle f g) :
    CoeffCompatible
      (pasteTwoSquaresIso (compactSupportCoefficientRestrictionPlus φ T.cf)
        (compactSupportCoefficientRestrictionPlus φ T.cg))
      (compactSupportCoefficientRestrictionPlus φ T.cfg)
      ((derivedPlusFormalism (ModuleCat.{u + 1} A)).compIso T).hom
      ((derivedPlusFormalism (ModuleCat.{u + 1} B)).compIso T).hom := by
  exact (scalar_paste_component_iff _ _ _ _ _).2
    (fun K ↦ compactSupportRestrictionPlus_triangle φ T K)

set_option maxHeartbeats 800000 in
-- Specialize the canonical pasting equation without expanding inferred formalism types.
private theorem scalar_compositor_comparison
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)] :
    CoeffCompatible
      (pasteTwoSquaresIso
        (compactSupportCoefficientRestrictionPlus φ (HasCompactification.compactification f))
        (compactSupportCoefficientRestrictionPlus φ (HasCompactification.compactification g)))
      (compactSupportCoefficientRestrictionPlus φ
        (HasCompactification.compactification (f ≫ g)))
      (rightDerivedLowerShriekPlusCompIso A f g).hom
      (rightDerivedLowerShriekPlusCompIso B f g).hom := by
  exact scalar_canonical_paste
    (derivedPlusFormalism (ModuleCat.{u + 1} A))
    (derivedPlusFormalism (ModuleCat.{u + 1} B)) f g
    (fun W ↦ (Sheaf.restrictScalars W.smallEtaleTopology φ).mapDerivedCategoryPlus)
    (compactSupportCoefficientRestrictionPlus φ (HasCompactification.compactification f))
    (compactSupportCoefficientRestrictionPlus φ (HasCompactification.compactification g))
    (compactSupportCoefficientRestrictionPlus φ (HasCompactification.compactification (f ≫ g)))
    (compactSupportCoefficientRestrictionPlus φ
      (Compactification.Triangle.ofHasCompactification f g).cf)
    (compactSupportCoefficientRestrictionPlus φ
      (Compactification.Triangle.ofHasCompactification f g).cfg)
    (scalar_compactification_comparison φ _ _)
    (scalar_triangle_comparison φ _)
    (scalar_compactification_comparison φ _ _)

/-- Scalar restriction commutes with the specified compact-support compositor.
Source: Stacks Project, Tags 0F7J and 0GL6
(blueprint: lem-sf-etale-restriction-compositor).

Proof: compute the compositor on the compatible compactification triangle. On its
proper factors, restriction commutes with the direct-image compositors by the
K-injective normalization of the derived direct-image comparison. On the open
factors, transpose under the extension-by-zero adjunction: both paths are the same
restriction/inverse-image identification, so the unit identities give equality.
For the mixed factor, paste that identification with the cartesian inverse-image
square and take mates. This proves the restriction square for proper/open
interchange. Whisker these three equations to obtain the square for the triangle.
For an arbitrary chosen compactification, use the two cartesian legs of the
common refinement. Express each refinement comparison by the pullback/direct-image
unit, the normalized open base-change isomorphism, and proper composition. The
same mate calculation commutes restriction with these maps; inverse comparisons
cancel. This is the displayed equation for the canonical chosen compositor.
No scalar tensor, finite Tor amplitude or faithfulness of derived restriction is
used. Identity ring maps and identity geometric maps give the respective unit
identities; the zero coefficient ring is included. -/
theorem compactSupportRestrictionPlus_compositor
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (rightDerivedLowerShriekPlusCompIso A f g).hom.app
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.obj L) ≫
      (compactSupportCoefficientRestrictionPlus φ
        (HasCompactification.compactification (f ≫ g))).hom.app L =
    (rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) g).map
        ((compactSupportCoefficientRestrictionPlus φ
          (HasCompactification.compactification f)).hom.app L) ≫
      (compactSupportCoefficientRestrictionPlus φ
        (HasCompactification.compactification g)).hom.app
          ((rightDerivedLowerShriekPlus (ModuleCat.{u + 1} B) f).obj L) ≫
      (Sheaf.restrictScalars Z.smallEtaleTopology φ).mapDerivedCategoryPlus.map
        ((rightDerivedLowerShriekPlusCompIso B f g).hom.app L) := by
  exact (scalar_paste_component_iff _ _ _ _ _).1 (scalar_compositor_comparison φ f g) L

end AlgebraicGeometry.Etale
