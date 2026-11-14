/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechNormalization
import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechPullbackTotalBeta

/-! # Augmentation-preserving pullback maps of the additive Čech complexes
Source: Stacks Project, Tags 01FD, 01FB and 03P2. -/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A supplied augmented coefficient comparison induces a map of the Cech totals.
Source: Stacks Project, Tag 01FD, explicit tuple restriction maps in the proof.


In Cech degree zero, the square of k_y with the maps to the terminal objects
commutes by the same pullback projection calculation. Section transfer naturality
therefore gives the alpha equation. In resolution degree zero, naturality of J.ι
and hα identify the coordinate composite with the structural coefficient map
followed by J.ι at B_y. The inverse restrictFunctorΓ isomorphism used in beta
identifies a function on the open with a function on its open subscheme.
Naturality of this isomorphism identifies restriction to B_y with restriction
along hinter; structural pullback on these functions is precisely
unitToPushforwardObjUnit g.toRingCatSheafHom. After lifting by ULift, the supplied
coordinate equation identifies these sections with the corresponding beta(x')
sections. Product projection extensionality and total inclusion naturality give
the beta equation. This uses no cover or acyclicity. Empty families have zero
products; empty intersections have zero structural functions. Degree zero uses
the same equations, with no negative degree or boundary selection. -/
theorem exists_additiveCech_pullback_total_transfer
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (V : ι → Y.Opens)
    (hinter : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      (⨅ l, V (y l)) ≤ g ⁻¹ᵁ (⨅ l, U (y l)))
    (I : InjectiveResolution X.etaleAdditiveSheaf)
    (J : InjectiveResolution Y.etaleAdditiveSheaf)
    (α : I.cocomplex ⟶
      ((Etale.lowerStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex
        (.up ℕ)).obj J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 = Scheme.etaleAdditiveSheafToLowerStar g ≫
      (Etale.lowerStar AddCommGrpCat.{u + 1} g).map (J.ι.f 0))
    (n : ℕ) :
    ∃ t : additiveCechTotal U I ⟶ additiveCechTotal V J,
      (additiveCechAlpha U I n ≫ t.f n =
        (Etale.globalResolutionSectionTransfer g I.cocomplex J.cocomplex α).f n ≫
        additiveCechAlpha V J n) ∧
      (∀ (x : (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).X n)
        (x' : (cechOver Y.toSpecΓ V (SheafOfModules.unit Y.ringCatSheaf)).X n),
        (∀ y : Fin (n + 1) → ι,
            cechCoordinate Y.toSpecΓ V (SheafOfModules.unit Y.ringCatSheaf) n y
                x' =
              (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf).presheaf.map
                (homOfLE (hinter n y)).op
                ((SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom).val.app
                  (op (⨅ l, U (y l)))
                  (cechCoordinate X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf) n y
                    x))) → t.f n (additiveCechBeta U I n x) = additiveCechBeta V J n x') := by
  obtain ⟨t, hmap, ht⟩ := exists_additiveCech_pullback_total_map g U V hinter I J α n
  refine ⟨t, ht, ?_⟩
  exact additiveCech_pullback_total_beta g U V hinter I J α hα n t hmap

end AlgebraicGeometry.Scheme.Modules
