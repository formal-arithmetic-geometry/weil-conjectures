/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.GlobalHomPullbackComparison
import WeilConjectures.AlgebraicGeometry.MixedGlobalHomBaseChangeCounitTransport

/-!
# Transport of global Hom comparisons across a counit square

Source: Stacks Project, Tag 0AA8, the commutative diagrams in the final part of the proof.
(blueprint: lem-sc-global-hom-base-change-counit-transport).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry

section Compatibility

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (R : Type u) [Ring R], HasDerivedCategory.{w} (ModuleCat.{u} R)]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem legacyLeray_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    schemeGlobalSectionsDirectImageIso f = mixedGlobalSectionsDirectImageIso f := by
  rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
omit [∀ (R : Type u) [Ring R], HasDerivedCategory.{w} (ModuleCat.{u} R)] in
private theorem legacyTensor_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    schemeHomTensorPullbackIso f = mixedHomTensorPullbackIso f := by
  ext Z
  rfl

-- The right side is the complete former definition, with its original wrapper names.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem legacyPullbackComparison_eq
    {S T : Scheme.{u}} (h : T ⟶ S) (P Q : schemeDerivedCategory S) :
    schemeGlobalDerivedHom_pullback_comparison h P Q =
  (schemeDerivedGlobalSections S).map
      ((schemeHomPullbackAdjunction h).homEquiv _ _
        (((schemeDerivedTensorHomEquiv T)
          ((derivedPullback h).obj
            ((derivedInternalHom (Opens.grothendieckTopology S) S.sheaf).obj (op P, Q)))
          ((derivedPullback h).obj P) ((derivedPullback h).obj Q)).symm
            ((schemeHomTensorPullbackIso h).inv.app
              ((derivedInternalHom (Opens.grothendieckTopology S) S.sheaf).obj (op P, Q), P) ≫
              (derivedPullback h).map
                ((schemeDerivedTensorHomEquiv S)
                  ((derivedInternalHom (Opens.grothendieckTopology S) S.sheaf).obj (op P, Q))
                  P Q (𝟙 _))))) ≫
    (schemeGlobalSectionsDirectImageIso h).hom.app
      ((derivedInternalHom (Opens.grothendieckTopology T) T.sheaf).obj
        (op ((derivedPullback h).obj P), (derivedPullback h).obj Q)) := by
  dsimp only [schemeGlobalDerivedHom_pullback_comparison]
  simp only [legacyTensor_eq h, legacyLeray_eq h]
  rfl


end Compatibility

/-- The pullback and direct-image global Hom comparisons transport a commuting
counit square. This assertion concerns arbitrary derived objects and morphisms;
no right adjoints on quasi-coherent categories or right-adjoint base-change map
are used.

Source: Stacks Project, Tag 0AA8, the final commutative diagrams; the comparisons
are the evaluation mates of Tags 08I3 and 0B6I.
(blueprint: lem-sc-global-hom-base-change-counit-transport).

Proof: specialize mixedGlobalHom_baseChange_counit_transport to equal sheaf
and module localization universes. The pullback comparisons are the same
normalized evaluation mates. The direct-image comparisons choose witnesses of
the same existence statement, so proof irrelevance identifies the witnesses.
Unfold these comparison wrappers to obtain the asserted identity. -/
theorem schemeGlobalHom_baseChange_counit_transport
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (R : Type u) [Ring R], HasDerivedCategory.{w} (ModuleCat.{u} R)]
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (M N : schemeDerivedCategory X) (E : schemeDerivedCategory (pullback f g))
    (K : schemeDerivedCategory Y)
    (t : (derivedPullback (pullback.fst f g)).obj N ⟶ E)
    (e : (schemeDerivedDirectImage f).obj N ⟶ K)
    (e' : (schemeDerivedDirectImage (pullback.snd f g)).obj E ⟶
      (derivedPullback g).obj K)
    [IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g
      (pullback.fst f g) pullback.condition M)]
    (h : schemeDerivedBaseChangeMap f (pullback.snd f g) g
        (pullback.fst f g) pullback.condition N ≫
      (schemeDerivedDirectImage (pullback.snd f g)).map t ≫ e' =
        (derivedPullback g).map e) :
    (schemeGlobalScalarRestriction f).map
      (schemeGlobalDerivedHom_pullback_comparison (pullback.fst f g) M N ≫
        (schemeGlobalScalarRestriction (pullback.fst f g)).map
          ((schemeGlobalDerivedHom (pullback f g)).map ((𝟙 _).op, t))) ≫
      (schemeGlobalScalarSquareIso f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition).hom.app
          ((schemeGlobalDerivedHom (pullback f g)).obj
            (op ((derivedPullback (pullback.fst f g)).obj M), E)) ≫
      (schemeGlobalScalarRestriction g).map
        (schemeGlobalHomDirectImageMap (pullback.snd f g)
            ((derivedPullback (pullback.fst f g)).obj M) E ≫
          (schemeGlobalDerivedHom Y').map ((𝟙 _).op, e')) =
    (schemeGlobalHomDirectImageMap f M N ≫
        (schemeGlobalDerivedHom Y).map ((𝟙 _).op, e)) ≫
      schemeGlobalDerivedHom_pullback_comparison g
        ((schemeDerivedDirectImage f).obj M) K ≫
      (schemeGlobalScalarRestriction g).map
        ((schemeGlobalDerivedHom Y').map
          (X := (op ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj M)),
            (derivedPullback g).obj K))
          (Y := (op ((schemeDerivedDirectImage (pullback.snd f g)).obj
            ((derivedPullback (pullback.fst f g)).obj M)), (derivedPullback g).obj K))
          ((inv (schemeDerivedBaseChangeMap f (pullback.snd f g) g
            (pullback.fst f g) pullback.condition M)).op, 𝟙 _)) := by
  simpa only [schemeGlobalDerivedHom_pullback_comparison,
    mixedGlobalHomPullbackComparison, schemeGlobalHomDirectImageMap,
    mixedGlobalHomDirectImageMap, mixedHomDirectImageComparison] using
    mixedGlobalHom_baseChange_counit_transport f g M N E K t e e' h

end AlgebraicGeometry
