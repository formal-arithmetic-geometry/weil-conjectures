/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q67
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.CategoryTheory.Sites.CoverLifting
import Sheaf.CategoryTheory.SiteInverseImageTensor
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Localized ring-sheaf mates evaluated on graphs

Source: Stacks Project, Sites and Sheaves, Tags 03CE, 00Y0, 00VE and 00WX;
Modules on Sites, Tag 03EL (blueprint: lem-sfb-localized-ring-mate-graph-evaluation).

The helpers only expand the maps in the statement. In particular the mate uses the
specified Kan-extension/sheafification adjunction, and both forgetful and integer-unit
comparisons use the coprojection-normalized restriction comparisons.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The mate `u_* β ∘ e_u` for the specified ring inverse-image adjunction.
Source: Stacks, Tags 00VE, 00WX and 03CE
(blueprint: lem-sfb-localized-ring-mate-graph-evaluation). -/
noncomputable def proEtaleLocalizedRingMate {B : Scheme.{u}} (V : B.ProEt)
    (R : Sheaf (ProEt.topology B) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology V.left) CommRingCat.{u + 1})
    (β : (proEtaleSheafInverseImage V.hom CommRingCat.{u + 1}).obj R ≅ S) :
    R ⟶ (proEtaleSheafDirectImage V.hom CommRingCat.{u + 1}).obj S :=
  (proEtaleSheafAdjunction V.hom CommRingCat.{u + 1}).unit.app R ≫
    (proEtaleSheafDirectImage V.hom CommRingCat.{u + 1}).map β.hom

/-- The ring isomorphism `bar β : R|_V ≅ S` under the normalized restriction comparison.
Source: Stacks, Tags 03CE and 00Y0
(blueprint: lem-sfb-localized-ring-mate-graph-evaluation). -/
noncomputable def proEtaleLocalizedRingIso {B : Scheme.{u}} (V : B.ProEt)
    (c : ProEtaleObjectRestrictionComparison V CommRingCat.{u + 1})
    (R : Sheaf (ProEt.topology B) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology V.left) CommRingCat.{u + 1})
    (β : (proEtaleSheafInverseImage V.hom CommRingCat.{u + 1}).obj R ≅ S) :
    (AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
      V.hom V.prop).obj R ≅ S :=
  (c.sheafIso.app R).symm ≪≫ β

/-- The graph `(b, U → V)` in the localization/base-change adjunction.
Source: Stacks, Tag 03CE
(blueprint: lem-sfb-localized-ring-mate-graph-evaluation). -/
noncomputable def proEtaleLocalizationGraph {B : Scheme.{u}} (V : B.ProEt)
    (U : V.left.ProEt) (T : B.ProEt)
    (b : (MorphismProperty.Over.map (f := V.hom) ⊤ V.prop).obj U ⟶ T) :
    U ⟶ (proEtaleBaseChange V.hom).obj T :=
  (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ V.hom V.prop trivial).homEquiv U T b

/-- The identity of the underlying scheme identifies the composite of `V/V` with `V/B`.
Source: Stacks, Tag 00Y0
(blueprint: lem-sfb-localized-ring-mate-graph-evaluation). -/
def proEtaleLocalizationIdentityIso {B : Scheme.{u}} (V : B.ProEt) :
    (MorphismProperty.Over.map (f := V.hom) ⊤ V.prop).obj
      (ProEt.mk (𝟙 V.left)) ≅ V :=
  MorphismProperty.Over.isoMk (Iso.refl V.left) rfl

/-- The additive sheaf map from the integer sheaf determined by a global section `r`.
The constant-sheaf/evaluation adjunction sends it to `n ↦ n • r` at `B/B`.
Source: Stacks, Tags 00Y0 and 03EL
(blueprint: lem-sfb-localized-ring-mate-graph-evaluation). -/
noncomputable def proEtaleLocalizedSectionMap (B : Scheme.{u})
    (R : Sheaf (ProEt.topology B) CommRingCat.{u + 1})
    (r : R.obj.obj (op (ProEt.mk (𝟙 B)))) :
    (constantSheaf (ProEt.topology B) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶
      (sheafCompose (ProEt.topology B)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj R :=
  ((constantSheafAdj (ProEt.topology B) AddCommGrpCat.{u + 1}
    (MorphismProperty.Over.mkIdTerminal @WeaklyEtale B)).homEquiv _ _).symm
      (AddCommGrpCat.ofHom (uliftZMultiplesHom _ r))

/-- The canonical integer-unit isomorphism `Z_V ≅ u⁻¹ Z_B` in localization coordinates.
First commute restriction with sheafification, then invert the normalized comparison.
Source: Stacks, Tags 00Y0, 0H7J and 03EL
(blueprint: lem-sfb-localized-ring-mate-graph-evaluation). -/
noncomputable def proEtaleLocalizedIntegerUnit {B : Scheme.{u}} (V : B.ProEt)
    (cA : ProEtaleObjectRestrictionComparison V AddCommGrpCat.{u + 1}) :
    (constantSheaf (ProEt.topology V.left) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≅
      (proEtaleSheafInverseImage V.hom AddCommGrpCat.{u + 1}).obj
        ((constantSheaf (ProEt.topology B) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) :=
  letI : (MorphismProperty.Over.map (f := V.hom) ⊤ V.prop).IsContinuous
      (ProEt.topology V.left) (ProEt.topology B) :=
    ProEt.isContinuous_overMap (V := V.left) (U := B) V.prop
  letI : (MorphismProperty.Over.map (f := V.hom) ⊤ V.prop).IsCocontinuous
      (ProEt.topology V.left) (ProEt.topology B) :=
    ProEt.isCocontinuous_overMap (V := V.left) (U := B) V.prop
  (Functor.pushforwardContinuousSheafificationCompatibility
    (MorphismProperty.Over.map (f := V.hom) ⊤ V.prop) AddCommGrpCat.{u + 1}
      (ProEt.topology V.left) (ProEt.topology B)).app
        ((Functor.const B.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≪≫
    (cA.sheafIso.app _).symm

/-- The inverse-image/underlying-additive-sheaf comparison, through normalized restriction.
Both middle presheaves are literally `U ↦ R(U → V → B)` with their additive structure.
Source: Stacks, Tags 00Y0 and 03CE
(blueprint: lem-sfb-localized-ring-mate-graph-evaluation). -/
noncomputable def proEtaleLocalizedAbelianComparison {B : Scheme.{u}} (V : B.ProEt)
    (c : ProEtaleObjectRestrictionComparison V CommRingCat.{u + 1})
    (cA : ProEtaleObjectRestrictionComparison V AddCommGrpCat.{u + 1})
    (R : Sheaf (ProEt.topology B) CommRingCat.{u + 1}) :
    (proEtaleSheafInverseImage V.hom AddCommGrpCat.{u + 1}).obj
        ((sheafCompose (ProEt.topology B)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj R) ≅
      (sheafCompose (ProEt.topology V.left)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
          ((proEtaleSheafInverseImage V.hom CommRingCat.{u + 1}).obj R) :=
  cA.sheafIso.app _ ≪≫
    (sheafCompose (ProEt.topology V.left)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).mapIso (c.sheafIso.app R).symm

/-- Pull back the integer-to-`R` map and compose with `β`, using the canonical unit.
Source: Stacks, Tag 03EL
(blueprint: lem-sfb-localized-ring-mate-graph-evaluation). -/
noncomputable def proEtaleLocalizedPulledSection {B : Scheme.{u}} (V : B.ProEt)
    (c : ProEtaleObjectRestrictionComparison V CommRingCat.{u + 1})
    (cA : ProEtaleObjectRestrictionComparison V AddCommGrpCat.{u + 1})
    (R : Sheaf (ProEt.topology B) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology V.left) CommRingCat.{u + 1})
    (β : (proEtaleSheafInverseImage V.hom CommRingCat.{u + 1}).obj R ≅ S)
    (r : R.obj.obj (op (ProEt.mk (𝟙 B)))) :
    (constantSheaf (ProEt.topology V.left) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶
      (sheafCompose (ProEt.topology V.left)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj S :=
  (proEtaleLocalizedIntegerUnit V cA).hom ≫
    (proEtaleSheafInverseImage V.hom AddCommGrpCat.{u + 1}).map
      (proEtaleLocalizedSectionMap B R r) ≫
    (proEtaleLocalizedAbelianComparison V c cA R).hom ≫
    (sheafCompose (ProEt.topology V.left)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).map β.hom

/-- The specified Kan unit is projection restriction, and its ring-isomorphism mate
is evaluated on any graph by ordinary restriction followed by `bar β`. At the diagonal
this is a ring isomorphism. Pullback of an arbitrary global section uses the canonical
integer-unit comparison, inverse to the specified constant-coefficient map.

Source: Stacks, Sites and Sheaves, Tags 00VE, 00WX, 03CE and 00Y0;
Modules on Sites, Tag 03EL
(blueprint: lem-sfb-localized-ring-mate-graph-evaluation).

Proof:
1. The forward Kan adjunction map sends `t` to `t` after the identity-index
   coprojection; its inverse sends the coprojection `(T, φ)` to restriction along
   `φ` after the adjoint map at `T`. Naturality verifies the cocone relations and
   the two inverse identities. Compose with sheafification to compute exactly
   `proEtaleSheafAdjunction`, which also defines upperStar on abelian sheaves.
2. At `T ×_B V`, the projection gives an arrow from the distinguished initial
   index to the identity index. The colimit cocone relation identifies the unit
   with projection restriction. The normalized coprojection and sheafification
   equations of `lem-sfb-proetale-object-inverse-image-restriction` identify this
   with the displayed ring comparison, respecting all ring operations.
3. Direct image evaluates at the fibre product, giving the mate formula.
   Naturality of `bar β` along `(b, U → V)` and the graph's first projection
   give the graph formula; this is sectionwise restriction of
   `def-pur-localized-ringed-site`.
4. Take `T = V`, `U = V/V`, and `b` the identity of the underlying scheme.
   The graph is the diagonal. Its composite with the mate is the component
   of `bar β`, with the identity-object identification. Both factors on the
   right are isomorphisms, giving the asserted ring isomorphism.
5. The additive map associated with `r` sends `1` at `B/B` to `r`.
   Naturality sends it at `V/V` to `R(u)(r)`. Normalized restriction identifies
   its inverse image with that restriction. Restriction commutes with
   sheafification on integer constants. Clause (2) of the restriction lemma
   identifies its inverse with the specified constant-coefficient map. The
   inverse-image monoidal unit is this inverse: it sends the integer unit
   to the pulled-back integer unit, hence agrees on every integer section;
   these locally generate the constant sheaf (Tag 03EL). Composing with `β`
   yields the final formula. The comparison with the underlying abelian
   inverse image is through these same normalized restriction isomorphisms.
-/
theorem proEtaleLocalizedRingMateGraphEvaluation {B : Scheme.{u}} (V : B.ProEt)
    (c : ProEtaleObjectRestrictionComparison V CommRingCat.{u + 1})
    (cA : ProEtaleObjectRestrictionComparison V AddCommGrpCat.{u + 1})
    (R : Sheaf (ProEt.topology B) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology V.left) CommRingCat.{u + 1})
    (β : (proEtaleSheafInverseImage V.hom CommRingCat.{u + 1}).obj R ≅ S) :
    (∀ (T : B.ProEt) (a : R.obj.obj (op T)),
      (c.sheafIso.hom.app R).hom.app (op ((proEtaleBaseChange V.hom).obj T))
          (((proEtaleSheafAdjunction V.hom CommRingCat.{u + 1}).unit.app R).hom.app
            (op T) a) =
        R.obj.map ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤
          V.hom V.prop trivial).counit.app T).op a) ∧
    (∀ (T : B.ProEt) (a : R.obj.obj (op T)),
      (proEtaleLocalizedRingMate V R S β).hom.app (op T) a =
        (proEtaleLocalizedRingIso V c R S β).hom.hom.app
          (op ((proEtaleBaseChange V.hom).obj T))
            (R.obj.map ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤
              V.hom V.prop trivial).counit.app T).op a)) ∧
    (∀ (T : B.ProEt) (a : R.obj.obj (op T)) (U : V.left.ProEt)
      (b : (MorphismProperty.Over.map (f := V.hom) ⊤ V.prop).obj U ⟶ T),
      S.obj.map (proEtaleLocalizationGraph V U T b).op
          ((proEtaleLocalizedRingMate V R S β).hom.app (op T) a) =
        (proEtaleLocalizedRingIso V c R S β).hom.hom.app (op U) (R.obj.map b.op a)) ∧
    ((proEtaleLocalizedRingMate V R S β).hom.app (op V) ≫
        S.obj.map (proEtaleLocalizationGraph V (ProEt.mk (𝟙 V.left)) V
          (proEtaleLocalizationIdentityIso V).hom).op =
      R.obj.map (proEtaleLocalizationIdentityIso V).hom.op ≫
        (proEtaleLocalizedRingIso V c R S β).hom.hom.app
          (op (ProEt.mk (𝟙 V.left)))) ∧
    IsIso ((proEtaleLocalizedRingMate V R S β).hom.app (op V) ≫
      S.obj.map (proEtaleLocalizationGraph V (ProEt.mk (𝟙 V.left)) V
        (proEtaleLocalizationIdentityIso V).hom).op) ∧
    ((proEtaleLocalizedIntegerUnit V cA).hom ≫
        proEtaleConstantInverseImageMap V.hom AddCommGrpCat.{u + 1}
          (AddCommGrpCat.of (ULift.{u + 1} ℤ)) = 𝟙 _) ∧
    (∀ r : R.obj.obj (op (ProEt.mk (𝟙 B))),
      (proEtaleLocalizedPulledSection V c cA R S β r).hom.app
          (op (ProEt.mk (𝟙 V.left)))
            ((toSheafify (ProEt.topology V.left)
              ((Functor.const V.left.ProEtᵒᵖ).obj
                (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
                  (op (ProEt.mk (𝟙 V.left))) (ULift.up 1)) =
        (proEtaleLocalizedRingIso V c R S β).hom.hom.app (op (ProEt.mk (𝟙 V.left)))
          (R.obj.map ((MorphismProperty.Over.mkIdTerminal @WeaklyEtale B).from
            ((MorphismProperty.Over.map (f := V.hom) ⊤ V.prop).obj
              (ProEt.mk (𝟙 V.left)))).op r)) := by
  sorry

end AlgebraicGeometry.Scheme
