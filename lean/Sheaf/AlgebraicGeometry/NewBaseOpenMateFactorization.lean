/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H4
-/
module

public import Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap
public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Mathlib.CategoryTheory.Comma.Arrow


import Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded
import Sheaf.AlgebraicGeometry.DerivedPullbackComposition

/-! # Horizontal factorization at a new-base open

Source: Stacks Project, duality.tex, Remark 48.6.1 (Tag 0E9S).
(blueprint: lem-sc-new-base-open-mate-factorization).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Horizontal pasting compares the outer mate with the composite of the
restricted first mate and the actual canonical open-square mate. Only qcqs hypotheses
on the morphism are needed. No invertibility
of either mate, including the open-square mate, is used in this statement.
Source: Stacks Project, duality.tex, Tag 0ATR; Tag 0E9S; Cohomology, Tag 0ATM.
(blueprint: lem-sc-new-base-open-mate-factorization)

Proof: The projection identities for q identify the open subscheme with the
pullback of f' along W -> Y'. Exact restriction is derived pullback along the
open inclusion. Compose this canonical comparison with derived pullback composition
and q followed by the first projection to obtain a canonical delta_0. For any
supplied natural isomorphism delta with the stated endpoints, delta followed by
delta_0 inverse is a natural automorphism of restriction. Naturality at the first
mate shows that replacing delta_0 by delta only changes the source comparison
by this automorphism; it does not change the validity of the arrow comparison.
The two pullback squares paste horizontally. The projection identities for r
identify their outer rectangle with the pullback of f along W -> Y; monicity
of W -> Y' supplies the second projection equality. Pullback composition
therefore identifies the sources of the two displayed arrows. Direct-image
composition and uniqueness of right adjoints identify the right adjoint d of
the iterated square with the transported c of the outer square; pullback
composition on the base identifies their inputs. These give the target comparison.
Expand each mate into pullback of the right-adjoint image of the unit, pullback
of the inverse conjugate of ordinary base change, and the pullback counit.
Naturality slides the first inverse conjugate past the second unit. The composite
units and counits are the units and counits of the composite adjunctions; the
triangle identities cancel the intervening counit-unit pair. Ordinary base change
pastes under the same composition comparisons (Tag 0ATM); taking conjugates
reverses their order, and taking inverses restores the order in the displayed
composite. Consequently the composite is the outer mate under the two endpoint
isomorphisms. Apply Arrow.isoMk to this commuting square. This computation never
inverts a mate: only the ordinary base-change conjugates are inverted. Empty opens
and zero objects require no separate assumption.
-/
theorem newBase_open_mate_factorization
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y Y' : Scheme.{u}}
    [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Y'] [QuasiSeparatedSpace Y']
    (g : Y' ⟶ Y) (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (a' : schemeDerivedQCohCategory Y' ⥤ schemeDerivedQCohCategory (pullback f g))
    (adjf : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f) (fun E ↦
        (@schemeDerivedDirectImage_qcqs_hasRightAdjoint X Y
          (QuasiCompact.compactSpace_of_compactSpace f)
          (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _ f _ _).fst E.obj E.property) ⊣ a)
    (adjf' : (schemeDerivedQCohProperty Y').lift
      ((schemeDerivedQCohProperty (pullback f g)).ι ⋙
        schemeDerivedDirectImage (pullback.snd f g)) (fun E ↦
        (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
          (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
          (pullback.snd f g) _ _).fst E.obj E.property) ⊣ a')
    (hβ : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition E.obj))
    (K : schemeDerivedQCohCategory Y)
    (W : Y'.Opens) [IsAffine W.toScheme]
    (c : schemeDerivedQCohCategory W.toScheme ⥤
      schemeDerivedQCohCategory (pullback f (W.ι ≫ g)))
    (adjc : (schemeDerivedQCohProperty W.toScheme).lift
      ((schemeDerivedQCohProperty (pullback f (W.ι ≫ g))).ι ⋙
        schemeDerivedDirectImage (pullback.snd f (W.ι ≫ g))) (fun E ↦
        (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
          (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f (W.ι ≫ g))) _ _ _ _
          (pullback.snd f (W.ι ≫ g)) _ _).fst E.obj E.property) ⊣ c)
    (hβW : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f (W.ι ≫ g)) (W.ι ≫ g)
        (pullback.fst f (W.ι ≫ g)) pullback.condition E.obj))
    (r : ((pullback.snd f g) ⁻¹ᵁ W).toScheme ⟶ pullback f (W.ι ≫ g))
    [IsIso r]
    (hr₁ : r ≫ pullback.fst f (W.ι ≫ g) =
      ((pullback.snd f g) ⁻¹ᵁ W).ι ≫ pullback.fst f g)
    (hr₂ : r ≫ pullback.snd f (W.ι ≫ g) ≫ W.ι =
      ((pullback.snd f g) ⁻¹ᵁ W).ι ≫ pullback.snd f g)
    (d : schemeDerivedQCohCategory W.toScheme ⥤
      schemeDerivedQCohCategory (pullback (pullback.snd f g) W.ι))
    (adjd : (schemeDerivedQCohProperty W.toScheme).lift
      ((schemeDerivedQCohProperty (pullback (pullback.snd f g) W.ι)).ι ⋙
        schemeDerivedDirectImage (pullback.snd (pullback.snd f g) W.ι)) (fun E ↦
        (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
          (quasiSeparatedSpace_of_quasiSeparated (pullback.snd (pullback.snd f g) W.ι))
          _ _ _ _ (pullback.snd (pullback.snd f g) W.ι) _ _).fst E.obj E.property) ⊣ d)
    (hβO : ∀ E : schemeDerivedQCohCategory (pullback f g),
      IsIso (schemeDerivedBaseChangeMap (pullback.snd f g)
        (pullback.snd (pullback.snd f g) W.ι) W.ι
        (pullback.fst (pullback.snd f g) W.ι) pullback.condition E.obj))
    (q : ((pullback.snd f g) ⁻¹ᵁ W).toScheme ⟶ pullback (pullback.snd f g) W.ι)
    [IsIso q]
    (hq₁ : q ≫ pullback.fst (pullback.snd f g) W.ι = ((pullback.snd f g) ⁻¹ᵁ W).ι)
    (hq₂ : q ≫ pullback.snd (pullback.snd f g) W.ι = (pullback.snd f g) ∣_ W)
    (δ : (schemeOpenRestriction (pullback f g) ((pullback.snd f g) ⁻¹ᵁ W)).mapDerivedCategory ≅
      derivedPullback (pullback.fst (pullback.snd f g) W.ι) ⋙ derivedPullback q) :
      Nonempty (Arrow.mk
        (((schemeOpenRestriction (pullback f g) ((pullback.snd f g) ⁻¹ᵁ W)).mapDerivedCategory.map
          ((schemeDerivedQCohProperty (pullback f g)).ι.map
            (@dualityEquationBaseChangeMap _ X Y Y'
              (QuasiCompact.compactSpace_of_compactSpace f)
              (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _
              f g a a' adjf adjf' hβ K))) ≫
        δ.hom.app _ ≫ (derivedPullback q).map
          ((schemeDerivedQCohProperty (pullback (pullback.snd f g) W.ι)).ι.map
            (@dualityEquationBaseChangeMap _ (pullback f g) Y' W.toScheme
              (QuasiCompact.compactSpace_of_compactSpace (pullback.snd f g))
              (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
              (pullback.snd f g) W.ι a' d adjf' adjd hβO
              (((schemeDerivedQCohProperty Y').lift
                ((schemeDerivedQCohProperty Y).ι ⋙ derivedPullback g)
                (fun E ↦ (derivedPullback_tensor_preserve_QCoh g).1
                  E.obj E.property)).obj K)))) ≅
        Arrow.mk ((derivedPullback r).map
          ((schemeDerivedQCohProperty (pullback f (W.ι ≫ g))).ι.map
            (@dualityEquationBaseChangeMap _ X Y W.toScheme
              (QuasiCompact.compactSpace_of_compactSpace f)
              (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _
              f (W.ι ≫ g) a c adjf adjc hβW K)))) := by sorry

end AlgebraicGeometry
