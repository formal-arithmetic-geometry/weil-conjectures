/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FlatAffineGlobalHomComparison
public import Sheaf.AlgebraicGeometry.MixedGlobalHomAdjunctionIso

/-!
# Transport of global Hom comparisons across a counit square

Source: Stacks Project, Tag 0AA8, the commutative diagrams in the final part of the proof.
(blueprint: lem-sc-mixed-global-hom-base-change-counit-transport).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w wA
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry

/-- The pullback and direct-image global Hom comparisons transport a commuting
counit square. This assertion concerns arbitrary derived objects and morphisms;
no right adjoints on quasi-coherent categories or right-adjoint base-change map
are used.

Source: Stacks Project, Tag 0AA8, the final commutative diagrams; the comparisons
are the evaluation mates of Tags 08I3 and 0B6I.
(blueprint: lem-sc-mixed-global-hom-base-change-counit-transport).

Proof:
1. Expand the pullback comparison and direct-image comparison as evaluation mates.
Transpose under the pinned tensor-Hom bijections and pullback/direct-image
adjunctions. Their naturality shows that the square comparing pullback followed
by direct image with direct image followed by pullback commutes, with the
canonical base-change maps in the two Hom entries. The tensor comparisons and
Leray comparisons are the canonical ones, so their composition identifications
agree with the scalar square isomorphism.
2. Postcompose the square with Hom of the morphism t and then Hom of e'.
Naturality in the second Hom entry replaces this by Hom of Rf'(t) followed by e'.
Use the assumed counit square to replace beta_N followed by these maps by Lg*(e).
Naturality of the pullback comparison in its second entry now moves e to the
source, giving the comparison applied to (Rf*M,K).
3. The remaining map in the first Hom entry is beta_M. Since beta_M is invertible,
cancel it contravariantly; its inverse gives exactly the final displayed factor.
The tensorators are normalized by their K-flat equations and Leray comparisons by
their derived-unit equations, so the computation holds with independent sheaf and
module localization universes. All steps hold before extension of scalars and give the identity
of transposes. -/
theorem mixedGlobalHom_baseChange_counit_transport
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]
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
      (mixedGlobalHomPullbackComparison (pullback.fst f g) M N ≫
        (schemeGlobalScalarRestriction (pullback.fst f g)).map
          ((schemeGlobalDerivedHom (pullback f g)).map ((𝟙 _).op, t))) ≫
      (schemeGlobalScalarSquareIso f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition).hom.app
          ((schemeGlobalDerivedHom (pullback f g)).obj
            (op ((derivedPullback (pullback.fst f g)).obj M), E)) ≫
      (schemeGlobalScalarRestriction g).map
        (mixedGlobalHomDirectImageMap (pullback.snd f g)
            ((derivedPullback (pullback.fst f g)).obj M) E ≫
          (schemeGlobalDerivedHom Y').map ((𝟙 _).op, e')) =
    (mixedGlobalHomDirectImageMap f M N ≫
        (schemeGlobalDerivedHom Y).map ((𝟙 _).op, e)) ≫
      mixedGlobalHomPullbackComparison g
        ((schemeDerivedDirectImage f).obj M) K ≫
      (schemeGlobalScalarRestriction g).map
        ((schemeGlobalDerivedHom Y').map
          (X := (op ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj M)),
            (derivedPullback g).obj K))
          (Y := (op ((schemeDerivedDirectImage (pullback.snd f g)).obj
            ((derivedPullback (pullback.fst f g)).obj M)), (derivedPullback g).obj K))
          ((inv (schemeDerivedBaseChangeMap f (pullback.snd f g) g
            (pullback.fst f g) pullback.condition M)).op, 𝟙 _)) := by sorry

end AlgebraicGeometry
