/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap
import Sheaf.AlgebraicGeometry.GlobalHomPullbackComparison
import Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso

/-!
# Flat precomposition transformation for right-adjoint base change

Source: Stacks Project, `duality.tex`, Tag 0AA8 (Lemma 48.6.2),
case (1), final compatibility sentence
(blueprint: lem-sc-flat-precompose-pus).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe uMain wMain
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry

/-- Canonical pullback comparison followed by Hom of c equals the right-adjoint
Hom adjunction, pullback comparison on Y, Hom of beta inverse, and inverse Hom
adjunction on X'. Both sides are the A-linear transposes of the stated A'-linear
maps from RHom_X(M,aK) tensor_A^L A'. Scalar restriction along f supplies the A-action;
the canonical scalar square comparison identifies both targets. Equality of these
transposes is equivalent to equality of the original maps by the derived
extension/restriction adjunction; it does not discard any A'-linear information.
Source: Stacks Project, duality.tex, Tag 0AA8, lemma-more-base-change, final
compatibility paragraph (blueprint: lem-sc-flat-precompose-pus).

Proof:
1. Expand c of def-sc-duality-equation-base-change-map as pullback of the unit,
inverse conjugate of beta, then the pullback counit. Use the counit-induced global
Hom adjunction of lem-pc-global-hom-adjunction and the pullback/direct-image Hom
adjunction of lem-pc-global-hom-pullback-adjunction to transport this expansion.
2. The triangle identities and the definition of the conjugate identify the middle
factors with the pullback comparison followed by Hom of c. The canonical Leray
and scalar composition comparisons carry all maps into D(A).
3. The algebraic RHom base-change map is defined as the A'-linear extension of the
pullback-induced map. Its transpose is precisely the pullback comparison on Y.
Transporting through the first Hom adjunction, Hom of beta inverse, and the second
Hom adjunction gives the same map. The scalar-extension adjunction then gives the
equality in D(A') stated by the node. -/
theorem flat_precompose_pus
    [∀ Z : Scheme.{uMain},
      HasDerivedCategory.{wMain} (SheafOfModules.{uMain} (moduleRings Z.toRingedSpace))]
    [∀ (R : Type uMain) [Ring R],
      HasDerivedCategory.{wMain} (ModuleCat.{uMain} R)]
    {X Y Y' : Scheme.{uMain}} [IsAffine Y] [IsAffine Y']
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace Y'] [QuasiSeparatedSpace Y']
    (f : X ⟶ Y) (g : Y' ⟶ Y)
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (a' : schemeDerivedQCohCategory Y' ⥤
      schemeDerivedQCohCategory (pullback f g))
    (adjf : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
      (fun E ↦ (schemeDerivedDirectImage_qcqs_hasRightAdjoint X Y f).fst
        E.obj E.property) ⊣ a)
    (adjf' : (schemeDerivedQCohProperty Y').lift
      ((schemeDerivedQCohProperty (pullback f g)).ι ⋙
        schemeDerivedDirectImage (pullback.snd f g))
      (fun E ↦ (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
        (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
        (pullback.snd f g) _ _).fst E.obj E.property) ⊣ a')
    (hβ : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g
        (pullback.fst f g) pullback.condition E.obj))
    (M : schemeDerivedQCohCategory X) (K : schemeDerivedQCohCategory Y) :
    (schemeGlobalScalarRestriction f).map
      (schemeGlobalDerivedHom_pullback_comparison (pullback.fst f g) M.obj (a.obj K).obj ≫
        (schemeGlobalScalarRestriction (pullback.fst f g)).map
          ((schemeGlobalDerivedHom (pullback f g)).map
            (X := (op ((derivedPullback (pullback.fst f g)).obj M.obj),
              (derivedPullback (pullback.fst f g)).obj (a.obj K).obj))
            (Y := (op ((derivedPullback (pullback.fst f g)).obj M.obj),
              (a'.obj (((schemeDerivedQCohProperty Y').lift
                ((schemeDerivedQCohProperty Y).ι ⋙ derivedPullback g)
                (fun E ↦ (derivedPullback_tensor_preserve_QCoh g).1
                  E.obj E.property)).obj K)).obj))
            ((𝟙 ((derivedPullback (pullback.fst f g)).obj M.obj)).op,
              (dualityEquationBaseChangeMap f g a a' adjf adjf' hβ K).hom))) ≫
      (schemeGlobalScalarSquareIso f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition).hom.app
          ((schemeGlobalDerivedHom (pullback f g)).obj
            (op ((derivedPullback (pullback.fst f g)).obj M.obj),
              (a'.obj (((schemeDerivedQCohProperty Y').lift
                ((schemeDerivedQCohProperty Y).ι ⋙ derivedPullback g)
                (fun E ↦ (derivedPullback_tensor_preserve_QCoh g).1
                  E.obj E.property)).obj K)).obj)) =
    (schemeGlobalHomAdjunctionIso f a adjf M K).hom ≫
      schemeGlobalDerivedHom_pullback_comparison g ((schemeDerivedDirectImage f).obj M.obj)
        K.obj ≫
      (schemeGlobalScalarRestriction g).map
        ((schemeGlobalDerivedHom Y').map
          (X := (op ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj M.obj)),
            (derivedPullback g).obj K.obj))
          (Y := (op ((schemeDerivedDirectImage (pullback.snd f g)).obj
            ((derivedPullback (pullback.fst f g)).obj M.obj)), (derivedPullback g).obj K.obj))
          ((inv (schemeDerivedBaseChangeMap f (pullback.snd f g) g
            (pullback.fst f g) pullback.condition M.obj)).op, 𝟙 _)) ≫
      (schemeGlobalScalarRestriction g).map
        (@schemeGlobalHomAdjunctionIso _ _ (pullback f g) Y' _
          (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _
          (pullback.snd f g) a' adjf'
          (((schemeDerivedQCohProperty (pullback f g)).lift
            ((schemeDerivedQCohProperty X).ι ⋙ derivedPullback (pullback.fst f g))
            (fun E ↦ (derivedPullback_tensor_preserve_QCoh (pullback.fst f g)).1
              E.obj E.property)).obj M)
          (((schemeDerivedQCohProperty Y').lift
            ((schemeDerivedQCohProperty Y).ι ⋙ derivedPullback g)
            (fun E ↦ (derivedPullback_tensor_preserve_QCoh g).1
              E.obj E.property)).obj K)).inv := by
  sorry

end AlgebraicGeometry
