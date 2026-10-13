/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap
public import Sheaf.AlgebraicGeometry.GlobalHomPullbackComparison
public import Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso
import Sheaf.AlgebraicGeometry.GlobalHomBaseChangeCounitTransport

/-!
# Flat precomposition transformation for right-adjoint base change

Source: Stacks Project, `duality.tex`, Tag 0AA8 (Lemma 48.6.2),
case (1), final compatibility sentence
(blueprint: lem-sc-flat-precompose-pus).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe uMain wMain
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry

-- The counit equation for the inverse conjugate, independent of derived Hom.
private theorem mate_counit
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {F : C ⥤ D} {A : D ⥤ C} {F' : C' ⥤ D'} {A' : D' ⥤ C'}
    {L : D ⥤ D'} {R : D' ⥤ D} {L' : C ⥤ C'} {R' : C' ⥤ C}
    (p : F ⊣ A) (p' : F' ⊣ A') (q : L ⊣ R) (q' : L' ⊣ R')
    (β : F ⋙ L ⟶ L' ⋙ F') [IsIso β] (K : D) :
    β.app (A.obj K) ≫
      F'.map (L'.map (A.map (q.unit.app K)) ≫
        L'.map (inv ((conjugateEquiv (q'.comp p') (p.comp q) β).app (L.obj K))) ≫
          q'.counit.app (A'.obj (L.obj K))) ≫ p'.counit.app (L.obj K) =
      L.map (p.counit.app K) := by
  let θ := conjugateEquiv (q'.comp p') (p.comp q) β
  have h := conjugateEquiv_counit (q'.comp p') (p.comp q) β (L.obj K)
  simp only [Adjunction.comp_counit_app, Functor.comp_map] at h
  change L.map (F.map (θ.app (L.obj K))) ≫
    (L.map (p.counit.app (R.obj (L.obj K))) ≫ q.counit.app (L.obj K)) =
    β.app (R'.obj (A'.obj (L.obj K))) ≫
      (F'.map (q'.counit.app (A'.obj (L.obj K))) ≫ p'.counit.app (L.obj K)) at h
  have hn {U V : C} (t : U ⟶ V) :
      β.app U ≫ F'.map (L'.map t) = L.map (F.map t) ≫ β.app V :=
    (β.naturality t).symm
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn (A.map (q.unit.app K)),
    reassoc_of% hn (inv (θ.app (L.obj K))), ← h]
  simp only [Functor.map_inv, IsIso.inv_hom_id_assoc]
  rw [← L.map_comp_assoc]
  have hp : F.map (A.map (q.unit.app K)) ≫ p.counit.app (R.obj (L.obj K)) =
      p.counit.app K ≫ q.unit.app K := p.counit.naturality (q.unit.app K)
  have hq : L.map (q.unit.app K) ≫ q.counit.app (L.obj K) = 𝟙 _ :=
    q.left_triangle_components K
  rw [hp, L.map_comp, Category.assoc, hq, Category.comp_id]

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
  have hc : schemeDerivedBaseChangeMap f (pullback.snd f g) g
        (pullback.fst f g) pullback.condition (a.obj K).obj ≫
      (schemeDerivedDirectImage (pullback.snd f g)).map
        (dualityEquationBaseChangeMap f g a a' adjf adjf' hβ K).hom ≫
          (adjf'.counit.app (((schemeDerivedQCohProperty Y').lift
            ((schemeDerivedQCohProperty Y).ι ⋙ derivedPullback g)
            (fun E ↦ (derivedPullback_tensor_preserve_QCoh g).1
              E.obj E.property)).obj K)).hom =
      (derivedPullback g).map (adjf.counit.app K).hom := by
    unfold dualityEquationBaseChangeMap
    extract_lets PX PY PY' PX' Lg LgX Rg RgX Rf Rf' adjg adjgX β
    exact congrArg (fun z ↦ z.hom) (mate_counit adjf adjf' adjg adjgX β K)
  have := hβ M
  have ht := schemeGlobalHom_baseChange_counit_transport f g M.obj (a.obj K).obj
    (a'.obj (((schemeDerivedQCohProperty Y').lift
      ((schemeDerivedQCohProperty Y).ι ⋙ derivedPullback g)
      (fun E ↦ (derivedPullback_tensor_preserve_QCoh g).1
        E.obj E.property)).obj K)).obj K.obj
    (dualityEquationBaseChangeMap f g a a' adjf adjf' hβ K).hom
    (adjf.counit.app K).hom
    (adjf'.counit.app (((schemeDerivedQCohProperty Y').lift
      ((schemeDerivedQCohProperty Y).ι ⋙ derivedPullback g)
      (fun E ↦ (derivedPullback_tensor_preserve_QCoh g).1
        E.obj E.property)).obj K)).hom hc
  let e := @schemeGlobalHomAdjunctionIso _ _ (pullback f g) Y' _
    (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _
    (pullback.snd f g) a' adjf'
    (((schemeDerivedQCohProperty (pullback f g)).lift
      ((schemeDerivedQCohProperty X).ι ⋙ derivedPullback (pullback.fst f g))
      (fun E ↦ (derivedPullback_tensor_preserve_QCoh (pullback.fst f g)).1
        E.obj E.property)).obj M)
    (((schemeDerivedQCohProperty Y').lift
      ((schemeDerivedQCohProperty Y).ι ⋙ derivedPullback g)
      (fun E ↦ (derivedPullback_tensor_preserve_QCoh g).1
        E.obj E.property)).obj K)
  change _ = _ ≫ _ ≫ _ ≫ (schemeGlobalScalarRestriction g).map e.inv
  apply (cancel_mono ((schemeGlobalScalarRestriction g).map e.hom)).1
  simp only [Category.assoc]
  rw [← Functor.map_comp, e.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id]
  simpa only [e, schemeGlobalHomAdjunctionIso, asIso_hom,
    schemeGlobalHomAdjunctionMap, Category.assoc, ObjectProperty.lift_obj_obj, Functor.comp_obj,
    ObjectProperty.ι_obj] using ht

end AlgebraicGeometry
