/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FlatAffineGlobalHomComparison
public import Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.ProperFlatImageGlobalHomBaseChangeIso
import Sheaf.AlgebraicGeometry.MixedGlobalHomBaseChangeCounitTransport
import Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso

/-! # The composite global Hom comparison through the right adjoint
Source: Stacks Project, duality.tex, Tag 0AA8, equation duality-equation-iso.
(blueprint: lem-sc-proper-flat-global-hom-composite-isIso).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w wA
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

-- The counit equation for the inverse conjugate, independent of derived Hom.
private theorem composite_mate_counit
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

/-- The scalar-extended pullback comparison followed by global Hom of the mate is
invertible. This asserts invertibility of the composite, before cancelling its first
factor; it does not assert that the mate, or global Hom of the mate, is invertible.
Source: Stacks Project, duality.tex, Tag 0AA8, equation duality-equation-iso and the
final compatibility diagram.
(blueprint: lem-sc-proper-flat-global-hom-composite-isIso).

Proof: Apply proper-support perfect direct image with the structure sheaf in degree
zero. Flatness makes that sheaf base-flat; finite presentation makes it finitely
presented and properness gives proper support. Its tensor with M is M, so Rf_*M is
perfect. On the affine base, identify the derived scalar extension of RHom(Rf_*M,K)
with RHom(Lg*Rf_*M,Lg*K) by perfect RHom base change. Precede this with scalar
extension of the counit-induced global Hom adjunction for f. Follow it with Hom of
the assumed inverse of beta at M, then with the inverse global Hom adjunction for
f'. Every factor is invertible. The flat-precomposition identity says that the
transpose of this composite is the transpose of the map displayed here. To check
it with independent localization universes, compute both Leray comparisons using
their derived-unit equations and the tensorator on K-flat representatives; the
same evaluation-mate and triangle-identity calculation applies. The derived
extension/restriction Hom equivalence is injective, giving equality of the two
maps before cancelling any factor. Thus the displayed composite is invertible.
No boundedness of K or flatness of g is required; zero M and empty schemes are valid. -/
theorem properFlatGlobalHomComposite_isIso
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]
    {X Y Y' : Scheme.{u}} [IsAffine Y] [IsAffine Y']
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace Y'] [QuasiSeparatedSpace Y']
    (g : Y' ⟶ Y) (f : X ⟶ Y)
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (a' : schemeDerivedQCohCategory Y' ⥤
      schemeDerivedQCohCategory (pullback f g))
    (adjf : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
      (fun E ↦ (schemeDerivedDirectImage_qcqs_hasRightAdjoint X Y f).fst E.obj E.property) ⊣ a)
    (adjf' : (schemeDerivedQCohProperty Y').lift
      ((schemeDerivedQCohProperty (pullback f g)).ι ⋙
        schemeDerivedDirectImage (pullback.snd f g))
      (fun E ↦ (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
        (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
        (pullback.snd f g) _ _).fst E.obj E.property) ⊣ a')
    (hβ : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g
        (pullback.fst f g) pullback.condition E.obj))
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K : schemeDerivedQCohCategory Y)
    (M : schemeDerivedQCohCategory X) (hM : Scheme.IsPerfect X M.obj)
    : IsIso (mixedAffineGlobalHomBaseChangeMap f g M.obj (a.obj K).obj ≫
      (schemeGlobalScalarRestriction (pullback.snd f g)).map
        ((schemeGlobalDerivedHom (pullback f g)).map
          (X := (op ((derivedPullback (pullback.fst f g)).obj M.obj),
            (derivedPullback (pullback.fst f g)).obj (a.obj K).obj))
          (Y := (op ((derivedPullback (pullback.fst f g)).obj M.obj),
            (a'.obj (((schemeDerivedQCohProperty Y').lift
              ((schemeDerivedQCohProperty Y).ι ⋙ derivedPullback g)
              (fun E ↦ (derivedPullback_tensor_preserve_QCoh g).1
                E.obj E.property)).obj K)).obj))
          ((𝟙 ((derivedPullback (pullback.fst f g)).obj M.obj)).op,
            (dualityEquationBaseChangeMap f g a a' adjf adjf' hβ K).hom))) := by
  classical
  let Lg := (schemeDerivedQCohProperty Y').lift
    ((schemeDerivedQCohProperty Y).ι ⋙ derivedPullback g)
    (fun E ↦ (derivedPullback_tensor_preserve_QCoh g).1 E.obj E.property)
  let LgX := (schemeDerivedQCohProperty (pullback f g)).lift
    ((schemeDerivedQCohProperty X).ι ⋙ derivedPullback (pullback.fst f g))
    (fun E ↦ (derivedPullback_tensor_preserve_QCoh (pullback.fst f g)).1
      E.obj E.property)
  let c := (dualityEquationBaseChangeMap f g a a' adjf adjf' hβ K).hom
  let s := (schemeGlobalDerivedHom (pullback f g)).map
    (X := (op ((derivedPullback (pullback.fst f g)).obj M.obj),
      (derivedPullback (pullback.fst f g)).obj (a.obj K).obj))
    (Y := (op ((derivedPullback (pullback.fst f g)).obj M.obj),
      (a'.obj (Lg.obj K)).obj)) ((𝟙 _).op, c)
  let t := (schemeGlobalScalarRestriction (pullback.snd f g)).map s
  let d := mixedGlobalHomAdjunctionMap f a adjf M K
  let d' := @mixedGlobalHomAdjunctionMap _ _ (pullback f g) Y' _
    (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _
    (pullback.snd f g) a' adjf' (LgX.obj M) (Lg.obj K)
  let q := mixedGlobalExtensionAdjunction g
  let b := (q.homEquiv _ _).symm
    (mixedGlobalHomPullbackComparison g ((schemeDerivedDirectImage f).obj M.obj) K.obj)
  have hb : IsIso b := properFlatImage_globalHomBaseChange_isIso f g M hM K
  have hd : IsIso d := mixedGlobalHomAdjunctionMap_isIso f a adjf M K
  have hd' : IsIso d' := @mixedGlobalHomAdjunctionMap_isIso _ _ (pullback f g) Y' _
    (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _
    (pullback.snd f g) a' adjf' (LgX.obj M) (Lg.obj K)
  have := hβ M
  let j := (schemeGlobalDerivedHom Y').map
    (X := (op ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj M.obj)),
      (derivedPullback g).obj K.obj))
    (Y := (op ((schemeDerivedDirectImage (pullback.snd f g)).obj
      ((derivedPullback (pullback.fst f g)).obj M.obj)), (derivedPullback g).obj K.obj))
    ((inv (schemeDerivedBaseChangeMap f (pullback.snd f g) g
      (pullback.fst f g) pullback.condition M.obj)).op, 𝟙 _)
  have hj : IsIso j := by
    have : IsIso
        ((inv (schemeDerivedBaseChangeMap f (pullback.snd f g) g
          (pullback.fst f g) pullback.condition M.obj)).op,
            𝟙 ((derivedPullback g).obj K.obj)) :=
      (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
    dsimp only [j]
    infer_instance
  have hc : schemeDerivedBaseChangeMap f (pullback.snd f g) g
        (pullback.fst f g) pullback.condition (a.obj K).obj ≫
      (schemeDerivedDirectImage (pullback.snd f g)).map c ≫
        (adjf'.counit.app (Lg.obj K)).hom =
      (derivedPullback g).map (adjf.counit.app K).hom := by
    dsimp only [c, Lg]
    unfold dualityEquationBaseChangeMap
    extract_lets PX PY PY' PX' LLg LLgX Rg RgX Rf Rf' adjg adjgX β
    exact congrArg (fun z ↦ z.hom)
      (composite_mate_counit adjf adjf' adjg adjgX β K)
  have ht := mixedGlobalHom_baseChange_counit_transport f g M.obj (a.obj K).obj
    (a'.obj (Lg.obj K)).obj K.obj c (adjf.counit.app K).hom
    (adjf'.counit.app (Lg.obj K)).hom hc
  let α := mixedAffineGlobalHomBaseChangeMap f g M.obj (a.obj K).obj
  have hfactor : α ≫ t ≫ d' = (mixedGlobalExtension g).map d ≫ b ≫ j := by
    apply (q.homEquiv _ _).injective
    rw [q.homEquiv_naturality_left]
    simp only [q.homEquiv_naturality_right, Functor.map_comp]
    dsimp only [α, mixedAffineGlobalHomBaseChangeMap, b, q]
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    have hsq := (schemeGlobalScalarSquareIso f (pullback.snd f g) g
      (pullback.fst f g) pullback.condition).hom.naturality s
    dsimp only [Functor.comp_map, s] at hsq
    simp only [Functor.map_comp, Category.assoc] at ht
    rw [reassoc_of% hsq] at ht
    simpa only [d, d', t, s, j, Lg, LgX, mixedGlobalHomAdjunctionMap,
      ObjectProperty.lift, ObjectProperty.ι, inducedFunctor, Functor.comp_obj,
      Functor.map_comp, Category.assoc] using ht
  have hcomp : IsIso (α ≫ t ≫ d') := by
    rw [hfactor]
    infer_instance
  have : IsIso (α ≫ t) := by
    have : IsIso ((α ≫ t) ≫ d') := by simpa only [Category.assoc] using hcomp
    exact IsIso.of_isIso_comp_right _ d'
  exact this


end AlgebraicGeometry
