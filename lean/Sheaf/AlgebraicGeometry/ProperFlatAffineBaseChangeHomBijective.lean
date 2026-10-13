/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.Algebra.Homology.BaseChangeRHomPerfect
import Sheaf.AlgebraicGeometry.AffineMorphismHomOutOfPerfect
import Sheaf.AlgebraicGeometry.FlatPrecomposePus
import Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso
import Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage

/-! # Hom comparison for affine proper flat duality base change

Source: Stacks Project, Tag 0AA8, equation duality-equation-iso and its compatibility proof.
(blueprint: lem-sc-proper-flat-affine-basechange-hom-bijective).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The canonical mate map induces bijections on shifted Hom from the pullback of
any perfect complex. Source: Stacks Project, Tag 0AA8, duality-equation-iso.
(blueprint: lem-sc-proper-flat-affine-basechange-hom-bijective).

Proof: Identify the affine bases with spectra of their global rings. Flatness of f
implies stalkwise Tor independence. The affine Hom-out-of-perfect theorem identifies
RHom on X' from the pullback of M to the pullback of a(K) with RHom_X(M,a(K))
tensored over the base ring with its extension. The global Hom adjunction identifies
this with RHom_Y(Rf_*M,K) tensored with the extension. Apply the proper-support
perfect-direct-image theorem to M and the structure sheaf in degree zero: f is proper,
flat and of finite presentation, so Rf_*M is perfect. Perfect RHom base change is
therefore an isomorphism. The assumed canonical base-change isomorphism at M and the
second global Hom adjunction identify the result with RHom on X' from the pullback
of M to a'(Lg*K). The flat-precomposition compatibility identifies the resulting
isomorphism with Hom of the displayed mate map, rather than an unrelated isomorphism.
Taking cohomology in degree n-m gives the asserted bijection, including its shift
comparisons. Empty schemes and zero perfect complexes give bijections between zero
Hom groups; no boundedness condition on K is used. -/
theorem proper_flat_rightAdjoint_affine_baseChange_hom_bijective
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
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
    (m n : ℤ) :
    Function.Bijective (fun t :
      ((derivedPullback (pullback.fst f g)).obj M.obj)⟦m⟧ ⟶
        ((derivedPullback (pullback.fst f g)).obj (a.obj K).obj)⟦n⟧ ↦
      t ≫ (dualityEquationBaseChangeMap f g a a' adjf adjf' hβ K).hom⟦n⟧') := by
  sorry

end AlgebraicGeometry
