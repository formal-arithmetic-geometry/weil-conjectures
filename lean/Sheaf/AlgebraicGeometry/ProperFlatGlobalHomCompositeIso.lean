/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FlatAffineGlobalHomComparison
public import Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.Algebra.Homology.BaseChangeRHomPerfect
import Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage
import Sheaf.AlgebraicGeometry.FlatPrecomposePus

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
            (dualityEquationBaseChangeMap f g a a' adjf adjf' hβ K).hom))) := by sorry

end AlgebraicGeometry
