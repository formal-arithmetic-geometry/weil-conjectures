/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.GlobalHomPullbackComparison
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.MixedHomTensorPullbackIso
public import Sheaf.AlgebraicGeometry.MixedGlobalSectionsDirectImageIso
public import Sheaf.AlgebraicGeometry.MixedGlobalExtension
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Sheaf.AlgebraicGeometry.AffineMorphismHomOutOfPerfect

/-! # Scalar-extension comparison for global Hom over arbitrary affine bases
Source: Stacks Project, perfect.tex, Tag 0AA7.
(blueprint: lem-sc-flat-affine-global-hom-comparison).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w wA
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
noncomputable section
namespace AlgebraicGeometry

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]

/-- Evaluation-mate pullback followed by normalized Leray.
Source: Stacks Tags 08I3 and 0B6A. -/
def mixedGlobalHomPullbackComparison
    {S T : Scheme.{u}} (h : T ⟶ S) (P Q : schemeDerivedCategory S) :
    (schemeGlobalDerivedHom S).obj (op P, Q) ⟶
      (schemeGlobalScalarRestriction h).obj
        ((schemeGlobalDerivedHom T).obj
          (op ((derivedPullback h).obj P), (derivedPullback h).obj Q)) :=
  (schemeDerivedGlobalSections S).map
      ((schemeHomPullbackAdjunction h).homEquiv _ _
        (((schemeDerivedTensorHomEquiv T)
          ((derivedPullback h).obj
            ((derivedInternalHom (Opens.grothendieckTopology S) S.sheaf).obj (op P, Q)))
          ((derivedPullback h).obj P) ((derivedPullback h).obj Q)).symm
            ((mixedHomTensorPullbackIso h).inv.app
              ((derivedInternalHom (Opens.grothendieckTopology S) S.sheaf).obj (op P, Q), P) ≫
              (derivedPullback h).map
                ((schemeDerivedTensorHomEquiv S)
                  ((derivedInternalHom (Opens.grothendieckTopology S) S.sheaf).obj (op P, Q))
                  P Q (𝟙 _))))) ≫
    (mixedGlobalSectionsDirectImageIso h).hom.app
      ((derivedInternalHom (Opens.grothendieckTopology T) T.sheaf).obj
        (op ((derivedPullback h).obj P), (derivedPullback h).obj Q))

/-- Transpose the restricted pullback comparison under derived scalar extension.
The scalar-square iso gives its target the Y'-global-ring action.
Source: Stacks Tag 0AA7. -/
def mixedAffineGlobalHomBaseChangeMap {X Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (M N : schemeDerivedCategory X) :
    (mixedGlobalExtension g).obj
        ((schemeGlobalScalarRestriction f).obj ((schemeGlobalDerivedHom X).obj (op M, N))) ⟶
      (schemeGlobalScalarRestriction (pullback.snd f g)).obj
        ((schemeGlobalDerivedHom (pullback f g)).obj
          (op ((derivedPullback (pullback.fst f g)).obj M),
            (derivedPullback (pullback.fst f g)).obj N)) :=
  ((mixedGlobalExtensionAdjunction g).homEquiv _ _).symm
    ((schemeGlobalScalarRestriction f).map
        (mixedGlobalHomPullbackComparison (pullback.fst f g) M N) ≫
      (schemeGlobalScalarSquareIso f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition).hom.app _)

/-- Scalar extension of global RHom commutes with a flat square over affine bases.
Source: Stacks Project, perfect.tex, Tag 0AA7, case (1).
(blueprint: lem-sc-flat-affine-global-hom-comparison).

Proof: identify Y and Y' with spectra of their global rings using their canonical
isomorphisms. Flatness of f makes the square stalkwise Tor independent. For perfect M,
RHom(M,N) is the perfect dual of M tensored with N. Apply Tor-independent tensor base
change and restricted derived global sections. Pullback commutes with the perfect dual.
The affine equivalences identify derived extension of global scalars with pullback;
the extension/restriction adjunction identifies the resulting comparison with the
transpose defined above. The normalized tensorator and Leray units give exactly the
same map after transport back from spectra. This argument is independent of the
localization morphism universes. Empty schemes and M = 0 give the unique zero isomorphism. -/
theorem mixedAffineGlobalHomBaseChangeMap_isIso
    {X Y Y' : Scheme.{u}} [IsAffine Y] [IsAffine Y']
    [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Y) (g : Y' ⟶ Y) [Flat f]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (M N : schemeDerivedQCohCategory X) (hM : Scheme.IsPerfect X M.obj) :
    IsIso (mixedAffineGlobalHomBaseChangeMap f g M.obj N.obj) := by sorry

end AlgebraicGeometry
