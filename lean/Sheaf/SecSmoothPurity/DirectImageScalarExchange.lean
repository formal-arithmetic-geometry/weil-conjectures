/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison
public import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
public import Sheaf.Paper.StratumScalarExtension
public import Sheaf.Paper.FourCorners
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.Paper.PbcActualRingedExchange
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Sheaf.SecSmoothPurity.DirectImageScalarOperations
import Sheaf.AlgebraicGeometry.ProEtaleConstantScalarPullbackCube

/-!
# Scalar extension and direct-image geometric exchange

Source: literature/stacks-project/sites-cohomology.tex, Tag 0E47,
`remark-compose-base-change-horizontal` (blueprint: lem-fix-direct-image-scalar-exchange).

All functors and comparisons below specialize existing canonical constructions to
constant coefficients. No functor, adjunction, tensor comparison or square comparison
is supplied as an arbitrary parameter.
- `directImageScalarExtension` is the universal K-flat scalar extension.
- `directImageScalarPullbackIso` is its canonical tensor/inverse-image comparison.
- `directImageScalarComparison` is the mate defining chi.
- `directImageConstantExchange` is the existing ambient ringed exchange for constants.
- `directImageScalarExchange` is the equality of the two specified composites.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
-- Replaying the categorical transport tactics for unused-tactic linting is expensive.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalar_exchange_of_cube
    {C D E F C' D' E' F' : Type*}
    [Category C] [Category D] [Category E] [Category F]
    [Category C'] [Category D'] [Category E'] [Category F']
    {a : C ⥤ D} {ar : D ⥤ C} {b : C' ⥤ D'} {br : D' ⥤ C'}
    {c : E ⥤ F} {cr : F ⥤ E} {d : E' ⥤ F'} {dr : F' ⥤ E'}
    (aa : a ⊣ ar) (ab : b ⊣ br) (ac : c ⊣ cr) (ad : d ⊣ dr)
    (s : C ⥤ C') (t : D ⥤ D') (v : E ⥤ E') (w : F ⥤ F')
    (g : C ⥤ E) (h : D ⥤ F) (g' : C' ⥤ E') (h' : D' ⥤ F')
    (la : s ⋙ b ⟶ a ⋙ t) (lc : v ⋙ d ⟶ c ⋙ w)
    (lg : s ⋙ g' ⟶ g ⋙ v) (lh : t ⋙ h' ⟶ h ⋙ w)
    (ta : g ⋙ c ⟶ a ⋙ h) (tb : g' ⋙ d ⟶ b ⋙ h')
    (cube : ∀ N : C,
      tb.app (s.obj N) ≫ h'.map (la.app N) ≫ lh.app (a.obj N) =
        d.map (lg.app N) ≫ lc.app (g.obj N) ≫ w.map (ta.app N))
    (M : D) :
    g'.map ((mateEquiv aa ab la).natTrans.app M) ≫
        (mateEquiv ab ad tb).natTrans.app (t.obj M) ≫ dr.map (lh.app M) =
      lg.app (ar.obj M) ≫ v.map ((mateEquiv aa ac ta).natTrans.app M) ≫
        (mateEquiv ac ad lc).natTrans.app (h.obj M) := by
  dsimp only [TwoSquare.natTrans]
  apply (ad.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [show d.map (dr.map (lh.app M)) ≫ ad.counit.app _ =
    ad.counit.app _ ≫ lh.app M from ad.counit.naturality _]
  slice_lhs 2 3 => rw [mateEquiv_counit]
  slice_lhs 1 2 =>
    exact tb.naturality ((mateEquiv aa ab la).app M)
  simp only [Functor.comp_map, Category.assoc]
  slice_lhs 2 3 =>
    rw [← h'.map_comp, mateEquiv_counit, h'.map_comp]
  slice_lhs 3 4 => exact lh.naturality (aa.counit.app M)
  slice_lhs 1 3 => exact cube (ar.obj M)
  slice_rhs 3 4 => exact mateEquiv_counit ac ad (TwoSquare.mk _ _ _ _ lc) (h.obj M)
  slice_rhs 2 3 => exact lc.naturality ((mateEquiv aa ac ta).app M)
  simp only [Functor.comp_map, Category.assoc]
  slice_rhs 3 4 => rw [← w.map_comp, mateEquiv_counit, w.map_comp]
  rfl


namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] directImageConstantAdjunction
  Scheme.completedAdicDerivedChange
  Functor.mapDerivedCategory Functor.rightDerivedFunctor Scheme.proEtaleRingModulePullback
  Scheme.proEtaleConstantRingComparison
  Scheme.proEtaleRingDerivedAdjunction Scheme.proEtaleReductionPullbackIso
  Scheme.proEtaleAmbientRingedPullbackComparison

private theorem scalarComparison_def
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {T V : Scheme.{u}} (f : T ⟶ V) :
    directImageScalarComparison φ f =
      (mateEquiv (directImageConstantAdjunction A f) (directImageConstantAdjunction B f)
        (directImageScalarPullbackIso φ f).hom).natTrans := rfl

private theorem constantExchange_def
    (A : Type u) [CommRing A] {X' X Y' Y : Scheme.{u}}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare h f' f g) :
    directImageConstantExchange A sq =
      (mateEquiv (directImageConstantAdjunction A f) (directImageConstantAdjunction A f')
        (directImageConstantPullbackIso A sq).hom).natTrans := rfl

/-- Scalar extension respects direct-image geometric exchange, naturally in M.
Source: literature/stacks-project/sites-cohomology.tex, Tag 0E47,
`remark-compose-base-change-horizontal` (blueprint: lem-fix-direct-image-scalar-exchange).

Proof:
1. The normalized ordinary inverse-image compositor localizes to the canonical
   geometric compositor. Restriction of scalars commutes with the ordinary square
   on sections; exact localization and the scalar adjunctions give the tensor square.
   Thus proEtaleConstantScalarPullback_cube gives the coefficient/pullback cube as an
   equality of natural transformations, before geometric direct-image mates.
2. The maps chi and Ex are by definition the mates of lambda and the specified
   canonical pullback-square comparison under the actual geometric adjunctions.
3. Apply injectivity of the last geometric Hom equivalence. The four mate-counit
   equations and naturality turn the two direct-image composites into the two paths
   of the pullback cube. Their equality therefore gives the mate identity.
4. Evaluate the pullback cube at each input and specialize the pointwise mate identity at M.
   This proves
   the displayed equality naturally in M with no additional geometric or coefficient
   hypotheses. -/
theorem directImageScalarExchange
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B)
    {X' X Y' Y : Scheme.{u}}
    (h : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : ChosenCartesianSquare h f' f g)
    (M : Scheme.proEtaleDerivedCategory X A) :
    (Scheme.proEtaleConstantRingDerivedPullback B g).map
        ((directImageScalarComparison φ f).app M) ≫
      (directImageConstantExchange B sq).app ((directImageScalarExtension φ X).obj M) ≫
      (directImageConstantPush B f').map ((directImageScalarPullbackIso φ h).hom.app M) =
    (directImageScalarPullbackIso φ g).hom.app ((directImageConstantPush A f).obj M) ≫
      (directImageScalarExtension φ Y').map ((directImageConstantExchange A sq).app M) ≫
      (directImageScalarComparison φ f').app
        ((Scheme.proEtaleConstantRingDerivedPullback A h).obj M) := by
  rw [scalarComparison_def, scalarComparison_def, constantExchange_def, constantExchange_def]
  have e := scalar_exchange_of_cube
    (directImageConstantAdjunction A f) (directImageConstantAdjunction B f)
    (directImageConstantAdjunction A f') (directImageConstantAdjunction B f')
    (directImageScalarExtension φ Y) (directImageScalarExtension φ X)
    (directImageScalarExtension φ Y') (directImageScalarExtension φ X')
    (Scheme.proEtaleConstantRingDerivedPullback A g)
    (Scheme.proEtaleConstantRingDerivedPullback A h)
    (Scheme.proEtaleConstantRingDerivedPullback B g)
    (Scheme.proEtaleConstantRingDerivedPullback B h)
    (directImageScalarPullbackIso φ f).hom (directImageScalarPullbackIso φ f').hom
    (directImageScalarPullbackIso φ g).hom (directImageScalarPullbackIso φ h).hom
    (directImageConstantPullbackIso A sq).hom (directImageConstantPullbackIso B sq).hom
    (fun N ↦ congr_app (Scheme.proEtaleConstantScalarPullback_cube φ sq) N) M
  exact e

end AlgebraicGeometry.ProEtale
