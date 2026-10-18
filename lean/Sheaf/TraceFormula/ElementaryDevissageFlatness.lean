/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Sheaf.TraceFormula.ElementaryModuleDevissage
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor

import Sheaf.AlgebraicGeometry.AffineCoverModuleTensorFlatCriterion
import Sheaf.TraceFormula.EtaleLocalRingFlatness
import Sheaf.AlgebraicGeometry.RelativeFlatnessSourceCover
import WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChange
import WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import Sheaf.AlgebraicGeometry.FiniteSingletonFibreLocalization

/-! # Relative flatness across elementary module dévissage

Source: Stacks Project, flat.tex, Tag 057U, lemma-devissage-flat
(blueprint: lem-trf-elementary-devissage-flatness).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Relative flatness near the three marked points of elementary module dévissage is
 equivalent; separately, relative flatness of their stalks is equivalent. The base actions
 on stalks are the canonical structure stalk maps. The marked-point equalities identify
 the base points with `s = f x` and `s' = h (π z')`.

Source: Stacks Project, flat.tex, Tag 057U, lemma-devissage-flat
(blueprint: lem-trf-elementary-devissage-flatness).

Proof:
1. Put H = g*F ≅ i_*G. Pullback preserves quasi-coherence
   (lem-weil-pbc-module-pullback-quasi-coherent). At every point of X', the etale
   local-ring comparison (lem-trf-etale-local-ring-flatness, Tag 05BA) identifies
   flatness of H over S with flatness over S'.
2. The source-cover criterion (lem-trf-relative-flatness-source-cover) applied to
   the flat map g compares F at g(u) with H at u. Pull back a flat neighbourhood
   along g in one direction. In the other direction its image is open, by
   lem-weil-pbc-etale-morphism-open-map, and the same pointwise criterion descends
   flatness to this image. This compares neighbourhoods of x and x'.
3. The closed-pushforward stalk comparison (lem-weil-pbc-closed-pushforward-stalks)
   identifies H at i(z) with G at z linearly over S', since i is over S'. Outside
   the closed image the stalks are zero and hence flat. Every open neighbourhood
   of z' is the inverse image of an open neighbourhood of x' under the closed
   embedding. Thus H near x' and G near z' are equivalent flatness conditions.
4. Specialize lem-pc-affine-cover-module-tensor-flat-criterion to identity base
   change and a one-member affine cover. Cancel A tensor_A A and A tensor_A N
   by multiplication. On an affine scheme over affine S', relative flatness is
   exactly flatness of global sections over the global sections of S'.
5. Finite π is affine, and π_*G is quasi-coherent by clause (1) of
   lem-weil-pbc-affine-pushforward-base-change. The singleton-fibre neighbourhood
   comparison (lem-trf-finite-singleton-fibre-localization) shrinks a neighbourhood
   of y' to have inverse image inside any prescribed neighbourhood of z'. Shrink
   further to an affine open. Its inverse image is affine, and the sections of G
   there are exactly the sections of π_*G with the same base action. Step 4 proves
   both directions of their neighbourhood equivalence.
6. At the marked stalks, Step 2 compares F_x with H_x' over S; Step 1 changes to
   S'; Step 3 compares with G_z'. The canonical finite singleton-fibre stalk map
   (lem-trf-finite-singleton-fibre-localization, Tag 05B8) identifies (π_*G)_y'
   with G_z', linearly over O_Y',y' and therefore over O_S',s'. Flatness is
   invariant under these linear isomorphisms. No finite-presentation condition
   on f enters any step. -/
theorem elementary_devissage_flatness
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) (_hF : F.IsQuasiCoherentFiniteType) (x : X)
    (hx : ¬ Subsingleton
      (((tensorPullback (f.fiberι (f x))).obj F).presheaf.stalk (f.asFiber x)))
    (n : ℕ)
    (_hn : topologicalKrullDimAt
      (⟨f.asFiber x, hx⟩ :
        {q : f.fiber (f x) |
          ¬ Subsingleton (((tensorPullback (f.fiberι (f x))).obj F).presheaf.stalk q)}) =
      (n : WithBot ℕ∞))
    (X' Z' Y' S' : Scheme.{u})
    (g : X' ⟶ X) (e : S' ⟶ S) (f' : X' ⟶ S')
    (i : Z' ⟶ X') (π : Z' ⟶ Y') (h : Y' ⟶ S')
    (x' : X') (s' : S') (z' : Z') (G : Z'.Modules)
    [Etale g] [Etale e] (_hg : g x' = x) (_he : e s' = f x)
    [IsIso (g.residueFieldMap x')] [IsIso (e.residueFieldMap s')]
    (_hfg : g ≫ f = f' ≫ e) (_hπ : i ≫ f' = π ≫ h)
    [IsAffine X'] [IsAffine Z'] [IsAffine Y'] [IsAffine S']
    [IsClosedImmersion i] [LocallyOfFinitePresentation i] [QuasiCompact i] [QuasiSeparated i]
    [IsFinite π] (_hG : G.IsQuasiCoherentFiniteType)
    (_hiso : Nonempty ((pushforward i).obj G ≅ (tensorPullback g).obj F))
    [SmoothOfRelativeDimension n h] [GeometricallyIntegral h]
    (_hi : i z' = x') (_hs : h (π z') = s')
    (_hfibre : (π ⁻¹' ({π z'} : Set Y')) = {z'})
    (_hpure : @Algebra.IsPurelyTranscendentalExtension
      (S'.residueField (h (π z'))) (Y'.residueField (π z'))
      inferInstance inferInstance (h.residueFieldMap (π z')).hom.toAlgebra) :
    ((∃ U : X.Opens, x ∈ U ∧
      ((tensorPullback U.ι).obj F).IsFlatOver (U.ι ≫ f)) ↔
     (∃ U : Z'.Opens, z' ∈ U ∧
      ((tensorPullback U.ι).obj G).IsFlatOver (U.ι ≫ (π ≫ h)))) ∧
    ((∃ U : Z'.Opens, z' ∈ U ∧
      ((tensorPullback U.ι).obj G).IsFlatOver (U.ι ≫ (π ≫ h))) ↔
     (∃ U : Y'.Opens, π z' ∈ U ∧
      ((tensorPullback U.ι).obj ((pushforward π).obj G)).IsFlatOver (U.ι ≫ h))) ∧
    (Module.Flat (S.presheaf.stalk (f x))
        ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F)) ↔
      Module.Flat (S'.presheaf.stalk ((π ≫ h) z'))
        ((ModuleCat.restrictScalars ((π ≫ h).stalkMap z').hom).obj
          ((RingedSpace.moduleStalkFunctor Z'.toRingedSpace z').obj G))) ∧
    (Module.Flat (S'.presheaf.stalk ((π ≫ h) z'))
        ((ModuleCat.restrictScalars ((π ≫ h).stalkMap z').hom).obj
          ((RingedSpace.moduleStalkFunctor Z'.toRingedSpace z').obj G)) ↔
      Module.Flat (S'.presheaf.stalk (h (π z')))
        ((ModuleCat.restrictScalars (h.stalkMap (π z')).hom).obj
          ((RingedSpace.moduleStalkFunctor Y'.toRingedSpace (π z')).obj
            ((pushforward π).obj G)))) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
