/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q133
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction
public import Sheaf.AlgebraicGeometry.AtlasEtaleRestriction
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModulePullbackQuasiCoherent
import Sheaf.AlgebraicGeometry.SpaceFinitePresentationModuleLimit
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.RelativelyFlatModulePullback
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction
import Sheaf.AlgebraicGeometry.RelativeFlatnessSourceCover
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Base change of relatively flat modules with proper support

Source: Stacks Project, spaces-morphisms.tex, Tag 05VW(1); sites-modules.tex,
Tag 03DO(5)-(7); spaces-perfect.tex, Tags 0CZI(3) and 0CZJ
(blueprint: lem-sfb-space-module-base-change-flat-proper-support).

The square is an arbitrary sheaf pullback square with scheme targets. Relative flatness
uses the recorded affine-local scheme predicate on every actual Zariski chart restriction;
for quasi-coherent modules it is equivalent to the ordinary stalk condition of the node.
Proper support is the existential closed-carrier criterion, expanded in both occurrences.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Arbitrary scheme base change preserves quasi-coherence, finite presentation, relative
flatness and support proper over the base.
Source: Stacks, Tag 05VW(1), Tag 03DO(5)-(7), Tags 0CZI(3) and 0CZJ
(blueprint: lem-sfb-space-module-base-change-flat-proper-support).

Proof:
1. Put H = p* M. Apply lem-sfb-space-module-pullback-quasicoherent and the arbitrary
   tensor-pullback assertion of lem-sfb-space-fp-module-limit-category. These give
   quasi-coherence and finite presentation without any flatness assumption on g.
2. Choose a surjective etale scheme chart U of X and base change it to U' over T'.
   By lem-trf-space-fibre-products-etale-covers this is a scheme chart of X'. Use
   lem-trf-scheme-zariski-etale-quasi-coherent-equivalence and
   lem-trf-space-etale-module-pushforward-restriction to identify H on U' with the
   scheme tensor pullback of M on U. Apply lem-pc-relatively-flat-module-pullback.
3. For any other chart W of X', form E = W times_X' U'. Its two projections are
   etale, hence flat by def-weil-etale-morphism, and E to W is surjective.
   The same restriction comparisons identify the two pullbacks of H on E.
   Apply the pointwise and surjective-flat-source assertions of
   lem-trf-relative-flatness-source-cover. Flatness therefore holds on every chart,
   in precisely the recorded scheme IsFlatOver sense, equivalently at every stalk.
4. Choose the proper carrier i:Z to X and G in the hypothesis. Base change Z to
   Z' = Z times_T T', canonically also Z times_X X'. Scheme testing, or
   lem-weil-pbc-closed-immersion-base-change, makes i':Z' to X' a closed immersion.
   By lem-sfb-space-proper-base-change, Z' to T' is proper for arbitrary g.
5. Set G' = q* G. It is quasi-coherent by the pullback theorem in step 1. Pull local
   finite generator surjections back: tensor pullback is a left adjoint, preserves
   cokernels and finite sums by lem-weil-pbc-left-adjoint-preserves-colimits, and
   sends the structure module to itself by tensor balancing. Refine the pulled covers
   by scheme charts using lem-trf-space-fibre-products-etale-covers and
   lem-trf-space-enlarged-etale-ringed-site-model. The restriction comparison of
   step 2 identifies their presentations. Thus G' is finite type.
6. Scheme tests show that a representable closed immersion is affine. Apply
   lem-sfb-space-affine-module-base-change to i and p: p* i_*G is canonically
   isomorphic to i'_* q*G, without flatness of p. Pull back the given isomorphism
   i_*G to M, obtaining i'_*G' isomorphic to H.
7. The carrier (i', G') gives the asserted existential proper support. Combine it
   with steps 1 and 3. Zero modules and empty charts cause no exception. -/
theorem moduleTensorPullback_flat_properSupport_baseChange
    {S : Scheme.{u}} (T T' : Over S) (g : T' ⟶ T)
    (X X' : AlgebraicSpace S) (f : X ⟶ schemeSpace T)
    (p : X' ⟶ X) (f' : X' ⟶ schemeSpace T')
    (sq : IsPullback p.hom f'.hom f.hom
      (ObjectProperty.homMk ⟨yoneda.map g⟩ : schemeSpace T' ⟶ schemeSpace T).hom)
    (hf : MapIsLocally (@LocallyOfFiniteType) f)
    (M : X.Modules) (hqc : M.IsQuasicoherent) (hfp : M.IsFinitePresentation)
    (hflat : ∀ U : X.EtaleSite,
      ((schemeRestriction X U).obj M).IsFlatOver
        (yoneda.preimage (U.obj.hom ≫ f.hom.hom)).left)
    (hsupp : ∃ (Z : AlgebraicSpace S) (i : Z ⟶ X),
      IsRepresentableWith (fun _ _ a ↦ IsClosedImmersion a.left) i.hom.hom ∧
      MapIsProper (i ≫ f) ∧ ∃ G : Z.Modules,
        G.IsQuasicoherent ∧ G.IsFiniteType ∧ Nonempty ((moduleDirectImage i).obj G ≅ M)) :
    ((moduleTensorPullback p).obj M).IsQuasicoherent ∧
    ((moduleTensorPullback p).obj M).IsFinitePresentation ∧
    (∀ U : X'.EtaleSite,
      ((schemeRestriction X' U).obj ((moduleTensorPullback p).obj M)).IsFlatOver
        (yoneda.preimage (U.obj.hom ≫ f'.hom.hom)).left) ∧
    (∃ (Z : AlgebraicSpace S) (i : Z ⟶ X'),
      IsRepresentableWith (fun _ _ a ↦ IsClosedImmersion a.left) i.hom.hom ∧
      MapIsProper (i ≫ f') ∧ ∃ G : Z.Modules,
        G.IsQuasicoherent ∧ G.IsFiniteType ∧
          Nonempty ((moduleDirectImage i).obj G ≅ (moduleTensorPullback p).obj M)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
