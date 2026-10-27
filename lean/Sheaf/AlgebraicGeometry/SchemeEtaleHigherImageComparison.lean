/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q40
-/
module

public import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
public import Sheaf.AlgebraicGeometry.QcohCohomologyEtalePullbackNaturality
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.Modules.Ext
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange

import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
import WeilConjectures.AlgebraicGeometry.Cohomology.Projective
import Sheaf.CategoryTheory.Sites.ModuleDerivedEvaluationSlice
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison
import WeilConjectures.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
import WeilConjectures.AlgebraicGeometry.LerayDegenerateSections
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import WeilConjectures.AlgebraicGeometry.FlatBaseChangeMapSections

/-!
# Higher direct images on the Zariski and small étale sites

Source: Stacks Project, Descent, Tag 071N, lemma-higher-direct-images-small-etale,
étale case; Tags 03DX(2), 03LC, and lemma-compare-etale-zariski-flat.
(blueprint: lem-sfb-scheme-etale-higher-image-comparison).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- Proof data for the canonical flat ringed-site pullback and injective derivation.
There is no chosen module, functor, map, abelian structure, or derived category here.
The extension and restriction are precisely those of the recorded equivalence.
Source: Stacks 03DX(2), 071N, and lemma-compare-etale-zariski-flat
(blueprint: lem-sfb-scheme-etale-higher-image-comparison). -/
structure EtaleHigherImageContext (X : Scheme.{u}) extends ZariskiEtaleModuleContext X where
  /-- Injective resolutions are taken in all small étale structure-sheaf modules. -/
  enoughInjectives : EnoughInjectives (SmallEtaleModules X)
  /-- Canonical tensor extension is additive. -/
  additive : toZariskiEtaleModuleContext.extension.Additive
  /-- Flatness of the comparison morphism makes tensor extension left exact. -/
  preservesFiniteLimits : PreservesFiniteLimits toZariskiEtaleModuleContext.extension
  /-- Tensor extension, a left adjoint, is right exact. -/
  preservesFiniteColimits : PreservesFiniteColimits toZariskiEtaleModuleContext.extension

/-- The direct-image square, fixed on every open by the canonical pullback identification.
Thus its isomorphism is specified on every section, rather than arbitrarily selected.
Source: Stacks 03LC and 071N
(blueprint: lem-sfb-scheme-etale-higher-image-comparison). -/
structure EtaleHigherImageSquare {X Y : Scheme.{u}} (f : X ⟶ Y)
    (cX : EtaleHigherImageContext X) (cY : EtaleHigherImageContext Y) where
  /-- Restriction to opens commutes with direct image. -/
  comparison : smallEtaleModulePushforward f ⋙ cY.toZariskiEtaleModuleContext.restriction ≅
    cX.toZariskiEtaleModuleContext.restriction ⋙ pushforward f
  /-- The square is the usual restriction map along the canonical étale object isomorphism. -/
  onOpens : ∀ (M : SmallEtaleModules X) (W : Y.Opens),
    (comparison.hom.app M).app W =
      M.val.presheaf.map (AlgebraicGeometry.gabberPreimageEtaleIso f W).hom.op

/-- The canonical ordinary comparison is the mate of the specified restriction square.
Its source is (f_* F)_et and its target is f_et,*(F_et).
Source: Stacks 03LC and 071N
(blueprint: lem-sfb-scheme-etale-higher-image-comparison). -/
def EtaleHigherImageSquare.mate {X Y : Scheme.{u}} {f : X ⟶ Y}
    {cX : EtaleHigherImageContext X} {cY : EtaleHigherImageContext Y}
    (s : EtaleHigherImageSquare f cX cY) :
    pushforward f ⋙ cY.toZariskiEtaleModuleContext.extension ⟶
      cX.toZariskiEtaleModuleContext.extension ⋙ smallEtaleModulePushforward f :=
  ((mateEquiv cX.toZariskiEtaleModuleContext.adjunction
    cY.toZariskiEtaleModuleContext.adjunction).symm
      (TwoSquare.mk _ _ _ _ s.comparison.inv)).natTrans

/-- Derive the canonical mate and apply the canonical counit F_et -> M for F = M_Zar.
This is a natural transformation on all étale modules; its components on quasi-coherent
modules are the inverse direction of the isomorphism in Tag 071N.
Only proof instances are supplied by the contexts. The standard derived categories used
internally disappear from the type of the resulting classical right-derived map.
Source: Stacks 071N, derived from the normalized 03LC square
(blueprint: lem-sfb-scheme-etale-higher-image-comparison). -/
def EtaleHigherImageSquare.higherComparison {X Y : Scheme.{u}} {f : X ⟶ Y}
    {cX : EtaleHigherImageContext X} {cY : EtaleHigherImageContext Y}
    (s : EtaleHigherImageSquare f cX cY) (q : ℕ) :=
  letI := cX.enoughInjectives
  letI := cX.additive
  letI := cY.additive
  letI := cX.preservesFiniteLimits
  letI := cY.preservesFiniteLimits
  letI := cX.preservesFiniteColimits
  letI := cY.preservesFiniteColimits
  letI := HasDerivedCategory.standard X.Modules
  letI := HasDerivedCategory.standard Y.Modules
  letI := HasDerivedCategory.standard (SmallEtaleModules X)
  letI := HasDerivedCategory.standard (SmallEtaleModules Y)
  Functor.whiskerLeft cX.toZariskiEtaleModuleContext.restriction
      (Functor.rightDerivedBaseChange s.mate q) ≫
    Functor.whiskerRight cX.toZariskiEtaleModuleContext.adjunction.counit
      ((smallEtaleModulePushforward f).rightDerived q)

/-- The same normalized mate on bounded below derived categories, evaluated at M_Zar[0],
then transported by the single-complex comparison and the counit to Rf_et,* M[0].
This definition uses genuine derived functors, not a list of unrelated cohomology objects.
Source: Stacks 071N and the canonical derived base-change construction
(blueprint: lem-sfb-scheme-etale-higher-image-comparison). -/
def EtaleHigherImageSquare.derivedComparison {X Y : Scheme.{u}} {f : X ⟶ Y}
    {cX : EtaleHigherImageContext X} {cY : EtaleHigherImageContext Y}
    (s : EtaleHigherImageSquare f cX cY) (M : SmallEtaleModules X) :=
  letI := cX.enoughInjectives
  letI := cX.additive
  letI := cY.additive
  letI := cX.preservesFiniteLimits
  letI := cY.preservesFiniteLimits
  letI := cX.preservesFiniteColimits
  letI := cY.preservesFiniteColimits
  letI := HasDerivedCategory.standard X.Modules
  letI := HasDerivedCategory.standard Y.Modules
  letI := HasDerivedCategory.standard (SmallEtaleModules X)
  letI := HasDerivedCategory.standard (SmallEtaleModules Y)
  (Functor.rightDerivedFunctorPlusBaseChange s.mate).app
      ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj
        (cX.toZariskiEtaleModuleContext.restriction.obj M)) ≫
    (smallEtaleModulePushforward f).rightDerivedFunctorPlus.map
      ((cX.toZariskiEtaleModuleContext.extension.mapDerivedCategoryPlusSingleFunctor 0).hom.app
          (cX.toZariskiEtaleModuleContext.restriction.obj M) ≫
        (DerivedCategory.Plus.singleFunctor (SmallEtaleModules X) 0).map
          (cX.toZariskiEtaleModuleContext.adjunction.counit.app M))

/-- The canonical derived comparison for a qcqs scheme morphism is an isomorphism on
quasi-coherent modules. Its per-degree form identifies the two higher direct images;
the Zariski one is quasi-coherent. Naturality is built into `higherComparison`.
The displayed arrow goes from the associated Zariski higher image to the étale higher
image; its inverse is the arrow written in the node. All right derived functors resolve
in the categories of all structure-sheaf modules, never just quasi-coherent modules.

Source: Stacks Project, Descent, Tag 071N and Proposition 03DX(2)
(blueprint: lem-sfb-scheme-etale-higher-image-comparison).

Proof following the five DAG steps:
1. The canonical equivalence restricts M to F = M_Zar and its counit identifies F_et
with M. Quasi-compact, quasi-separated direct image has quasi-coherent higher images
N_q, by lem-pc-finite-support-hi(1), without any quasi-compactness assumption on Y.
The comparison ringed-site morphism is flat (lemma-compare-etale-zariski-flat), so
its tensor extension is exact; the affine étale basis gives enough injectives in the
original module universe. These supply the proof-only contexts.
2. On an étale U -> Y, the terminal chart X times_Y U computes direct image. For an
injective resolution I of M, the higher direct image is the sheafification of the
module presheaf U -> H^q(I(X times_Y U)). Derived evaluation on the slice, followed
by module/abelian evaluation comparison and the étale slice equivalence, identifies
this with étale cohomology of M restricted to X times_Y U. Kernels are objectwise;
images require sheafification. Use lem-pe-ringed-site-derived-evaluation-slice,
lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison and
lem-pc-sites-module-sheafification-interface.
3. The canonical quasi-coherent cohomology comparison identifies this presheaf with
U -> H^q(X times_Y U, a_U^* F). Its compatibility with étale pullback identifies
the restriction maps and scalar actions, by lem-sfb-qcoh-cohomology-etale-pullback-naturality.
4. On affine U, qcqs permanence, affine vanishing, and degenerate Leray identify
this with sections of R^q p_U,* a_U^* F. Flat base change along the étale U -> Y
identifies these with sections of g^*N_q. Use lem-weil-pbc-qcqs-morphism-permanence,
pqf-lem-affine-vanishing, lem-pc-leray-degenerate-sections and lem-pc-flat-base-change-cohom.
5. The section formula for flat base change gives compatibility on arrows between
affine étale objects; both composites pull back the same cocycle. Affine covers and
the sheaf condition glue these identifications. The resulting comparison is the
derived mate of the open-normalized square: it extends its degree-zero mate and
is compatible with the injective-resolution augmentations. Hence the specified
higherComparison is invertible, naturally in M. Exact extension commutes with
homology, so these are precisely the homology maps of derivedComparison. In negative
degrees both sides vanish; in all nonnegative degrees the maps are isomorphisms.
Conservativity of derived homology proves the derived assertion. -/
theorem scheme_etale_derived_image_comparison :
    ∃ c : ∀ X : Scheme.{u}, EtaleHigherImageContext X,
      ∀ (X Y : Scheme.{u}) (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f],
        ∃ s : EtaleHigherImageSquare f (c X) (c Y),
          ∀ (M : SmallEtaleModules X) [M.IsQuasicoherent],
            ((c X).toZariskiEtaleModuleContext.restriction.obj M).IsQuasicoherent ∧
            (∀ q : ℕ, (((pushforward f).rightDerived q).obj
              ((c X).toZariskiEtaleModuleContext.restriction.obj M)).IsQuasicoherent) ∧
            IsIso (s.derivedComparison M) := by
  sorry

/-- The per-degree form of the canonical derived comparison: for every q >= 0 the
specified module map (R^q f_Zar,* M_Zar)_et -> R^q f_et,* M is invertible. Its inverse
is the canonical isomorphism in the node, natural in M since higherComparison is a
natural transformation on all small étale modules. The Zariski higher image is
quasi-coherent, so its associated étale module has the asserted interpretation.
Source: Stacks Project, Descent, Tag 071N and Proposition 03DX(2)
(blueprint: lem-sfb-scheme-etale-higher-image-comparison).

Proof: take the contexts and normalized square from
scheme_etale_derived_image_comparison. Apply degree-q homology to its isomorphism.
Exact tensor extension commutes with homology, and the injective-resolution
comparison identifies homology of Rf applied to a module in degree zero with the
classical right-derived functor. By the definition of rightDerivedBaseChange,
the resulting map is exactly higherComparison q, including its counit factor.
The quasi-coherence clauses are those of the derived statement. -/
theorem scheme_etale_higher_image_comparison :
    ∃ c : ∀ X : Scheme.{u}, EtaleHigherImageContext X,
      ∀ (X Y : Scheme.{u}) (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f],
        ∃ s : EtaleHigherImageSquare f (c X) (c Y),
          ∀ (M : SmallEtaleModules X) [M.IsQuasicoherent],
            ((c X).toZariskiEtaleModuleContext.restriction.obj M).IsQuasicoherent ∧
            ∀ q : ℕ,
              (((pushforward f).rightDerived q).obj
                ((c X).toZariskiEtaleModuleContext.restriction.obj M)).IsQuasicoherent ∧
              IsIso ((s.higherComparison q).app M) := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
