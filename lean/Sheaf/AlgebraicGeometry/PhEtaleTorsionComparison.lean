/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q135
-/
module

public import Sheaf.AlgebraicGeometry.PhSchemeSite
public import Sheaf.CategoryTheory.Sites.GeometricMorphism
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.Pullback
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
import Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors
import Sheaf.CategoryTheory.TorsionSheafComplexRepresentative
import Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization
import Sheaf.TraceFormula.BigSmallEtaleExactRetraction
import Sheaf.TraceFormula.PhBigEtaleTorsionAcyclicity

/-!
# Torsion comparison between the small etale and big ph sites

Source: Stacks Project, Etale Cohomology, Section 0DDV, Lemma 0DE5
(blueprint: lem-trf-ph-etale-torsion-comparison).

## Main definitions and statements

* `phEtaleGeometricMorphism`: the geometric morphism induced by the actual site inclusion.
* `phEtaleAbelianAdjunction`: its canonical adjunction on abelian sheaves.
* `isIso_phEtale_derivedUnit`: the torsion comparison for the ordinary derived unit.

The site functor is the actual inclusion, followed by the canonical small presentation.
Pullback and its adjunction are the sheafified Kan-extension constructions of Mathlib.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The inclusion of small etale schemes into the big ph site, in its chosen presentation.
Source: Stacks, Section 0DDV (blueprint: lem-trf-ph-etale-torsion-comparison). -/
def phEtaleInclusion (T : Scheme.{u}) : T.Etale ⥤ phSiteModel.{u, w} T :=
  Etale.forget T ⋙ AsSmall.up

/-- The inclusion defining `h_T` is continuous. Source: Stacks, Section 0DDV
(blueprint: lem-trf-ph-etale-torsion-comparison).
Proof: etale coverings are ph coverings, by the fppf-to-ph comparison and the fact that
etale morphisms are fppf. The inclusion preserves fibre products, which are the scheme
fibre products on both sites. Hence restriction of a ph sheaf is an etale sheaf.
Transport this assertion along the canonical equivalence `AsSmall.equiv`. -/
theorem phEtaleInclusion_isContinuous (T : Scheme.{u}) :
    (phEtaleInclusion.{u, w} T).IsContinuous
      T.smallEtaleTopology (phModelTopology T) := by
  sorry

attribute [instance] phEtaleInclusion_isContinuous

/-- Finite limits are scheme fibre products and the final scheme over the base.
Source: Stacks, Section 0DDV (blueprint: lem-trf-ph-etale-torsion-comparison). -/
instance phEtaleInclusion_preservesFiniteLimits (T : Scheme.{u}) :
    PreservesFiniteLimits (phEtaleInclusion.{u, w} T) :=
  comp_preservesFiniteLimits (Etale.forget T)
    (AsSmall.equiv (C := Over T)).functor

/-- Flatness of the finite-limit-preserving site inclusion.
Source: Stacks, Section 0DDV (blueprint: lem-trf-ph-etale-torsion-comparison). -/
instance phEtaleInclusion_representablyFlat (T : Scheme.{u}) :
    RepresentablyFlat (phEtaleInclusion.{u, w} T) :=
  flat_of_preservesFiniteLimits _

/-- The inverse image of `h_T` on abelian sheaves, the canonical sheafified Kan extension.
Source: Stacks, Section 0DDV (blueprint: lem-trf-ph-etale-torsion-comparison). -/
abbrev phEtaleAbelianInverse (T : Scheme.{u}) :=
  (phEtaleInclusion.{u, w} T).sheafPullback AddCommGrpCat.{max w (u + 1)}
    T.smallEtaleTopology (phModelTopology T)

/-- The direct image of `h_T` on abelian sheaves, restriction along the site inclusion.
Source: Stacks, Section 0DDV (blueprint: lem-trf-ph-etale-torsion-comparison). -/
abbrev phEtaleAbelianDirect (T : Scheme.{u}) :=
  (phEtaleInclusion.{u, w} T).sheafPushforwardContinuous AddCommGrpCat.{max w (u + 1)}
    T.smallEtaleTopology (phModelTopology T)

/-- The ordinary inverse-image/direct-image adjunction, with its canonical unit.
Source: Stacks, Section 0DDV (blueprint: lem-trf-ph-etale-torsion-comparison). -/
def phEtaleAbelianAdjunction (T : Scheme.{u}) :
    phEtaleAbelianInverse.{u, w} T ⊣ phEtaleAbelianDirect T :=
  (phEtaleInclusion T).sheafAdjunctionContinuous _ _ _

/-- Sheafification on the original small etale category with values in the common universe.
Source: Stacks, Section 0DDV and the size convention
(blueprint: lem-trf-ph-etale-torsion-comparison). -/
instance phEtaleAbelian_hasSheafify (T : Scheme.{u}) :
    HasSheafify T.smallEtaleTopology AddCommGrpCat.{max w (u + 1)} :=
  hasSheafifyEssentiallySmallSite.{u, max w (u + 1), u + 1,
    max (w + 1) (u + 2), max w (u + 1)} _ _

/-- The inverse images on sets and abelian groups preserve finite limits, so the inclusion
induces a geometric morphism and its exact abelian inverse image. Source: Stacks,
Section 0DDV (blueprint: lem-trf-ph-etale-torsion-comparison).
Proof: the inclusion preserves finite limits, hence is representably flat. Compute its
left adjoint as a left Kan extension followed by sheafification. The relevant opposite
comma categories are filtered, so these Kan-extension colimits commute with finite limits
in sets and abelian groups. Sheafification is left exact. Transporting through `AsSmall`
does not change these assertions. -/
theorem phEtaleInverse_leftExact (T : Scheme.{u}) :
    PreservesFiniteLimits ((phEtaleInclusion.{u, w} T).sheafPullback
      (Type (max w (u + 1))) T.smallEtaleTopology (phModelTopology T)) ∧
    PreservesFiniteLimits (phEtaleAbelianInverse.{u, w} T) := by
  sorry

/-- The inverse image is left exact by flatness of the site inclusion.
Source: Stacks, Section 0DDV (blueprint: lem-trf-ph-etale-torsion-comparison). -/
instance phEtaleAbelianInverse_preservesFiniteLimits (T : Scheme.{u}) :
    PreservesFiniteLimits (phEtaleAbelianInverse.{u, w} T) :=
  (phEtaleInverse_leftExact T).2

/-- The actual geometric morphism `h_T` on sheaves of sets, induced by the inclusion.
Source: Stacks, Section 0DDV (blueprint: lem-trf-ph-etale-torsion-comparison). -/
def phEtaleGeometricMorphism (T : Scheme.{u}) :
    GeometricMorphism (PhSheaf.{u, w} T)
      (Sheaf T.smallEtaleTopology (Type (max w (u + 1)))) where
  inverse := (phEtaleInclusion T).sheafPullback (Type (max w (u + 1)))
    T.smallEtaleTopology (phModelTopology T)
  direct := (phEtaleInclusion T).sheafPushforwardContinuous (Type (max w (u + 1)))
    T.smallEtaleTopology (phModelTopology T)
  adj := (phEtaleInclusion T).sheafAdjunctionContinuous (Type (max w (u + 1)))
    T.smallEtaleTopology (phModelTopology T)
  leftExact := (phEtaleInverse_leftExact T).1

/-- The inverse image is a left adjoint, hence preserves finite colimits.
Source: Stacks, Section 0DDV (blueprint: lem-trf-ph-etale-torsion-comparison). -/
instance phEtaleAbelianInverse_preservesFiniteColimits (T : Scheme.{u}) :
    PreservesFiniteColimits (phEtaleAbelianInverse.{u, w} T) :=
  (phEtaleAbelianAdjunction T).leftAdjoint_preservesColimits.{0, 0}.preservesFiniteColimits

/-- Exact inverse image is additive on abelian sheaves.
Source: Stacks, Section 0DDV (blueprint: lem-trf-ph-etale-torsion-comparison). -/
instance phEtaleAbelianInverse_additive (T : Scheme.{u}) :
    (phEtaleAbelianInverse.{u, w} T).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Restriction is a right adjoint and preserves finite limits.
Source: Stacks, Section 0DDV (blueprint: lem-trf-ph-etale-torsion-comparison). -/
instance phEtaleAbelianDirect_preservesFiniteLimits (T : Scheme.{u}) :
    PreservesFiniteLimits (phEtaleAbelianDirect.{u, w} T) :=
  (phEtaleAbelianAdjunction T).rightAdjoint_preservesLimits.{0, 0}.preservesFiniteLimits

/-- Restriction is additive on abelian sheaves.
Source: Stacks, Section 0DDV (blueprint: lem-trf-ph-etale-torsion-comparison). -/
instance phEtaleAbelianDirect_additive (T : Scheme.{u}) :
    (phEtaleAbelianDirect.{u, w} T).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The comparison is the ordinary derived adjunction unit and is invertible for
bounded-below complexes with locally torsion cohomology. Source: Stacks, Lemma 0DE5
(blueprint: lem-trf-ph-etale-torsion-comparison).

Proof:
1. Factor `h_T` through the big etale site as `pi_T` after `epsilon_T`, using
   lem-trf-big-small-etale-exact-retraction and lem-trf-ph-big-etale-torsion-acyclicity.
   The composite site functor is exactly the inclusion defining `h_T`.
2. For a torsion sheaf `F`, the epsilon unit on `pi_T⁻¹ F` is invertible and its
   inverse image is epsilon-acyclic. Apply src-right-derived-functor-plus-acyclic-unit.
   Exactness and the invertible underived unit of pi give the corresponding pi result.
3. By lem-sfb-derived-composition-adjunction-normalization the derived h unit is the
   composite of these two units, so it is invertible on each torsion sheaf.
4. By lem-trf-torsion-sheaf-complex-representative choose a bounded-below representative
   with torsion terms. Its inverse image has h-acyclic terms; the termwise ordinary
   units form an isomorphism of complexes by naturality.
5. Apply src-right-derived-functor-plus-acyclic-unit to this complex. The comparison
   composed with the termwise unit is the actual derived adjunction unit: on an
   injective resolution its transpose is the resolution map and hence the identity
   after localization, as in lem-pc-derived-adjoint-functors. Enough injectives and
   K-injective resolutions are supplied by lem-weil-pbc-site-sheaves-enough-injectives
   and prop-pur-kinjective-resolutions-exist. Naturality transports the result to `K`.
No single integer annihilating all sections or all cohomology sheaves is required. -/
theorem isIso_phEtale_derivedUnit (T : Scheme.{u})
    [HasDerivedCategory.{max (w + 1) (u + 2)}
      (Sheaf T.smallEtaleTopology AddCommGrpCat.{max w (u + 1)})]
    [HasDerivedCategory.{max (w + 1) (u + 2)}
      (Sheaf (phModelTopology.{u, w} T) AddCommGrpCat.{max w (u + 1)})]
    (K : DerivedCategory.Plus
      (Sheaf T.smallEtaleTopology AddCommGrpCat.{max w (u + 1)}))
    (hK : ∀ q : ℤ, ((DerivedCategory.Plus.homologyFunctor
      (Sheaf T.smallEtaleTopology AddCommGrpCat.{max w (u + 1)}) q).obj K).IsTorsion) :
    IsIso ((phEtaleAbelianAdjunction.{u, w} T).derivedPlus.unit.app K) := by
  sorry

end AlgebraicGeometry.Scheme
