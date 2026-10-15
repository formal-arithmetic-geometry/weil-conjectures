/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.AlgebraicGeometry.FpqcFinerThanEtale
import Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects
import Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects

/-!
# The geometric comparison from the pro-etale to the etale site

Source: Stacks Project, Tag 099R, opening paragraph; Sites, Tags 00WX, 00X6 and 00YV
(blueprint: def-weil-pbc-site-comparison-morphism).

The inclusion is the existing `Scheme.toProEt`, identity on schemes and arrows.
Its continuity and finite-limit preservation are the existing instances
`Scheme.isContinuous_toProEt` and `Scheme.preservesFiniteLimits_toProEt`.
The set adjunction below uses restriction and the left Kan extension followed by
sheafification, rather than a chosen abstract left adjoint. The coefficient version uses
these same constructions in modules over a fixed ring.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The set-valued comparison adjunction, with inverse image given by left Kan extension
followed by sheafification and direct image by restriction along `toProEt T`.
The Kan extension at `W` is the colimit over `CostructuredArrow (toProEt T).op (op W)`,
which is the opposite of the category of pairs `(U, W ⟶ u(U))` of Tag 00WX.
Source: Stacks Project, Tags 099R and 00WX
(blueprint: def-weil-pbc-site-comparison-morphism). -/
noncomputable def proEtaleSiteComparison (T : Scheme.{u}) :
    Functor.sheafPullbackConstruction.sheafPullback (toProEt T)
      (Type (u + 1)) T.smallEtaleTopology (ProEt.topology T) ⊣
    (toProEt T).sheafPushforwardContinuous
      (Type (u + 1)) T.smallEtaleTopology (ProEt.topology T) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (toProEt T)
    (Type (u + 1)) T.smallEtaleTopology (ProEt.topology T)

/-- The inverse image in `proEtaleSiteComparison` preserves finite limits, so this
adjunction is the geometric morphism from the pro-etale to the etale topos.
Source: Stacks Project, Tags 099R, 00X6 and 00WJ
(blueprint: def-weil-pbc-site-comparison-morphism).

Proof: etale morphisms are weakly etale since they and their open diagonals are flat.
The existing inclusion therefore retains the underlying schemes and arrows. The terminal
scheme and scheme fibre products give terminal objects and fibre products in both sites;
their universal properties show that the inclusion preserves them and hence finite limits.
Etale covering families are fpqc by `fpqcCover_of_smallEtaleCover`, and their arrows are
weakly etale, so they are pro-etale covering families. Restriction consequently sends
sheaves to sheaves. Apply the continuous-functor sheaf adjunction (00WX): its left adjoint
is the left Kan extension followed by sheafification. The comma categories in this Kan
extension are filtered, using finite limits of the etale site and their preservation by
the inclusion (the presheaf-pullback left-exactness lemma). Filtered colimits of sets
preserve finite limits, so the Kan extension is left exact. Sheafification is left exact
by 00WJ, and so is inclusion of sheaves into presheaves. Their composite is left exact.
All categories and comma colimits are taken in the common larger site universe. -/
theorem preservesFiniteLimits_proEtaleSiteComparison (T : Scheme.{u}) :
    PreservesFiniteLimits
      (Functor.sheafPullbackConstruction.sheafPullback (toProEt T)
        (Type (u + 1)) T.smallEtaleTopology (ProEt.topology T)) := by
  sorry

/-- The same canonical comparison adjunction on sheaves of modules over a finite
(discrete) ring. The functors act on addition, zero, negation and scalar endomorphisms
by the module-valued Kan extension and sheafification. In particular this is the fixed
coefficient encoding of modules over the constant ring sheaf, not a structure-sheaf map.
Source: Stacks Project, Tag 00YV, module paragraph
(blueprint: def-weil-pbc-site-comparison-morphism). -/
noncomputable def proEtaleSiteComparisonModules (T : Scheme.{u})
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ] :
    ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) T ⊣
      ProEtale.comparisonLowerStar (ModuleCat.{u + 1} Λ) T :=
  ProEtale.comparisonAdjunction (ModuleCat.{u + 1} Λ) T

end AlgebraicGeometry.Scheme
