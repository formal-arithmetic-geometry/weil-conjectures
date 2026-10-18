/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Sites.Sheaf
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimits
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Sheaf.AlgebraicGeometry.ProEtale.WeakContractibleEquivalences

/-!
# Sections over weakly contractible affine pro-étale objects

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
sk-cor-pe-sections/det-pe-sections-limits-colimits.md
(blueprint: det-pe-sections-limits-colimits).
-/

@[expose] public section

universe u r v wJ uJ

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace CategoryTheory

/--
Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
sk-cor-pe-sections/det-pe-sections-limits-colimits.proof.md
(blueprint: det-pe-sections-limits-colimits).

First compute limits sectionwise, using the module-sheaf limit theorem and the size
convention. For coproducts sheafify the sectionwise direct sum, using presheaf colimits
and module sheafification. Finite subsums are sheaves and split off this sheafification
by coordinate projection. Local representatives in sheafification and a finite affine
covering refinement of W put each section into one finite subsum, so the comparison
is surjective. The finite-subsum retraction proves injectivity and compatibility with
summand maps. For cokernels sheafify the sectionwise quotient. Local representatives
and local equality make both the quotient map and the map onto its kernel locally
surjective; weak contractibility makes them surjective on W-sections, giving the
sectionwise cokernel. Present an arbitrary colimit as the cokernel of the difference
of the two maps between sums indexed by arrows and objects. Evaluation preserves
these sums, their difference maps and cokernels, so it preserves the canonical colimit
cocone. Equality on structure maps proves naturality; empty and filtered diagrams
are included.
-/
theorem peSectionsLimitsColimits {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) RingCat.{r})
    (W : X.ProEt) [IsAffine W.left]
    (hW : (Scheme.ProEt.topology X).IsWeaklyContractible.{max (u + 1) r v} W) :
    PreservesLimitsOfSize.{wJ, uJ} ((SheafOfModules.evaluation R (op W)) :
      SheafOfModules.{max (u + 1) r v} R ⥤ ModuleCat.{max (u + 1) r v} (R.obj.obj (op W))) ∧
      PreservesColimitsOfSize.{wJ, uJ} ((SheafOfModules.evaluation R (op W)) :
      SheafOfModules.{max (u + 1) r v} R ⥤ ModuleCat.{max (u + 1) r v} (R.obj.obj (op W))) := by
  sorry

end CategoryTheory
