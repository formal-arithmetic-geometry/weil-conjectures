/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.Paper.PQFCohomology
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic
import Sheaf.AlgebraicGeometry.GlobalSectionsLeftExact
import Sheaf.AlgebraicGeometry.ModulePushforwardInjectiveAcyclic
import Sheaf.AlgebraicGeometry.TensorPullback
import Sheaf.CategoryTheory.GrothendieckComposablePair
import Sheaf.CategoryTheory.GrothendieckSpectralSequence
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions

/-!
# Leray spectral sequence for a quasi-coherent module on a scheme

Source: Stacks Project, Cohomology of Sheaves, Lemma 20.13.4, Tag 01F2,
specialized to a module in degree zero (blueprint: pqf-lem-leray).
-/

@[expose] public section

universe v

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- A scheme morphism and a quasi-coherent module admit the Leray spectral sequence.
Both the page and the abutment are viewed as abelian groups by forgetting their
respective global-section scalar actions. Higher direct images and cohomology are
the right derived functors recorded in `pqf-def-cohomology`.

Source: Stacks Project, Cohomology of Sheaves, Lemma 20.13.4, Tag 01F2
(blueprint: pqf-lem-leray).

Proof:
1. Take F = module direct image and G = global sections followed by forgetting to
abelian groups. Module sheaves are Grothendieck abelian with enough injectives by
prop-pur-kinjective-resolutions-exist; abelian groups are Grothendieck abelian by
lem-weil-pbc-ring-modules-grothendieck-abelian for the integers. Direct image is the
sectionwise additive functor of def-pc-module-pullback, and preserves kernels and
finite products. Global sections is additive and left exact by
lem-sc-global-sections-left-exact. Direct images of injectives are G-acyclic by
lem-weil-pbc-module-pushforward-injective-acyclic, giving def-sp-composite-acyclicity.
2. Apply thm-sp-grothendieck to this pair and the module to obtain the first-quadrant
spectral sequence, its second-page isomorphisms, and convergence to the derived
composite in each total degree.
3. By pqf-def-cohomology the second-page objects are H^p(Y, R^q f_* F).
The composite global sections after direct image is global sections on X.
Resolution comparison (lem-sp-derived-well-defined) identifies its right derived
functors with H^n(X, F). Forgetting scalar actions is exact, so gives the displayed
abelian-group terms and abutment without changing cohomology. -/
theorem exists_leray_spectralSequence {X Y : Scheme.{v}} (f : X ⟶ Y)
    (F : SheafOfModules.{v} (moduleRings X.toRingedSpace)) [F.IsQuasicoherent] :
    ∃ E : E₂CohomologicalSpectralSequenceNat AddCommGrpCat.{v},
      (∀ p q : ℕ, Nonempty ((E.page 2).X (p, q) ≅
        (forget₂ (ModuleCat.{v} ((moduleRings Y.toRingedSpace).obj.obj (op ⊤)))
          AddCommGrpCat.{v}).obj
          ((RingedSpace.moduleCohomology Y.toRingedSpace p).obj
            (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived q).obj F)))) ∧
      E.AbutsTo (fun n ↦
        (forget₂ (ModuleCat.{v} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
          AddCommGrpCat.{v}).obj ((RingedSpace.moduleCohomology X.toRingedSpace n).obj F)) := by
  sorry

end AlgebraicGeometry
