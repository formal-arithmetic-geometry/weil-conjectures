/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.FieldTheory.SeparableClosure
import Sheaf.AlgebraicGeometry.StrictHenselizationChartMaximalIdeal
import Sheaf.Paper.StrictHenselizationPointedMap
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
import Mathlib.FieldTheory.PurelyInseparable.Basic
import WeilConjectures.AlgebraicGeometry.HomeomorphPurelyInseparableBaseChange
import Sheaf.AlgebraicGeometry.UniversalHomeomorphismInvariance
import Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula
import Sheaf.AlgebraicGeometry.AbelianSheavesGModules
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Sheaf.CategoryTheory.GrothendieckSpectralSequence
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.CategoryTheory.Sites.GlobalSections
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence
import WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence
import Sheaf.CategoryTheory.ExactCoupleConvergence
import Sheaf.AlgebraicGeometry.TorsionFilteredUnion
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Vertical

/-!
# Descent of a geometric cohomological dimension bound

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/
lem-sc-cd-ground-field.md (blueprint: lem-sc-cd-ground-field).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A finite-type scheme over `K` has torsion étale cohomological dimension at most `c + e`
if `K` has bound `c` and its base change to an algebraic closure has bound `e`.
Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/lem-sc-cd-ground-field.md,
(blueprint: lem-sc-cd-ground-field).

Proof plan, following the seven steps of the node:
1. Finite type implies quasi-compactness and local Noetherianity by
   `lem-weil-pbc-finite-type-algebra-noetherian`; quasi-separatedness follows from
   `lem-weil-pbc-locally-noetherian-quasi-separated`. Thus the scheme and structure map are qcqs.
2. The strict localization of `Spec K` at the chosen geometric point is `Spec Ksep` over `K`.
   Use `def-weil-pbc-relative-separable-closure`, the zero maximal ideal from
   `lem-weil-pbc-strict-henselization-chart-maximal-ideal`, the surjective residue map from
   `lem-weil-pbc-strict-henselization-pointed-map`, and its compatibility with the structural
   map from `def-weil-pbc-strict-henselization-structural-map`.
3. For a sheaf killed by a positive integer `n`, passage from `Ksep` to `Kbar` preserves
   cohomology by `lem-pc-kbar-pure-insep`, `lem-pc-homeo-pure-insep` and
   `thm-weil-pbc-universal-homeomorphism-invariance`. Pullback preserves the annihilator,
   so the geometric bound gives vanishing above `e`.
4. By `prop-weil-pbc-strict-henselization-stalk-formula` these groups are the stalks of
   higher direct images. The stalk equivalence `lem-exc-abelian-sheaves-gmodules` detects
   zero objects and the annihilator `n`, giving vanishing above `e` and torsion in all degrees.
5. Apply `thm-sp-grothendieck` to direct image followed by global sections. The categories
   are Grothendieck abelian by `lem-weil-pbc-abelian-etale-sheaves-grothendieck`;
   `def-weil-pbc-direct-image` and `def-weil-pbc-global-sections-functor` are additive and
   left exact. `lem-weil-pbc-direct-image-preserves-injectives` and
   `lemma-weil-pbc-leray-acyclicity` give the acyclicity assumption. Identify the abutment
   by `def-weil-pbc-etale-cohomology` and the direct-image section formula.
6. The field bound kills columns above `c`; step 4 kills rows above `e`. All terms of total
   degree above `c + e` vanish. Convergence (`def-sp-convergence`) gives a finite filtration
   with zero graded pieces, hence zero abutment.
7. Express any locally torsion sheaf as the filtered union of its `n`-torsion subsheaves
   using `lemma-weil-pbc-torsion-filtered-union`. Cohomology commutes with that union by
   `lem-weil-pbc-cohomology-filtered-colimit` since the scheme is qcqs. Step 6 proves
   vanishing for each subsheaf, hence the required bound `def-sc-etale-torsion-cd`.
-/
theorem hasTorsionEtaleCohomologicalDimensionLE_of_geometric
    (K Kbar : Type u) [Field K] [Field Kbar] [Algebra K Kbar] [IsAlgClosure K Kbar]
    (X : Scheme.{u}) [X.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))]
    (c e : ℕ) (hK : (Spec (.of K)).HasTorsionEtaleCohomologicalDimensionLE c)
    (hgeom : HasTorsionEtaleCohomologicalDimensionLE
      (pullback (X ↘ Spec (.of K))
        (Spec.map (CommRingCat.ofHom (algebraMap K Kbar)))) e) :
    X.HasTorsionEtaleCohomologicalDimensionLE (c + e) :=
  sorry

end AlgebraicGeometry.Scheme
