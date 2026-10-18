/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Mathlib.Algebra.Category.Grp.CartesianMonoidal
import Sheaf.Algebra.Homology.FilteredColimitDerivedTensor
import Sheaf.Algebra.Homology.IntegralBoundedKunnethExact
import Sheaf.AlgebraicGeometry.AbelianSheavesGModules
import Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry
import Sheaf.AlgebraicGeometry.GeometricStalkAsPullback
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import WeilConjectures.Algebra.Category.ModuleCat.TorSymmetry
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison

/-!
# Integral derived tensor: lower bound and torsion cohomology

Source: literature/stacks-project/etale-cohomology.tex, Tag 0F0F, lemma-projection-formula-proper
(blueprint: lem-kun-integral-derived-tensor-bounded-torsion).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/--
For integer étale coefficients, the derived tensor of two complexes bounded below in
cohomology is bounded below with the one-degree Tor loss.  If the first complex has
torsion cohomology, all cohomology sheaves of the derived tensor are torsion.
Source: literature/stacks-project/etale-cohomology.tex, Tag 0F0F, lemma-projection-formula-proper,
proof paragraphs beginning “Since Z has global dimension 1” and “Moreover”.
(blueprint: lem-kun-integral-derived-tensor-bounded-torsion).

The proof proceeds stalkwise at geometric points, using the exact point equivalence with
abelian groups and the integral Künneth short exact sequence for bounded truncations,
then passes to filtered colimits.  Torsion is preserved by tensor products, Tor, extensions,
and filtered colimits; geometric stalks detect zero and torsion sheaves.
-/
theorem integral_derivedTensor_boundedBelow_torsion
    (T : Scheme.{u})
    (A B : DerivedCategoryModule (ULift.{u + 1} ℤ) T)
    (a b : ℤ)
    (hA : ∀ i : ℤ, i < a →
      IsZero ((DerivedCategory.homologyFunctor
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) i).obj A))
    (hB : ∀ j : ℤ, j < b →
      IsZero ((DerivedCategory.homologyFunctor
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) j).obj B)) :
    (∀ r : ℤ, r < a + b - 1 →
      IsZero ((DerivedCategory.homologyFunctor
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) r).obj
        (((derivedTensor (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) T).obj A).obj B))) ∧
      ((∀ i : ℤ, CategoryTheory.Sheaf.IsTorsion
        ((sheafCompose T.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})).obj
          ((DerivedCategory.homologyFunctor
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) i).obj A))) →
        ∀ r : ℤ, CategoryTheory.Sheaf.IsTorsion
          ((sheafCompose T.smallEtaleTopology
            (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})).obj
            ((DerivedCategory.homologyFunctor
              (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) r).obj
              (((derivedTensor (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) T).obj A).obj B)))) := by
  sorry

end AlgebraicGeometry.Etale
