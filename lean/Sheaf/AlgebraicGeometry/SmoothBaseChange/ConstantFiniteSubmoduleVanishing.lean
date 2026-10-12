/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FilteredColimit
import Sheaf.AlgebraicGeometry.EtaleCohomologyFilteredColimit
import Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf

/-!
# Vanishing of constant coefficients from all finite submodules

Source: Stacks Project, Tag 0739 (lemma-colimit), applied on affine etale objects;
Tag 0F08, cyclic-coefficient reduction.
(blueprint: lem-sbc-constant-finite-submodule-vanishing)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- Higher direct image of a constant bounded torsion module vanishes if it vanishes
for all finite submodules. The submodule index is allowed to live in the module's universe.

Source: Stacks Project, Tag 0739 (lemma-colimit), and Tag 0F08,
cyclic-coefficient reduction.
(blueprint: lem-sbc-constant-finite-submodule-vanishing)

Proof:
1. Index by the finitely generated submodules of M, ordered by inclusion. The zero
submodule makes this category nonempty and the sum of two finitely generated submodules
is a common upper bound. This is a filtered category in Type (u+1). Its inclusion diagram
has colimit M: every element belongs to its cyclic submodule, and compatible linear maps
from the submodules glue uniquely to a linear map from M.
2. Every finitely generated submodule is finite. If it has k generators, the bound n
makes it a quotient of (Z/n)^k. The source is finite because n is nonzero; hence the
submodule is finite. Each corresponding constant sheaf therefore has zero higher image
by the hypothesis. The constant sheaf functor is a left adjoint, so preserves the union.
3. For q nonnegative, compute higher direct image on affine etale objects of X using
cohomology on their pullbacks to Y. These pullbacks are qcqs. Apply Tag 0739 to their
coherent etale sites, with the filtered index category from step 1. The proof of that
tag uses finite covers and finite intersections; it works in the lifted universe as
well, without shrinking this index category to Type 0. Pullback and sheafification
preserve colimits. Consequently the higher image of the union is the sheafified
filtered colimit of the higher images of these constant sheaves.
4. The latter diagram consists of zero objects, hence its colimit is zero. For q negative,
the right derived pushforward of a sheaf in degree zero is concentrated in nonnegative
degrees, so its degree-q homology is zero directly. The argument includes M=0 and n=1. -/
theorem isZero_higherDirectImage_constant_of_finite_submodules
    {X Y : Scheme.{u}} (h : Y ⟶ X) [QuasiCompact h] [QuasiSeparated h]
    (q : ℤ) (M : ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
    (n : ℕ) (hn : n ≠ 0) (hM : ∀ x : M, n • x = 0)
    (hfinite : ∀ (N : Submodule (ULift.{u + 1} ℤ) M), Finite N →
      IsZero (higherDirectImage (ULift.{u + 1} ℤ) h q
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).obj
          (ModuleCat.of (ULift.{u + 1} ℤ) N)))) :
    IsZero (higherDirectImage (ULift.{u + 1} ℤ) h q
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).obj M)) :=
  by sorry

end AlgebraicGeometry.Etale
