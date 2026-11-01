/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.Compactification.Defs
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Constructible compact support for constant finite coefficients on affine smooth curves

Source: Stacks Project, `more-etale.tex`, Tag 0GKX, `lemma-constant-shriek-rel-dim-1`,
lines 4511--4613 (blueprint: lem-fd-smooth-affine-curve-constant-shriek-constructible).

The theorem states constructibility of every cohomology sheaf of the bounded-below derived
lower shriek of a finite constant module on a separated affine smooth relative curve over an
affine Noetherian finite-dimensional base. The proof follows the closed-subset induction,
compact-support base change, good-curves diagram, quasi-finite boundary, proper-smooth models,
open-closed triangles, and descent steps recorded in the DAG node.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- Compactly supported cohomology of a finite constant module on a separated affine smooth
relative curve over an affine Noetherian finite-dimensional base is constructible in every
degree, in every characteristic.

Source: Stacks Project, `more-etale.tex`, Tag 0GKX, `lemma-constant-shriek-rel-dim-1`,
lines 4511--4613 (blueprint: lem-fd-smooth-affine-curve-constant-shriek-constructible).

Proof: use Noetherian closed-subset induction and the open-closed constructibility criterion.
Compact-support base change, exact inverse image, and pullback of constant sheaves reduce each
closed-subset step to the corresponding curve over the closed base. For a nonempty base, the
good-curves generic diagram, quasi-finite boundary constructibility, proper-smooth finite-module
constructibility, and compact-support composition establish the generic open case. The
open-closed triangles and Serre closure transfer constructibility across the boundary and any
thickening, and surjective descent followed by the induction criterion proves the assertion on
the original base. The comparison between finite-stalk and finite-constant-value formulations
of constructibility yields the stated module-sheaf predicate. No invertibility of the
characteristic is used.
-/
theorem constructibleCohomology_lowerShriek_constant_of_smooth_relativeDimension_one_all_char
    (ell : ℕ) (A : Type (u + 1)) [Field A] [Finite A] [CharP A ell]
    (S : Scheme.{u}) [IsAffine S] [IsNoetherian S]
    (hSdim : topologicalKrullDim S ≠ ⊤)
    (T : Scheme.{u}) (h : T ⟶ S) [IsSeparated h] [IsAffineHom h]
    [SmoothOfRelativeDimension 1 h]
    (M : ModuleCat.{u + 1} A) [Finite M] (c : Compactification h)
    [QuasiCompact c.i] (q : ℤ) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus
          (ModuleCat.{u + 1} A) c).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj
            ((constantSheaf T.smallEtaleTopology
              (ModuleCat.{u + 1} A)).obj M)))) := by
  sorry

end AlgebraicGeometry.Etale
