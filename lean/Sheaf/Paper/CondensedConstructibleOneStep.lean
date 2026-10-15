/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C4
-/
module

public import Sheaf.Paper.CondensedConstructiblePiece
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import Sheaf.Paper.CondensedOpenClosedRecollement
import WeilConjectures.Topology.StratificationDense
import Sheaf.AlgebraicGeometry.LocallyClosedStratification
import WeilConjectures.ConstructibleSheaf.GenericConstancy

/-! # One open/closed step for a constructible condensed sheaf -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- A constructible sheaf is a single locally closed piece, or an extension by a
constructible sheaf supported on a proper closed subscheme.
Source: Hemo--Richarz--Scholbach, Lemma 5.3(2), open/closed induction step.
(blueprint: lem-weil-pbc-condensed-constructible-one-step)

Proof: if T is nonempty, choose the finite stratification in constructibility.
The union of the interiors of its locally closed strata is dense: each stratum
minus its interior is nowhere dense, and a finite union of those is nowhere dense.
Thus some stratum has nonempty interior U. Restrict that stratum's presentations
to U, with the canonical coefficient comparisons, to obtain a locally finitely
presented module there. More precisely, the base change of the stratum to U is
a surjective closed immersion; empty-complement recollement gives a coefficient-
compatible equivalence reflecting the presentations. This handles differing
nilpotent structures without identifying schemes. The complementary closed
immersion i : Z → T is proper because U is nonempty. The proved constructible
pullback theorem makes i^*M constructible. Open/closed recollement supplies exact
closed pushforward and the triangle j_!j^*M[0] → M[0] → i_*i^*M[0]. Its first
term is a piece (use the identity closed immersion); the exact functor and single
comparisons identify the third term with D(i_*) applied to MZ[0] in the ordinary
derived category. If T is empty all its module sheaves are zero, so the identity
immersions and rank-zero presentations give the first alternative. -/
theorem condensed_constructible_one_step
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E.val) T))
    (hM : IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj E.val) T) M) :
    condensedConstructiblePiece T ℓ E ((DerivedCategory.singleFunctor _ 0).obj M) ∨
    ∃ (Z : Scheme.{u}) (i : Z ⟶ T),
      Exists fun [_hi : IsClosedImmersion i] ↦
      Exists fun [_hex : PreservesFiniteColimits
          (CondensedRing.lowerStar (Profinite.continuousMapRingObj E.val) i)] ↦
      ¬ Function.Surjective i ∧
      ∃ (MZ : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj E.val) Z)),
        IsConstructibleModuleObject
          (condensedRingObj (Profinite.continuousMapRingObj E.val) Z) MZ ∧
        ∃ (A : DerivedCategory
            (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
              (condensedRingObj (Profinite.continuousMapRingObj E.val) T)))
          (f : A ⟶ (DerivedCategory.singleFunctor _ 0).obj M)
          (g : (DerivedCategory.singleFunctor _ 0).obj M ⟶
            (CondensedRing.lowerStar
              (Profinite.continuousMapRingObj E.val) i).mapDerivedCategory.obj
                ((DerivedCategory.singleFunctor _ 0).obj MZ))
          (h : (CondensedRing.lowerStar
              (Profinite.continuousMapRingObj E.val) i).mapDerivedCategory.obj
                ((DerivedCategory.singleFunctor _ 0).obj MZ) ⟶
            A⟦(1 : ℤ)⟧),
          Pretriangulated.Triangle.mk f g h ∈ distTriang _ ∧
          condensedConstructiblePiece T ℓ E A := by
  sorry

end AlgebraicGeometry.ProEtale
