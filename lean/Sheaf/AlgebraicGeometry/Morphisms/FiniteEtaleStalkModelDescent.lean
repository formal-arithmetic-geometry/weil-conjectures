/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality
import Sheaf.AlgebraicGeometry.SpecStalkLimitAffineNeighbourhoods
import Sheaf.AlgebraicGeometry.FibreProductLimit
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Sheaf.AlgebraicGeometry.DescendFinite
import Sheaf.AlgebraicGeometry.EtaleInverseLimitDescent

/-!
# Descent of a finite etale cover from a stalk family

Source: Stacks Project, Tags 0BQ5 and 0EY3, object descent in their proofs.
(blueprint: lem-sbc-finite-etale-stalk-model-descent)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A finite etale cover of the stalk family has a model on an open neighbourhood.

Source: Stacks Project, Tag 0BQ5 (limits-lemma-glueing-near-point), the paragraph
expressing the stalk spectrum as a limit, and Tag 0EY3
(limits-lemma-glueing-near-point-properties), property descent, relative to `C`.
(blueprint: lem-sbc-finite-etale-stalk-model-descent)

Proof:
1. Index affine open neighbourhoods of s by reverse inclusion. They form a directed
   preorder and their limit is Spec O(S,s), with its canonical maps to the opens.
2. Base change the system by c. Its stages C_W are qcqs: W is affine, and c is
   quasi-compact and quasi-separated. Its transitions are affine, being base changes
   of inclusions between affine opens. Its limit is C times_S Spec O(S,s).
3. The finite etale morphism Q is quasi-compact, separated and locally of finite
   presentation. Descend it to a finitely presented morphism at a stage by Tag 01ZM.
   Descend finiteness by Tag 01ZO and etaleness by Tag 07RP, and take a common later
   stage. These properties persist under base change.
4. Regard the resulting finite etale morphism as R. The canonical projection of
   the local family to C_W is l. The limit cone identifies its composite with the
   open inclusion with pullback.fst c (S.fromSpecStalk s). The cartesian comparison
   supplied by object descent gives the isomorphism l^*R isomorphic to Q.
No comparison with a cover on another open is asserted here. -/
theorem FiniteEtale.exists_stalk_neighbourhood_model {S C : Scheme.{u}}
    [IsNoetherian S] [QuasiSeparatedSpace S]
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [LocallyOfFinitePresentation c]
    (s : S) (Q : (Limits.pullback c (S.fromSpecStalk s)).FiniteEtale) :
    ∃ (W : S.Opens), s ∈ W ∧
      ∃ (R : (c ⁻¹ᵁ W).toScheme.FiniteEtale)
        (l : Limits.pullback c (S.fromSpecStalk s) ⟶ (c ⁻¹ᵁ W).toScheme),
        l ≫ (c ⁻¹ᵁ W).ι = pullback.fst c (S.fromSpecStalk s) ∧
          Nonempty ((FiniteEtale.pullback l).obj R ≅ Q) := by sorry

end AlgebraicGeometry.Scheme
