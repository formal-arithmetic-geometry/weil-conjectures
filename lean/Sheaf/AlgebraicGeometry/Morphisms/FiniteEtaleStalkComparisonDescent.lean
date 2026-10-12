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

/-!
# Descent of a comparison between two existing finite etale models

Source: Stacks Project, Tag 0BQ5, comparison descent in its proof.
(blueprint: lem-sbc-finite-etale-stalk-comparison-descent)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Two existing models with a comparison on the local overlap become isomorphic
on an open overlap after shrinking the second neighbourhood.

Source: Stacks Project, Tag 0BQ5 (limits-lemma-glueing-near-point), the last
paragraph of the proof, using the morphism and equality parts of Tag 01ZM.
(blueprint: lem-sbc-finite-etale-stalk-comparison-descent)

Proof:
1. Restrict to affine neighbourhoods V of s contained in W. Noetherianity makes
   U intersect V quasi-compact. Base change by c; the overlap stages are qcqs and
   have affine transitions. Their limit is C_U times_C C_s^loc.
   The equation for l identifies the restriction of the fixed model R to this
   limit with the iterated pullback appearing in the hypothesis.
2. Both covers on each overlap are finite etale, hence finitely presented. Descend
   the given comparison and its inverse by the morphism part of Tag 01ZM.
3. The two composites become identities after passage to the limit. By the equality
   part of Tag 01ZM they are identities at a common later neighbourhood V. Thus
   the descended maps form an isomorphism of finite etale covers.
4. Pullback pasting identifies the second cover with the restriction to the overlap
   of (FiniteEtale.pullback (C.homOfLE (c.preimage_mono hVW))).obj R.
   The first cover is PA restricted by the left inclusion. These identifications
   produce the stated isomorphism. V is contained in W and still contains s.
The empty overlap is allowed: the same descent of maps and equations applies;
no new finite etale model and no gluing over the union are required. -/
theorem FiniteEtale.exists_neighbourhood_comparison_of_stalk {S C : Scheme.{u}}
    [IsNoetherian S] [QuasiSeparatedSpace S]
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [LocallyOfFinitePresentation c]
    (U W : S.Opens) (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale) (s : S) (hsW : s ∈ W)
    (R : (c ⁻¹ᵁ W).toScheme.FiniteEtale)
    (l : Limits.pullback c (S.fromSpecStalk s) ⟶ (c ⁻¹ᵁ W).toScheme)
    (hl : l ≫ (c ⁻¹ᵁ W).ι = pullback.fst c (S.fromSpecStalk s))
    (e : Nonempty ((FiniteEtale.pullback
      (pullback.fst (c ⁻¹ᵁ U).ι (pullback.fst c (S.fromSpecStalk s)))).obj PA ≅
      (FiniteEtale.pullback
      (pullback.snd (c ⁻¹ᵁ U).ι (pullback.fst c (S.fromSpecStalk s)))).obj
        ((FiniteEtale.pullback l).obj R))) :
    ∃ (V : S.Opens) (hVW : V ≤ W), s ∈ V ∧
      Nonempty ((FiniteEtale.pullback
        (C.homOfLE (inf_le_left : (c ⁻¹ᵁ U) ⊓ (c ⁻¹ᵁ V) ≤ c ⁻¹ᵁ U))).obj PA ≅
        (FiniteEtale.pullback
        (C.homOfLE (inf_le_right : (c ⁻¹ᵁ U) ⊓ (c ⁻¹ᵁ V) ≤ c ⁻¹ᵁ V))).obj
          ((FiniteEtale.pullback (C.homOfLE (c.preimage_mono hVW))).obj R)) := by sorry

end AlgebraicGeometry.Scheme
