/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality
import Sheaf.AlgebraicGeometry.Morphisms.FiniteEtaleStalkModelDescent
import Sheaf.AlgebraicGeometry.Morphisms.FiniteEtaleStalkComparisonDescent

/-!
# Spreading a finite etale stalk model and its comparison

Source: Stacks Project, Tags 0BQ5 and 0EY3.
(blueprint: lem-sbc-finite-etale-stalk-neighbourhood-spreading)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A finite etale model over a stalk with a comparison on an open spreads locally.

Source: Stacks Project, Tags 0BQ5 (limits-lemma-glueing-near-point) and
0EY3 (limits-lemma-glueing-near-point-properties), applied relative to C.
(blueprint: lem-sbc-finite-etale-stalk-neighbourhood-spreading)

Proof:
Write Spec O(S,s) as the inverse limit of affine open neighbourhoods W of s.
Their base changes C_W form a qcqs inverse system with affine transitions,
using the qcqs finite-presentation morphism c. Finite etale Q is finitely
presented over its local base and therefore descends to some C_W. Finiteness
and etaleness descend after shrinking W, by 0EY3 and its limit lemmas.
The intersections U intersect W are quasi-compact, since S is Noetherian.
Their base changes form a qcqs inverse system whose limit is the local overlap.
Descend the given comparison isomorphism e and its inverse over this system;
finite presentation descends their two identity equations after further shrinking.
This is the relative comparison part of 0BQ5. We obtain a finite etale model R
and an isomorphism on C_U intersect C_W. Identify the two open projections
with C.homOfLE inf_le_left and C.homOfLE inf_le_right to get the stated iso.
This works for the empty overlap as well; no torsor, section, integral base,
or restriction on the position of s is needed. No gluing over U union W
is part of the conclusion. -/
theorem FiniteEtale.exists_neighbourhood_model_of_stalk {S C : Scheme.{u}}
    [IsNoetherian S] [QuasiSeparatedSpace S]
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [LocallyOfFinitePresentation c]
    (U : S.Opens) (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale) (s : S)
    (Q : (Limits.pullback c (S.fromSpecStalk s)).FiniteEtale)
    (e : Nonempty ((FiniteEtale.pullback
      (pullback.fst (c ⁻¹ᵁ U).ι (pullback.fst c (S.fromSpecStalk s)))).obj PA ≅
      (FiniteEtale.pullback
      (pullback.snd (c ⁻¹ᵁ U).ι (pullback.fst c (S.fromSpecStalk s)))).obj Q)) :
    ∃ (W : S.Opens), s ∈ W ∧
      ∃ R : (c ⁻¹ᵁ W).toScheme.FiniteEtale,
        Nonempty ((FiniteEtale.pullback
          (C.homOfLE (inf_le_left : (c ⁻¹ᵁ U) ⊓ (c ⁻¹ᵁ W) ≤ c ⁻¹ᵁ U))).obj PA ≅
          (FiniteEtale.pullback
          (C.homOfLE (inf_le_right : (c ⁻¹ᵁ U) ⊓ (c ⁻¹ᵁ W) ≤ c ⁻¹ᵁ W))).obj R) := by
  by_cases hsU : s ∈ U
  · exact ⟨U, hsU, PA, ⟨Iso.refl _⟩⟩
  obtain ⟨W, hsW, R, l, hl, ⟨a⟩⟩ :=
    FiniteEtale.exists_stalk_neighbourhood_model c s Q
  obtain ⟨e⟩ := e
  let F := FiniteEtale.pullback
    (pullback.snd (c ⁻¹ᵁ U).ι (pullback.fst c (S.fromSpecStalk s)))
  have comparison : Nonempty (_ ≅ F.obj ((FiniteEtale.pullback l).obj R)) :=
    ⟨e ≪≫ (F.mapIso a).symm⟩
  obtain ⟨V, hVW, hsV, hV⟩ :=
    FiniteEtale.exists_neighbourhood_comparison_of_stalk c U W PA s hsW R l hl comparison
  exact ⟨V, hsV, (FiniteEtale.pullback (C.homOfLE (c.preimage_mono hVW))).obj R, hV⟩

end AlgebraicGeometry.Scheme
