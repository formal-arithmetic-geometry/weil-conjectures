/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.Paper.CoefficientHeart
import Sheaf.Paper.IndHeartCanonicalPresentation

/-!
# Filtered colimits and sums of ind-constructible module sheaves

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-ind-heart,
`sk-prop-ind-heart-filtered-colimits.md` and its proof
(blueprint: det-ind-heart-filtered-colimits).

The standing geometric hypotheses are those of `sk-def-sfb-dc-setting`.
`ObjectProperty.ind.{u + 1}` of `IsConstantModelConstructible` is precisely IndCons:
small filtered presentations in the actual internal-module category, closed under isomorphism.
The two statements cover respectively a finite coefficient subextension and the condensed
algebraic closure. Coproducts are stated using arbitrary colimit cofans, including the empty one.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- For finite `E/ℚ_ℓ`, IndCons is closed under ambient filtered colimits and arbitrary sums.
Source: blueprint main-20261015, sk-prop-ind-heart-filtered-colimits, both assertions;
standing setting: sk-def-sfb-dc-setting (blueprint: det-ind-heart-filtered-colimits).

Proof: Form the category K of pairs (i, C → B_i), with C constructible, and morphisms
(u, f) satisfying f ≫ c' = c ≫ B.map u. By det-ind-heart-canonical-presentation each fibre
J(B_i) is essentially small and filtered, and its tautological cocone presents B_i.
Since I is small, representatives in all the fibres give a set of representatives in K;
its homs are sets of pairs, so a small skeleton may be used. K is nonempty. Common successors
are obtained by moving two indices to a common successor in I and then using filteredness
of its fibre. Equalize parallel base arrows first in I, then the two remaining arrows in
that fibre; the resulting pair equalizes the original parallel arrows in K.
Restricting a cocone on K to each fibre gives unique maps B_i → M. The arrows (u, id)
make these maps compatible with I. Conversely a compatible family gives the cocone with
legs C → B_i → M. These constructions are inverse, so the given ambient colimit is the
small filtered colimit of the constructible objects indexed by K.
For sums, choose filtered presentations for each summand in a finite subsum. Their finite
product index is filtered, and finite sums of constructibles are constructible by
sk-lem-coefficient-heart: zero is constructible, and the split short exact sequence gives
closure under binary sums. Restriction to summands identifies cocones on the product diagram
with maps from each B_s, since common successors make each map independent of the other
coordinates. Thus its colimit is the finite subsum, which is ind-constructible. The empty
product is the one-object category with zero diagram. Finally the finite subsets of the
arbitrary index set form a nonempty filtered poset under union, and singleton maps identify
its finite-subsum colimit with the arbitrary sum. Apply the first assertion to this diagram;
this includes the empty sum. -/
theorem indConstructible_filteredColimits_and_sums
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpl : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] :
    (∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
      (B : I ⥤ CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E) X))
      (c : Cocone B), IsColimit c →
      (∀ i : I, ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X) (B.obj i)) →
      ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X) c.pt) ∧
    (∀ (S : Type (u + 1))
      (B : S → CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E) X))
      (c : Cofan B), IsColimit c →
      (∀ s : S, ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X) (B s)) →
      ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X) c.pt) := by
  sorry

/-- For the condensed algebraic closure, IndCons is closed under ambient filtered colimits
and arbitrary sums. Source: blueprint main-20261015, sk-prop-ind-heart-filtered-colimits,
both assertions; standing setting: sk-def-sfb-dc-setting
(blueprint: det-ind-heart-filtered-colimits).

Proof: As in the finite coefficient case, use det-ind-heart-canonical-presentation to
present each B_i by its essentially small filtered category J(B_i) of constructible arrows.
The pair category K has a small skeleton: I is small and the fibres have sets of
representatives and set-valued homs. It is nonempty; choose common successors first in I
and then in the common fibre. Equalize parallel base arrows in I, then equalize their
constructible components in the resulting fibre. Cocones on K restrict to cocones on
J(B_i), hence to unique maps B_i → M; the arrows (u, id) force transition compatibility.
Conversely those compatible maps give all cocone legs by composition. These inverse
constructions identify the colimit of the constructible diagram on K with the given
ambient colimit, establishing the filtered-colimit assertion.
For a finite subsum, take the product of the summands' filtered presentation categories.
It is filtered coordinatewise, including the empty product. Its diagram consists of finite
sums of constructibles, which are constructible by sk-lem-coefficient-heart and the split
short exact sequence; the empty sum is zero. Maps on each summand are independent of the
other coordinates by common successors, so the product diagram has colimit the finite
subsum. Finally the finite-subset poset is nonempty and filtered by union. Maps from its
finite subsums are precisely families of maps from the individual summands, so its colimit
is the arbitrary sum, also for an empty family. Apply the filtered-colimit assertion. -/
theorem indConstructible_filteredColimits_and_sums_padicAlgCl
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpl : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] :
    (∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
      (B : I ⥤ CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
      (c : Cocone B), IsColimit c →
      (∀ i : I, ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X) (B.obj i)) →
      ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X) c.pt) ∧
    (∀ (S : Type (u + 1))
      (B : S → CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
      (c : Cofan B), IsColimit c →
      (∀ s : S, ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X) (B s)) →
      ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X) c.pt) := by
  sorry

end AlgebraicGeometry.ProEtale
