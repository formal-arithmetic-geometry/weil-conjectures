/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.CategoryTheory.SheafTensor
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import WeilConjectures.CategoryTheory.PushoutShortExactSequence
import Mathlib.CategoryTheory.Abelian.Basic
import Sheaf.CategoryTheory.YonedaDerivedExtComparison
import Sheaf.Paper.IndConstructibleFilteredColimits

/-!
# Extensions of ind-constructible module sheaves

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-ind-heart,
`sk-prop-ind-heart-extensions.md` and its proof (blueprint: det-ind-heart-extensions).

The two coefficient cases use the existing finite constant-model constructibility predicate.
IndCons is `ObjectProperty.ind.{u + 1}` in the internal-module category itself, with small
filtered presentations and closure under isomorphisms. No abstract ind-category replaces
this ambient category.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Extensions of ind-constructible sheaves with finite field coefficients are
ind-constructible. Source: blueprint sk-prop-ind-heart-extensions, with the Noetherian
setting of det-ind-heart-extensions (blueprint: det-ind-heart-extensions).

Proof:
1. By sk-def-sfb-sheaf-tensor and lem-weil-pbc-sheaf-tensor-closed the ambient abelian
sheaves have closed symmetric additive tensor and are Grothendieck. The commutative ring
object and lem-sfb-modobj-grothendieck make their module category Grothendieck abelian;
def-sp-grothendieck-abelian supplies small colimits and exact filtered colimits.
2. Choose filtered constructible presentations N = colim D_i and B = colim C_a.
Pull the given short exact sequence back along each C_a → B, obtaining M_a.
Use lem-weil-pbc-pushout-short-exact-sequence in the opposite abelian category
(def-sp-abelian) for exactness. Pullback uniqueness makes the M_a a diagram over a.
3. The degree-one lem-coef-yoneda-derived-ext-comparison gives its class in Ext¹(C_a,N).
The field-coefficient clause of sk-lem-constructible-ext-continuity applies to the
uniformly degree-zero diagram D_i and identifies this Ext group with colim Ext¹(C_a,D_i).
4. Every element of a filtered colimit of abelian groups comes from one stage: write it
as a finite sum of stage elements and move them to a common stage. Descend the extension
class to an extension 0 → D_i → T → C_a → 0. Its pushout L = N ⨿_{D_i} T is exact by
lem-weil-pbc-pushout-short-exact-sequence and has the class of M_a by naturality of the
Yoneda comparison. The equivalence zigzag consists of isomorphisms by
lem-weil-pbc-short-five-lemma, so L and M_a are isomorphic as extensions.
5. The undercategory i/I is small, nonempty and filtered: common successors and then
equalizers in I give common successors under i; equalizers in I equalize parallel arrows.
Its target diagram D_j has colimit N. Indeed a cocone extends uniquely to I by choosing
common successors of i and each k; common successors and equalizers prove independence
and compatibility. The constant T diagram has colimit T since i/I is connected.
6. For u : i → j form P_u = D_j ⨿_{D_i} T. Each lies in an exact sequence with endpoints
D_j and C_a by lem-weil-pbc-pushout-short-exact-sequence, so is constructible by
det-lem-coefficient-heart-closure. Pushout uniqueness gives the transition functor.
7. A cocone from P_u is exactly a compatible family from D_j and a single map from T
agreeing on D_i, since the identity of i is initial in i/I. By step 5 these are exactly
maps from N ⨿_{D_i} T. The colimit universal property in def-weil-pbc-category-colimit
therefore exhibits L, and hence M_a, as a filtered colimit of constructibles.
8. Exact filtered colimits give 0 → N → colim M_a → B → 0. The canonical comparison to
the original extension is identity on endpoints, hence an isomorphism by
lem-weil-pbc-short-five-lemma. For the filtered-colimit closure used by
det-ind-heart-filtered-colimits at this Noetherian generality, degree-zero
sk-lem-constructible-ext-continuity says that constructibles are finitely presentable.
Mathlib ObjectProperty.ind_ind therefore flattens the resulting ind-of-ind presentation.
Isomorphism invariance gives the assertion. -/
theorem indConstructible_of_shortExact
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (S : ShortComplex (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X)))
    (hS : S.ShortExact)
    (hN : ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X) S.X₁)
    (hB : ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X) S.X₃) :
    ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X) S.X₂ := by
  sorry

/-- Extensions of ind-constructible sheaves with condensed algebraic-closure coefficients
are ind-constructible. Source: blueprint sk-prop-ind-heart-extensions, with the Noetherian
setting of det-ind-heart-extensions (blueprint: det-ind-heart-extensions).

Proof:
1. The abelian sheaf tensor of sk-def-sfb-sheaf-tensor is closed symmetric additive and
Grothendieck by lem-weil-pbc-sheaf-tensor-closed. Apply lem-sfb-modobj-grothendieck to
the commutative coefficient ring; def-sp-grothendieck-abelian gives exact filtered colimits.
2. Write N = colim D_i and B = colim C_a with constructible stages. Pull back over C_a;
lem-weil-pbc-pushout-short-exact-sequence in the opposite abelian category gives
0 → N → M_a → C_a → 0, and uniqueness gives the transition maps in a.
3. Use lem-coef-yoneda-derived-ext-comparison in degree one and
sk-lem-constructible-ext-continuity for the allowed field coefficient and the uniformly
zero-below-zero complexes D_i[0], giving Ext¹(C_a,N) = colim Ext¹(C_a,D_i).
4. A colimit class comes from a stage by filteredness and finite support. Represent it
by 0 → D_i → T → C_a → 0, then push out to N using
lem-weil-pbc-pushout-short-exact-sequence. Naturality of the Yoneda comparison identifies
the resulting class with that of M_a. The endpoint-fixed equivalence zigzag has invertible
middle maps by lem-weil-pbc-short-five-lemma, giving N ⨿_{D_i} T ≅ M_a.
5. The small undercategory i/I is filtered: it contains the identity; common successors
follow by taking successors in I and equalizing the two maps from i; parallel morphisms
are equalized in I. Its target diagram has colimit N: extend cocones using common
successors with i, and prove independence and compatibility by further equalizers.
6. The pushouts P_u = D_j ⨿_{D_i} T for u : i → j form a functor by uniqueness. They
are extensions of C_a by D_j by lem-weil-pbc-pushout-short-exact-sequence, hence
constructible by det-lem-coefficient-heart-closure.
7. Cocones on P_u are compatible maps from D_j and one map from T agreeing on D_i:
the maps from T coincide since the identity of i is initial. Step 5 identifies this
with the pushout universal property of N ⨿_{D_i} T. Thus M_a is ind-constructible.
8. Take the exact filtered colimit of the pullback sequences. Its endpoints are N and B,
since a filtered category is nonempty and connected. Its comparison to the given sequence
is an isomorphism by lem-weil-pbc-short-five-lemma. For the filtered-colimit closure of
det-ind-heart-filtered-colimits at this Noetherian generality, degree-zero
sk-lem-constructible-ext-continuity makes constructibles finitely presentable. Mathlib
ObjectProperty.ind_ind flattens the ind-of-ind presentation. Invariance under isomorphism
then gives the conclusion. -/
theorem indConstructible_of_shortExact_padicAlgCl
    (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (S : ShortComplex (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)))
    (hS : S.ShortExact)
    (hN : ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X) S.X₁)
    (hB : ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X) S.X₃) :
    ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X) S.X₂ := by
  sorry

end AlgebraicGeometry.ProEtale
