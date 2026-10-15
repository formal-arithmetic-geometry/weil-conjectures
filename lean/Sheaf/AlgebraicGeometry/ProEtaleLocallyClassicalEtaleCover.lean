/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
import Sheaf.RingTheory.IndPrincipalZariski
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import Sheaf.RingTheory.IndEtaleStability
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence
import Sheaf.AlgebraicGeometry.ProEtaleComparisonSections
import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory

/-!
# Locally classical pro-etale sheaves and etale-local sections

Source: Bhatt--Scholze, Definition 5.1.3, Lemmas 5.1.1--5.1.4 and Proposition 6.8.4(6)
(blueprint: lem-weil-pbc-proetale-locally-classical-etale-cover).

The three predicates spell out the notions introduced in this node. Restriction to
`U` is precomposition with the existing localization functor, which composes structure
maps with `U.hom`. Covering families use the actual small-site topologies.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- Restriction of set-valued sheaves to the small pro-etale site of a cover member.
It is precomposition with the canonical structure-map composition functor.
Source: Bhatt--Scholze, Lemma 5.1.4, restriction to a covering member
(blueprint: lem-weil-pbc-proetale-locally-classical-etale-cover). -/
def proEtaleSetRestriction (X : Scheme.{u}) (U : X.ProEt) :
    Sheaf (ProEt.topology X) (Type (u + 1)) ⥤
      Sheaf (ProEt.topology U.left) (Type (u + 1)) :=
  @Functor.sheafPushforwardContinuous U.left.ProEt _ X.ProEt _
    (MorphismProperty.Over.map (P := @WeaklyEtale) ⊤ U.prop)
    (Type (u + 1)) _ (ProEt.topology U.left) (ProEt.topology X)
    (ProEt.isContinuous_overMap U.prop)

/-- Classical means isomorphic to the canonical inverse image of an etale sheaf of sets.
Source: Bhatt--Scholze, Definition 5.1.3
(blueprint: lem-weil-pbc-proetale-locally-classical-etale-cover). -/
def IsProEtaleClassical (X : Scheme.{u}) (F : Sheaf (ProEt.topology X) (Type (u + 1))) :
    Prop :=
  ∃ G : Sheaf X.smallEtaleTopology (Type (u + 1)),
    Nonempty (F ≅ (Functor.sheafPullbackConstruction.sheafPullback (toProEt X)
      (Type (u + 1)) X.smallEtaleTopology (ProEt.topology X)).obj G)

/-- Local classicality uses a pro-etale cover and the sectionwise restriction to each
member's small pro-etale site, with no compatibility imposed on the etale presentations.
Source: Bhatt--Scholze, Lemma 5.1.4
(blueprint: lem-weil-pbc-proetale-locally-classical-etale-cover). -/
def IsProEtaleLocallyClassical (X : Scheme.{u})
    (F : Sheaf (ProEt.topology X) (Type (u + 1))) : Prop :=
  ∃ (I : Type (u + 1)) (U : I → X.ProEt), (ProEt.topology X).CoversTop U ∧
    ∀ i : I, IsProEtaleClassical (U i).left
      ((proEtaleSetRestriction X (U i)).obj F)

/-- Local constancy allows varying, possibly empty, sets on the members of a pro-etale
cover. The constant sheaves are sheafifications of constant presheaves.
Source: Bhatt--Scholze, Proposition 6.8.4(6)
(blueprint: lem-weil-pbc-proetale-locally-classical-etale-cover). -/
def IsProEtaleLocallyConstant (X : Scheme.{u})
    (F : Sheaf (ProEt.topology X) (Type (u + 1))) : Prop :=
  ∃ (I : Type (u + 1)) (U : I → X.ProEt), (ProEt.topology X).CoversTop U ∧
    ∀ i : I, ∃ S : Type (u + 1), Nonempty
      (((proEtaleSetRestriction X (U i)).obj F) ≅
          (constantSheaf (ProEt.topology (U i).left) (Type (u + 1))).obj S)

/-- Local classicality implies classicality, including for locally constant sheaves.
Local inhabitedness of such a sheaf can be witnessed by an etale cover. There is no
compatibility condition on the local sections, nor a nonemptiness condition on the
index sets or the constant value sets.

Source: Bhatt--Scholze, Lemmas 5.1.1--5.1.4 and Proposition 6.8.4(6)
(blueprint: lem-weil-pbc-proetale-locally-classical-etale-cover).

Proof plan:
1. Over an affine open, `lem-weil-pbc-comparison-sections` identifies the comparison
   counit on an affine ind-etale presentation with the restriction map from the colimit
   of the finite-stage sections. The basis in `lem-weil-pbc-ind-etale-basis` detects
   isomorphisms. The same formula on constant etale presentations makes the unit an
   isomorphism. Thus this continuity criterion is equivalent to classicality. These
   tests are Zariski local by `lem-weil-proetale-weakly-etale-localization`.
2. Refine the local classicality cover by finitely many affine ind-etale basis objects
   over each affine open. Use `lem-weil-pbc-comparison-pullback` to retain classicality.
   Write the sheaf equalizers for an ind-etale algebra C and its etale finite stages C_j.
   The tensor presentations are ind-etale by `lem-weil-pbc-ind-etale-stability`.
   Classicality on each cover member identifies the middle terms with filtered colimits.
   For the double intersections, present the second cover algebra by its etale stages
   and interchange the two filtered colimits. All identifications are restriction maps.
   Filtered colimits of sets commute with finite products and equalizers: finitely many
   representatives and equalities can be moved to a common later stage. The equalizers
   therefore give colim_j F(C_j) = F(C). Step 1 proves classicality locally, hence globally.
3. A constant sheaf is a coproduct of copies of the terminal sheaf. The inverse image
   preserves coproducts and the terminal object, so it takes constant etale sheaves to
   constant pro-etale sheaves. Local constancy therefore implies local classicality;
   apply step 2.
4. Write a locally classical F as the inverse image of G. Over each affine open refine
   a cover with sections by affine ind-etale basis objects. Each section is represented
   at an etale finite stage by the section formula. The comparison unit takes it to a
   section of F at that stage. The selected stages cover because each original basis
   object factors through its selected stage. Take these etale stages over all affine
   opens. On the empty scheme use the empty covering family. -/
theorem proEtale_locallyClassical_etaleCover (X : Scheme.{u})
    (F : Sheaf (ProEt.topology X) (Type (u + 1))) :
    (IsProEtaleLocallyClassical X F → IsProEtaleClassical X F) ∧
    (IsProEtaleLocallyConstant X F →
      IsProEtaleLocallyClassical X F ∧ IsProEtaleClassical X F) ∧
    (IsProEtaleLocallyClassical X F →
      (∃ (I : Type (u + 1)) (U : I → X.ProEt),
        (ProEt.topology X).CoversTop U ∧ ∀ i : I, Nonempty (F.obj.obj (op (U i)))) →
      ∃ (I : Type (u + 1)) (Y : I → X.Etale),
        X.smallEtaleTopology.CoversTop Y ∧
          ∀ i : I, Nonempty (F.obj.obj (op ((toProEt X).obj (Y i))))) := by
  sorry

end AlgebraicGeometry.Scheme
