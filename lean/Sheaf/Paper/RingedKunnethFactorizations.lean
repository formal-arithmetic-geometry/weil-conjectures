/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q36
-/
module

public import Sheaf.Paper.RingedExchangeTensorCoherence
public import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.RingedComparisonTensorAdjunction

/-!
# The two factorizations of the ringed-topos external product

Source: Stacks Project, Cohomology on Sites, Tags 07A7, 0B56, 0D6E;
the First identity in the blueprint unit `sk-prop-p1-adjunction-rational`
(blueprint: lem-sfb-ringed-kunneth-factorizations).

The existing ringed tensor presentations allow arbitrary models of the derived
adjunctions, identified by the unique adjunction-compatible isomorphisms. In particular
the direct-image path comparison below is conjugation, exactly as in the proof of
Stacks Tag 0D6E. No exchange or projection map is inverted.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- Projection with the fixed factor first: the adjunct of identity tensor counit.
This is the usual projection map with tensor symmetry putting its factors in this order.
Source: Stacks Tag 0B56, equation-projection-formula-map
(blueprint: lem-sfb-ringed-kunneth-factorizations). -/
noncomputable def RingedTensorEdge.projectionFixedFirst
    {Y X : RingedTensorCorner.{u, w}} (f : RingedTensorEdge Y X)
    (aY : RingedTensorModel Y) (aX : RingedTensorModel X)
    (Q : DerivedCategory (SheafOfModules.{u}
      ((sheafCompose Y.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.ring)))
    (E : DerivedCategory (SheafOfModules.{u}
      ((sheafCompose X.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj X.ring))) :
    Y.tensor.obj (Q, f.right.obj E) ⟶ f.right.obj (X.tensor.obj (f.left.obj Q, E)) :=
  f.derivedAdjunction.homEquiv _ _
    ((f.tensorComparison aY aX).hom.app (Q, f.right.obj E) ≫
      X.tensor.map (CategoryTheory.Prod.mkHom (𝟙 (f.left.obj Q))
        (f.derivedAdjunction.counit.app E)))

namespace RingedKunneth

variable {Y X W : RingedTensorCorner.{u, w}}
  {q : RingedTensorEdge Y X} {a b : RingedTensorEdge X W}

/-- The opposite exchange map bar-beta: LR → SB, using the inverse comparison.
Source: Stacks Tag 07A7, remark-base-change
(blueprint: lem-sfb-ringed-kunneth-factorizations). -/
noncomputable def betaBar (s : RingedTensorSquare Y X X W q q a b) :
    q.right ⋙ q.left ⟶ b.left ⋙ a.right :=
  (mateEquiv q.derivedAdjunction a.derivedAdjunction
    (TwoSquare.mk q.left q.left a.left b.left s.derivedComparison.inv)).natTrans

/-- The canonical path comparison RS ≅ RU, obtained by uniqueness of right adjoints
from BL ≅ AL. This is the composition comparison of Stacks Tag 0D6E, whose proof
constructs it by precisely this conjugation of pullback composition comparisons.
Source: Stacks Tag 0D6E, lemma-derived-pushforward-composition
(blueprint: lem-sfb-ringed-kunneth-factorizations). -/
noncomputable def directComparison (s : RingedTensorSquare Y X X W q q a b) :
    a.right ⋙ q.right ≅ b.right ⋙ q.right :=
  conjugateIsoEquiv (q.derivedAdjunction.comp a.derivedAdjunction)
    (q.derivedAdjunction.comp b.derivedAdjunction) s.derivedComparison

variable (s : RingedTensorSquare Y X X W q q a b)
  (aY : RingedTensorModel Y) (aX : RingedTensorModel X) (aW : RingedTensorModel W)
  (M N : DerivedCategory (SheafOfModules.{u}
    ((sheafCompose X.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj X.ring)))

/-- First route: projection for q, beta tensor identity, then projection for b.
Its target is RU(AM tensor BN), before the canonical comparison with RS.
Source: Stacks Tags 07A7, 0B56; blueprint First identity
(blueprint: lem-sfb-ringed-kunneth-factorizations). -/
noncomputable def first :
    Y.tensor.obj (q.right.obj M, q.right.obj N) ⟶
      q.right.obj (b.right.obj (W.tensor.obj (a.left.obj M, b.left.obj N))) :=
  q.projectionFixedFirst aY aX (q.right.obj M) N ≫
    q.right.map (X.tensor.map (CategoryTheory.Prod.mkHom (s.exchange.app M) (𝟙 N)) ≫
      b.projection aX aW (a.left.obj M) N)

/-- Second route: projection for q, identity tensor bar-beta, then projection for a
with the fixed factor first. Its target is RS(AM tensor BN).
Source: Stacks Tags 07A7, 0B56; blueprint First identity
(blueprint: lem-sfb-ringed-kunneth-factorizations). -/
noncomputable def second :
    Y.tensor.obj (q.right.obj M, q.right.obj N) ⟶
      q.right.obj (a.right.obj (W.tensor.obj (a.left.obj M, b.left.obj N))) :=
  q.projection aY aX M (q.right.obj N) ≫
    q.right.map (X.tensor.map (CategoryTheory.Prod.mkHom (𝟙 M) ((betaBar s).app N)) ≫
      a.projectionFixedFirst aX aW M (b.left.obj N))

/-- The mixed tensor of the two original counits. The first two arrows are the tensor
comparison for AL; theta inverse changes the second factor from ALRN to BLRN.
Thus the source is (qa)* applied to RM tensor RN, in its composite pullback model.
Source: Stacks Tags 07A7, 0B56; the two-counit expansion of the blueprint First identity
(blueprint: lem-sfb-ringed-kunneth-factorizations). -/
noncomputable def commonTranspose :
    a.left.obj (q.left.obj (Y.tensor.obj (q.right.obj M, q.right.obj N))) ⟶
      W.tensor.obj (a.left.obj M, b.left.obj N) :=
  a.left.map ((q.tensorComparison aY aX).hom.app (q.right.obj M, q.right.obj N)) ≫
    (a.tensorComparison aX aW).hom.app
      (q.left.obj (q.right.obj M), q.left.obj (q.right.obj N)) ≫
    W.tensor.map (CategoryTheory.Prod.mkHom
      (a.left.map (q.derivedAdjunction.counit.app M))
      (s.derivedComparison.inv.app (q.right.obj N) ≫
        b.left.map (q.derivedAdjunction.counit.app N)))

end RingedKunneth

/-- The two projection/exchange factorizations agree, and their common transpose is
the displayed mixed tensor of the original q-counits.

Source: Stacks Tags 07A7, 0B56, 0D6E; blueprint First identity
(blueprint: lem-sfb-ringed-kunneth-factorizations).

Proof plan, following the node's six steps:
1. Apply lem-sfb-ringed-comparison-tensor-adjunction to the two paths (a,q), (b,q).
   Its tensor identity says theta intertwines the composite tensor comparisons d_B,d_A.
   Its adjunction compatibility identifies the canonical direct-image comparison with
   the conjugate used by directComparison (Stacks 0D6E).
2. The mate equations from def-weil-pbc-adjunction-mate give
   w_AM B(beta_M) = A(v_M) theta_RM and
   s_BN A(bar-beta_N) = B(v_N) theta_RN inverse.
3. Transpose first successively under q and b, using
   def-weil-pbc-composite-adjunction. The definition of projection from
   lem-weil-pbc-ringed-exchange-tensor-coherence, counit naturality, and naturality of
   the canonical tensor comparisons rewrite its transpose as
   (A(v_M) theta_RM tensor B(v_N)) d_B.
4. Transpose second under q and a. The same identities give
   (A(v_M) tensor B(v_N) theta_RN inverse) d_A.
5. Apply the tensor identity from step 1 and cancel theta on the first factor.
   The first transpose precomposed with theta inverse becomes the second transpose,
   precisely commonTranspose. This proves the second conjunct.
6. The conjugate comparison satisfies the composite-counit equation. Thus transporting
   first by directComparison inverse corresponds to precomposing its transpose with
   theta inverse. Injectivity of the composite hom-equivalence now proves the first
   conjunct. No beta, bar-beta or projection map is inverted, and neither a relation
   between M and N nor cartesianness, properness or boundedness is used. -/
theorem ringedKunnethFactorizations
    {Y X W : RingedTensorCorner.{u, w}}
    {q : RingedTensorEdge Y X} {a b : RingedTensorEdge X W}
    (s : RingedTensorSquare Y X X W q q a b)
    (aY : RingedTensorModel Y) (aX : RingedTensorModel X) (aW : RingedTensorModel W)
    (M N : DerivedCategory (SheafOfModules.{u}
      ((sheafCompose X.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj X.ring))) :
    (RingedKunneth.first s aY aX aW M N ≫
        (RingedKunneth.directComparison s).inv.app
          (W.tensor.obj (a.left.obj M, b.left.obj N)) =
      RingedKunneth.second s aY aX aW M N) ∧
    ((q.derivedAdjunction.comp a.derivedAdjunction).homEquiv _ _).symm
        (RingedKunneth.second s aY aX aW M N) =
      RingedKunneth.commonTranspose s aY aX aW M N := sorry

end SheafOfModules
