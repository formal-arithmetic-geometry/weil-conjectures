/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.KummerGCover
public import Sheaf.AlgebraicGeometry.VeryTameFSLogAction
import Sheaf.AlgebraicGeometry.VeryTameLogQuotient
import WeilConjectures.RingTheory.StrictHenselizationNoetherian
import WeilConjectures.AlgebraicGeometry.FinitePushforwardSetStalk
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.IndEtaleStrictLocalInvariance
import Sheaf.TraceFormula.LogRegularDivisorialStructure
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective

/-! # Kummer etale group covers after fs base change

Source: ILO VI 2.1--2.3 and Theorem 3.2, VIII 5.3.8, X 1.8
(blueprint: lem-per-kummer-g-cover-fs-base-change).

All products are specified by the existing fs universal property. Every representative
is a locally Noetherian fs log scheme. The quotient identifications are the canonical
pullback maps in `IsQuotient`, not independently chosen sheaf isomorphisms.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- Every locally Noetherian fs base change has its uniquely induced action, remains
 a Kummer etale group cover, and is the invariant log and scheme quotient with orbit
 geometric fibres. `IsQuotient` specifies both invariant-sheaf identifications by
 the canonical pullbacks. Source: ILO VI 2.3 and X 1.8
(blueprint: lem-per-kummer-g-cover-fs-base-change). -/
def FSLogGroupAction.HasKummerQuotientsAfterFSBaseChange {G : Type v} [Group G] [Finite G]
    {C D : FineSaturatedLogScheme.{u}} (a : FSLogGroupAction G C)
    (q : EtaleLogHom C D) : Prop :=
  ∀ B : FSLogBaseChange q, ∃! b : FSLogGroupAction G B.total,
    B.IsInducedAction a b ∧ b.IsKummerGCover B.snd ∧ b.IsQuotient B.snd ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (x z : Spec (.of Ω) ⟶ B.total.scheme),
        x ≫ B.snd.base = z ≫ B.snd.base ↔ ∃ g : G, x ≫ (b.baseAction g).hom = z

/-- Canonical fs comparisons, identity, composition, and the isomorphism between
successive and direct fs base changes. Comparison equations are equations of full
log morphisms: they give compatibility of ring and log pullbacks, hence of the
canonical invariant quotient identifications. No ordinary-scheme base-change
identification is asserted. Source: ILO X 1.8, diagram (1.a)
(blueprint: lem-per-kummer-g-cover-fs-base-change). -/
structure FSLogGroupAction.FSBaseChangeCoherence {G : Type v} [Group G]
    {C D : FineSaturatedLogScheme.{u}} (a : FSLogGroupAction G C)
    (q : EtaleLogHom C D) : Prop where
  comparison : ∀ (B B' : FSLogBaseChange q) (h : EtaleLogHom B'.base B.base),
    h.CompEq B.map B'.map → ∃! r : EtaleLogHom B'.total B.total, B.IsComparison B' h r
  equivariant : ∀ (B B' : FSLogBaseChange q) (h : EtaleLogHom B'.base B.base)
    (b : FSLogGroupAction G B.total) (b' : FSLogGroupAction G B'.total)
    (r : EtaleLogHom B'.total B.total), h.CompEq B.map B'.map →
    B.IsInducedAction a b → B'.IsInducedAction a b' → B.IsComparison B' h r →
      b'.IsEquivariant b r
  identity : ∀ (B : FSLogBaseChange q) (r : EtaleLogHom B.total B.total),
    B.IsComparison B (EtaleLogHom.id B.base) r → r.IsIdentity
  composition : ∀ (B₁ B₂ B₃ : FSLogBaseChange q)
    (h₂₁ : EtaleLogHom B₂.base B₁.base) (h₃₂ : EtaleLogHom B₃.base B₂.base)
    (r₂₁ : EtaleLogHom B₂.total B₁.total) (r₃₂ : EtaleLogHom B₃.total B₂.total)
    (r₃₁ : EtaleLogHom B₃.total B₁.total),
    h₂₁.CompEq B₁.map B₂.map → h₃₂.CompEq B₂.map B₃.map →
    B₁.IsComparison B₂ h₂₁ r₂₁ → B₂.IsComparison B₃ h₃₂ r₃₂ →
    B₁.IsComparison B₃ (h₃₂.comp h₂₁) r₃₁ → r₃₂.CompEq r₂₁ r₃₁
  iterated : ∀ (B : FSLogBaseChange q) (W : FSLogBaseChange B.snd)
    (T : FineSaturatedLogScheme.{u}) (p : EtaleLogHom T C) (s : EtaleLogHom T W.base),
    p.IsFSPullback q s (W.map.comp B.map) →
      ∃! i : EtaleLogHom W.total T,
        i.CompEq p (W.fst.comp B.fst) ∧ i.CompEq s W.snd ∧
          ∃ j : EtaleLogHom T W.total, i.AreInverses j

/-- Kummer etale group covers remain covers and invariant log quotients after every
locally Noetherian fs base change, compatibly with composition. The group order is
invertible at every point of the base. Source: ILO X 1.8, pp.146--147, and VI 2.3.
(blueprint: lem-per-kummer-g-cover-fs-base-change).

Proof plan:
1. Lift each action map by the fs product universal property
   [lem-per-fs-product-finite-comparison]. Projection equality gives the action
   laws. Base change of the disjoint-union diagonal is the new diagonal.
2. Apply [lem-per-kummer-etale-fs-base-change-stability] to obtain log etaleness
   and the Kummer condition, with no flatness or strictness hypothesis.
3. The fs comparison is finite surjective, and the ordinary projection is finite
   surjective [lem-per-fs-product-finite-comparison, lem-trf-finite-radicial-basechange].
4. Strictly localize at a geometric base point. Noetherianity follows from
   [lem-sc-strict-henselization-noetherian]. The standard local models
   [lem-per-kummer-strict-local-standard-model] and the diagonal show that the
   group permutes components transitively and each stabilizer is its standard
   character group.
5. Evaluate invariant tuples on a fixed component. Its character invariants are
   the base ring and base log structure by the same standard-model node. Finite
   pushforward stalks [lem-weil-pbc-sets-finite-pushforward-stalk] and conservativity
   [lemma-openclosed-point-ulift] descend both canonical identifications.
6. The component transitivity gives orbit geometric fibres. On affine quotient
   opens finiteness and the invariant ring identity identify the scheme quotient
   [lem-per-tame-admissible-scheme-quotient]; these identifications glue uniquely.
10. Successive products represent the same compatible maps. Their unique
   comparisons are inverse, are equivariant, and obey identity and composition
   because their projections do. Canonical ring and log pullbacks compose by
   functoriality [def-trf-fs-log-blowup]. This proves quotient compatibility too.
The very-tame application is stated separately below (Steps 7--9). -/
theorem kummerGCover_fs_baseChange {G : Type v} [Group G] [Finite G]
    {C D : FineSaturatedLogScheme.{u}} (a : FSLogGroupAction G C)
    (q : EtaleLogHom C D)
    (horder : ∀ d : D.scheme, IsUnit (Nat.card G : D.scheme.presheaf.stalk d))
    (hcover : a.IsKummerGCover q) :
    a.HasKummerQuotientsAfterFSBaseChange q ∧ a.FSBaseChangeCoherence q := by
  sorry

/-- The very tame finite quotient is a Kummer group cover when the action is free
on the log triviality locus, and therefore has the same fs base-change conclusions.
The admissible, generically free, Noetherian log regular setting and the invariant
quotient are exactly those of `exists_veryTame_logQuotient`.
Source: ILO VI Theorem 3.2 and 3.5(c); VIII 5.3.8; X 1.8
(blueprint: lem-per-kummer-g-cover-fs-base-change).

Proof plan:
7. The very-tame quotient theorem [lem-per-very-tame-log-quotient] gives finite
   surjectivity and Kummer etaleness. At a strictly localized base its standard
   components [lem-per-kummer-strict-local-standard-model] are permuted transitively.
   Their stabilizer H acts through the standard character group Gamma. The log
   stalk of the quotient is the H-invariant log stalk
   [lem-per-finite-quotient-strict-local-invariants].
8. Strict localization preserves log regularity
   [lem-trf-ind-etale-strict-local-invariance], so every component has a nonempty
   log-trivial locus [lem-trf-log-regular-divisorial-structure]. Freeness there
   kills the kernel of H to Gamma. A character class annihilated by its image has
   an invariant chart section; log invariants force that section to come from the
   base chart. Thus the annihilator is zero and H maps onto Gamma
   [lem-per-finite-character-annihilator-duality]. The actual diagonal is the
   standard diagonal.
9. Both diagonal schemes are finite over the base. The strict-local diagonal
   isomorphisms descend using finite pushforward stalks and geometric-point
   conservativity [lem-weil-pbc-sets-finite-pushforward-stalk,
   lemma-openclosed-point-ulift]. The same stalk test identifies the log maps.
   This gives the G-cover diagonal. Apply Steps 1--6 and 10 of the preceding
   theorem for all base changes and their composition. -/
theorem veryTame_logQuotient_isKummerGCover {G : Type v} [Group G] [Finite G]
    {C D : FineSaturatedLogScheme.{u}} [IsNoetherian C.scheme]
    (a : FSLogGroupAction G C) (q : EtaleLogHom C D)
    (hadmissible : ∀ x : C.scheme, ∃ U : C.scheme.Opens, x ∈ U ∧ IsAffineOpen U ∧
      ∀ (g : G) (z : C.scheme), (a.baseAction g).hom z ∈ U ↔ z ∈ U)
    (hgeneric : a.IsGenericallyFree) (hregular : C.IsLogRegular)
    (hverytame : a.IsVeryTame) (hquotient : a.IsQuotient q)
    (horder : ∀ d : D.scheme, IsUnit (Nat.card G : D.scheme.presheaf.stalk d))
    (hfree : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (x : Spec (.of Ω) ⟶ C.scheme) (g : G),
      x default ∈ C.logStructure.trivialityLocus → x ≫ (a.baseAction g).hom = x → g = 1) :
    a.IsKummerGCover q ∧ a.HasKummerQuotientsAfterFSBaseChange q ∧
      a.FSBaseChangeCoherence q := by
  sorry

end AlgebraicGeometry
