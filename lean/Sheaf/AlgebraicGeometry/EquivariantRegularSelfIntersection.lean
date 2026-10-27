/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q60
-/
module

public import Sheaf.AlgebraicGeometry.EquivariantTorLinearization
public import Sheaf.AlgebraicGeometry.RationalRepresentationGZero
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.RingTheory.RegularSequenceKoszulRegular
import WeilConjectures.RingTheory.KoszulNormalizedProjectiveResolution
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardAnnihilated
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.FinitePushforwardFiniteType
import WeilConjectures.AlgebraicGeometry.ClosedImmersionConormalFlatBaseChange

/-! # Equivariant regular self-intersection in integral coherent G-zero

Source: Milne, Algebraic Groups (iAG2017), Section 22d, Theorem 22.50, p.480,
agent-supplied prerequisite; Stacks 062F, 062I, 08BP and 0473 for the local argument.
(blueprint: lem-sfb-equivariant-regular-self-intersection)

The additive groups are actual integral quotients. Ring and module structures are
asserted to exist with their prescribed tensor normalization. All representatives
of pullback, pushforward, Tor and exterior powers are identified equivariantly by
the normalized operation predicates, so their choices do not affect these formulas.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.EquivariantCoherent

set_option maxHeartbeats 300000 in
-- This single signature elaborates several dependent integral quotients and derived models.
/-- Equivariant coherent regular self-intersection, including the empty immersion
and length-zero regular charts. There is no hypothesis on the ideal away from W.
Source: Milne iAG2017, Section 22d, Theorem 22.50, p.480 (agent prerequisite),
Stacks 062F, 062I, 08BP and 0473
(blueprint: lem-sfb-equivariant-regular-self-intersection).

Proof:
1. Finite type over the field makes Y and its closed subscheme W Noetherian
(lem-weil-pbc-finite-type-over-noetherian). On a regular affine chart the
regular-sequence Koszul complex is a finite free resolution, of length at most c
(lem-weil-pbc-regular-sequence-koszul-regular and
new-d3-koszul-normalized-projective-resolution). Thus Tor vanishes above c and is
coherent. The closed-immersion annihilated-pushforward equivalence descends these
Tor modules to W (lem-weil-pbc-closed-immersion-pushforward-annihilated and
pqf-lem-coherent-ft-locnoeth). Pulling the Tor linearization back along id_G × i
and using the normalized pullback composition gives its identity and cocycle.
The coefficient Koszul comparison gives local bases for the conormal bundle.
2. An equivariant short exact sequence gives a finite Tor long exact sequence
(lem-sfb-equivariant-coherent-tor-calculus). Splitting into images and cancelling
alternating image classes proves the alternating Tor formula respects G-zero
relations and defines the homomorphism gysin.
3. Tor commutes equivariantly with tensoring by an associated vector bundle.
Tensor is exact in the sheaf variable. A short exact sequence of representations
is split over F as vector spaces, so tensoring with any sheaf preserves its
underlying exactness and retains equivariant arrows. Thus the action descends
through both sets of Grothendieck relations and gysin is R(G)-linear. For a
locally finite free E, only degree-zero Tor remains, equal to i* E.
4. The closed immersion is finite and its pushforward is coherent and exact
(lem-weil-pbc-closed-immersion-finite, lem-pc-f3-finite-pushforward-finite-type).
The regular-quotient coefficient Tor comparison identifies Tor_q(O_W,i_* M)
with exteriorPower_q(I/I²) tensor M (lem-sfb-regular-quotient-coefficient-tor).
Its flat-base-change and presentation-independence properties glue these local
comparisons on overlaps.
5. Projection G × Y → Y is flat over the field, and the action is that projection
composed with the automorphism (g,y) ↦ (g,gy). Flat conormal base change
(lem-weil-pbc-closed-immersion-conormal-flat-base-change) and the normalized
coefficient Tor comparison identify both pullbacks of the local comparisons.
Their square with the given linearizations commutes; hence the glued
comparisons are equivariant. No invariant affine charts or equivariant regular
generators, smoothness, or reductivity are used.
6. Take finite alternating classes of these comparisons and extend from coherent
module classes through the relations. Tensor by each exterior bundle is exact.
This yields gysin(push alpha) = lambda alpha integrally. If W is empty all its
module classes vanish. For c = 0, the ideal on each chart is zero, the conormal
is zero, and exterior degree zero is O_W. These are the asserted degenerate cases.
-/
theorem equivariant_regular_self_intersection
    [∀ X : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (F : Type u) [Field F] (G Y W : Over (Spec (.of F)))
    [GrpObj G] [ModObj G Y] [ModObj G W]
    [IsAffine G.left] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (i : W ⟶ Y) [IsModHom G i] [IsClosedImmersion i.left]
    (c : ℕ)
    (hregular : ∀ w : W.left, ∃ U : Y.left.affineOpens,
      i.left w ∈ U.1 ∧ ∃ f : List Γ(Y.left, U.1),
        f.length ≤ c ∧ RingTheory.Sequence.IsRegular Γ(Y.left, U.1) f ∧
          Ideal.span {x : Γ(Y.left, U.1) | x ∈ f} = i.left.ker.ideal U) :
    ∃ (DY : ActionGroupoidModel G Y) (DW : ActionGroupoidModel G W)
      (AY : FlatDerivedModel (target G Y)) (PY : FlatDerivedModel (source G Y))
      (AW : FlatDerivedModel (target G W)) (PW : FlatDerivedModel (source G W))
      (r : CommRing (RepresentationGZero F Γ(G.left, ⊤)))
      (mY : @Module (RepresentationGZero F Γ(G.left, ⊤)) (GZero DY)
        r.toSemiring inferInstance)
      (mW : @Module (RepresentationGZero F Γ(G.left, ⊤)) (GZero DW)
        r.toSemiring inferInstance),
      IsRepresentationRing r ∧ IsRepresentationAction F DY r mY ∧
        IsRepresentationAction F DW r mW ∧
      ∃ (gysin : GZero DY →+ GZero DW) (push : GZero DW →+ GZero DY)
        (lambda : GZero DW →+ GZero DW),
        (∀ (M : Coherent DY) (q : ℕ), ∃ T : Coherent DW,
          IsTor (DY := DY) (DW := DW) i AY PY AW PW M q T) ∧
        (∀ (M : Coherent DY) (q : ℕ), c < q →
          IsZero (immersionTor (DY := DY) i M q)) ∧
        (∀ (M : Coherent DY) (T : Fin (c + 1) → Coherent DW),
          (∀ q, IsTor (DY := DY) (DW := DW) i AY PY AW PW M q.val (T q)) →
          gysin (classOf (D := DY) M) = ∑ q, (-1 : ℤ) ^ q.val • classOf (D := DW) (T q)) ∧
        (∀ (a : RepresentationGZero F Γ(G.left, ⊤)) (b : GZero DY),
          gysin (mY.smul a b) = mW.smul a (gysin b)) ∧
        (∀ N : Coherent DW, ∃ M : Coherent DY, IsPushforward (DY := DY) (DW := DW) i N M) ∧
        (∀ (N : Coherent DW) (M : Coherent DY), IsPushforward (DY := DY) (DW := DW) i N M →
          push (classOf (D := DW) N) = classOf (D := DY) M) ∧
        (∃ (K : Coherent DY) (N : Coherent DW),
          IsIdeal (D := DY) i.left K ∧ IsPullback (DY := DY) (DW := DW) i K N ∧
          SheafOfModules.IsLocallyFree (R := W.left.ringCatSheaf) (underlying (D := DW) N) ∧
          (∀ q : ℕ, ∃ E : Coherent DW, IsExterior (D := DW) N q E ∧
            SheafOfModules.IsLocallyFree (R := W.left.ringCatSheaf) (underlying (D := DW) E)) ∧
          (∀ (q : ℕ) (E : Coherent DW), c < q → IsExterior (D := DW) N q E →
            IsZero (underlying (D := DW) E)) ∧
          ∀ (M : Coherent DW) (E T : Fin (c + 1) → Coherent DW),
            (∀ q, IsExterior (D := DW) N q.val (E q)) →
            (∀ q, IsTensor (D := DW) (E q) M (T q)) →
            lambda (classOf (D := DW) M) = ∑ q, (-1 : ℤ) ^ q.val • classOf (D := DW) (T q)) ∧
        (∀ alpha : GZero DW, gysin (push alpha) = lambda alpha) ∧
        (∀ E : Coherent DY,
          SheafOfModules.IsLocallyFree (R := Y.left.ringCatSheaf) (underlying (D := DY) E) →
          (∃ Ew : Coherent DW, IsPullback (DY := DY) (DW := DW) i E Ew) ∧
          ∀ Ew : Coherent DW, IsPullback (DY := DY) (DW := DW) i E Ew →
            gysin (classOf (D := DY) E) = classOf (D := DW) Ew) := by
  sorry

end AlgebraicGeometry.EquivariantCoherent
