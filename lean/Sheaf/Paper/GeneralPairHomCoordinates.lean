/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients

/-! # Normalized Hom coordinates on the intrinsic pair category

Source: blueprint `sec-six-functors-basics/sk-thm-sfb-qlbar-two-colimit/_section.md`,
clauses (2), (4), and the retained order-1462 literal-pair construction in
`Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`
(blueprint: lem-pur-general-pair-hom-coordinates).

All constructions below are the existing intrinsic ones: the fixed quotient pair category,
the associator-conjugated transports, the abelian-group direct limit, and the uniquely
representative-normalized coordinates. No second pair category or group structure is defined.
-/

@[expose] public section
set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace WeilConjectures.GeneralAlgebraicallyClosedCoefficients

attribute [local irreducible] stageCategory

/-- The full normalized Hom-colimit interface on the actual intrinsic pair category.
The two universe parameters for the scheme and the coefficient closure are independent.
The group used for sums and zero is the existing `homAddCommGroup`, defined by transfer
along `homCoordinates`, whose unique representative normalization is asserted below.

Source: blueprint `sec-six-functors-basics/sk-thm-sfb-qlbar-two-colimit/_section.md`,
clauses (2), (4); retained order-1462 Hom, additive and zero-object construction
(blueprint: lem-pur-general-pair-hom-coordinates).

Proof: the finite coefficient compositum makes every common-overfield index nonempty and
directed. The intrinsic rational stages are preadditive with zero objects; the normalized
scalar transitions are additive. Expanding transport as the scalar map conjugated by the
two associator components therefore proves additivity and preservation of zero. Naturality
and the associator cocycle give iterated transport. In particular reflexive transport is
idempotent. The normalized tensor unitor makes the reflexive scalar functor faithful;
cancelling the associator components makes reflexive transport injective. Its idempotence
then forces it to be the identity, giving the directed-system laws without strict unitors.

Send a quotient representative to its direct-limit class. Both equivalence relations are
equality after specified transport to a common later field, so this descends to a bijection.
The inverse sends a direct-limit representative back to its quotient class. Representative
induction proves both inverse identities and uniqueness of the normalized set equivalence.
Transfer the direct limit's abelian group along this equivalence. Since its structure maps
are homomorphisms, injectivity gives the displayed same-stage addition and zero formulas.
Represent any three arrows at one common field; finite-stage bilinearity proves both
composition equations. The inclusion sends an arrow to its reflexive scalar image, so
scalar additivity and the same-stage formula make every specified inclusion additive.

For a zero object Z at the bottom field, its identity is zero. The additive reflexive
transition preserves this equality, so the identity of the literal pair is the zero
representative. The same-stage zero formula and bilinearity make every arrow to or from
this pair zero; hence the pair is a zero object. Finally quotient induction supplies a
finite representative of every arrow, and the defining quotient relation gives exactly
the stated equality criterion at one common later field. None of these arguments uses
a finite-field structure on the scheme, noetherianity, or a Karoubi completion. -/
theorem pairHomCoordinates
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (Y : AlgebraicGeometry.Scheme.{u}) :
    (∀ A B : Pair l Ω Y,
      DirectedSystem (StageHom A B) (fun {L M} h ↦ transportHom A B L M h)) ∧
    (∀ A B : Pair l Ω Y,
      ∃! e : (A ⟶ B) ≃ ColimitHom A B,
        ∀ (L : Padic.FiniteCoefficientFields l Ω) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
          (f : StageHom A B ⟨L, hA, hB⟩),
          e (StageSystem.PairCategory.mkHom L hA hB f) = colimitOf A B L hA hB f) ∧
    (∀ (A B : Pair l Ω Y) (L : Padic.FiniteCoefficientFields l Ω)
        (hA : A.stage ≤ L) (hB : B.stage ≤ L)
        (f g : StageHom A B ⟨L, hA, hB⟩),
      ofHom A B L hA hB f + ofHom A B L hA hB g = ofHom A B L hA hB (f + g)) ∧
    (∀ (A B : Pair l Ω Y) (L : Padic.FiniteCoefficientFields l Ω)
        (hA : A.stage ≤ L) (hB : B.stage ≤ L),
      ofHom A B L hA hB (0 : StageHom A B ⟨L, hA, hB⟩) = 0) ∧
    (∀ (A B C : Pair l Ω Y) (f f' : A ⟶ B) (g : B ⟶ C),
      (f + f') ≫ g = f ≫ g + f' ≫ g) ∧
    (∀ (A B C : Pair l Ω Y) (f : A ⟶ B) (g g' : B ⟶ C),
      f ≫ (g + g') = f ≫ g + f ≫ g') ∧
    (∀ E : Padic.FiniteCoefficientFields l Ω,
      (inclusion E : Stage l Ω Y E ⥤ Pair l Ω Y).Additive) ∧
    (∀ Z : Stage l Ω Y (Padic.finiteCoefficientBase l Ω),
      IsZero Z → IsZero (⟨Padic.finiteCoefficientBase l Ω, Z⟩ : Pair l Ω Y)) ∧
    (∀ (A B : Pair l Ω Y) (f : A ⟶ B),
      ∃ (L : Padic.FiniteCoefficientFields l Ω) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
        (g : StageHom A B ⟨L, hA, hB⟩), f = ofHom A B L hA hB g) ∧
    (∀ (A B : Pair l Ω Y) (L M : Common A B) (f : StageHom A B L) (g : StageHom A B M),
      ofHom A B L.val L.property.1 L.property.2 f =
          ofHom A B M.val M.property.1 M.property.2 g ↔
        ∃ (N : Common A B) (hL : L ≤ N) (hM : M ≤ N),
          transport A B L N hL f = transport A B M N hM g) := by
  have he (A B : Pair l Ω Y) (L : Padic.FiniteCoefficientFields l Ω)
      (hA : A.stage ≤ L) (hB : B.stage ≤ L) (f : StageHom A B ⟨L, hA, hB⟩) :
      homCoordinates A B (ofHom A B L hA hB f) = colimitOf A B L hA hB f :=
    (homCoordinates_existsUnique A B).exists.choose_spec L hA hB f
  refine ⟨transportSystem, homCoordinates_existsUnique, ?_, ?_,
    composition_bilinear.1, composition_bilinear.2, inclusion_additive, ?_, ?_, ?_⟩
  · intro A B L hA hB f g
    apply (homCoordinates A B).injective
    rw [show homCoordinates A B (_ + _) = homCoordinates A B _ + homCoordinates A B _
      from (homCoordinates A B).addEquiv.map_add _ _]
    rw [he A B L hA hB f, he A B L hA hB g, he A B L hA hB (f + g)]
    exact (map_add (AddCommGroup.DirectLimit.of (StageHom A B) (transportHom A B)
      ⟨L, hA, hB⟩) f g).symm
  · intro A B L hA hB
    apply (homCoordinates A B).injective
    rw [show homCoordinates A B (0 : A ⟶ B) = 0
      from (homCoordinates A B).addEquiv.map_zero]
    rw [he A B L hA hB 0]
    exact map_zero (AddCommGroup.DirectLimit.of (StageHom A B) (transportHom A B)
      ⟨L, hA, hB⟩)
  · intro Z hZ
    exact Functor.map_isZero (inclusion (Padic.finiteCoefficientBase l Ω)) hZ
  · intro A B
    exact (representatives A B).1
  · intro A B
    exact (representatives A B).2

end WeilConjectures.GeneralAlgebraicallyClosedCoefficients
