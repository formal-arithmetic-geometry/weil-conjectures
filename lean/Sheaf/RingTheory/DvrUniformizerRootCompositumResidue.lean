/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-! # Tame residue separability over a uniformizer-root base

Source: Stacks Project, Tags 0BRM (the last two paragraphs), 09EV, 09EQ and 09E7.
(blueprint: lem-sbc-dvr-uniformizer-root-compositum-residue) -/

@[expose] public section

universe u
namespace RingTheory

/-- The root case of tame ramification cancellation, including further DVR base change.

Source: Stacks Project, Tag 0BRM, the paragraphs after the unit-root claim,
with Tags 09EV (uniformizer root), 09EQ (further base change), and 09E7.
(blueprint: lem-sbc-dvr-uniformizer-root-compositum-residue)

Proof: The ring maps to the specified fraction fields are injective. Embed
Frac(B) into Frac(A) compatibly with B and let K0 be the intermediate field
it generates with theta. Since theta^e = pi and pi is a uniformizer, the
Eisenstein root theorem 09EV identifies the normalization of B in K0 with
the DVR B[theta]; its ramification index is e and its residue field is k(B).
Choose a uniformizer q of U. The index hypothesis writes pi = w*q^e for a
unit w of U. In E tensor_Frac(B) K0, theta/q satisfies X^e-w. This is a unit-root
polynomial with invertible derivative, so the normalization of U in each field
factor is a local factor of a finite etale U-algebra. Its ramification index
is one over U and its residue field is finite separable over k(U). Multiplicativity
in the two towers over B gives index one over B[theta]. Transitivity with the
assumed separability k(U)/k(B) gives separability over the residue field of
B[theta]. This is the adic formal smoothness criterion 09E7. Base change now
from K0 to Frac(A): the tensor of the weakly unramified normalization with A
has special fibre a product of finite separable extensions of k(A), as in 09EQ.
The uniformizer of A is a nonzerodivisor in this tensor, so each of its local
factors above the closed point is a DVR and is already normal. The compatible
maps and the generation hypothesis select the factor whose fraction field is F.
The DVR T equals this local factor: both are valuation rings in F and the map is
local, and a proper overring of a DVR in its fraction field is the field itself.
Consequently its residue extension over k(A) is separable. The tensor argument
works for any DVR A containing theta, without finiteness of A over B. When e=1,
B[theta]=B and the same argument is just weakly unramified base change. -/
theorem dvr_uniformizer_root_compositum_residue_isSeparable
    (B : Type u) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (pi : B) (hpi : Irreducible pi)
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra B A]
    (U : Type u) [CommRing U] [IsDomain U] [IsDiscreteValuationRing U]
    [Algebra B U] [IsLocalHom (algebraMap B U)]
    (e : ℕ) (he : IsUnit (e : B))
    (theta : A) (hroot : theta ^ e = algebraMap B A pi)
    (hindexU : (IsLocalRing.maximalIdeal B).map (algebraMap B U) =
      IsLocalRing.maximalIdeal U ^ e)
    (hsep : Algebra.IsSeparable (IsLocalRing.ResidueField B) (IsLocalRing.ResidueField U))
    (E : Type u) [Field E] [Algebra (FractionRing B) E]
    [Algebra B E] [IsScalarTower B (FractionRing B) E]
    [FiniteDimensional (FractionRing B) E] [Algebra.IsSeparable (FractionRing B) E]
    [Algebra U E] [IsFractionRing U E] [IsScalarTower B U E]
    (F : Type u) [Field F] [Algebra A F] (iE : E →+* F)
    (hcomm : ∀ b : B, iE (algebraMap B E b) =
      algebraMap A F (algebraMap B A b))
    (hgen : Algebra.adjoin A (Set.range iE) = ⊤)
    (T : Type u) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Algebra A T] [IsLocalHom (algebraMap A T)]
    [Algebra T F] [IsFractionRing T F] [IsScalarTower A T F]
    (j : U →+* T) (hj : IsLocalHom j)
    (hjB : ∀ b : B, j (algebraMap B U b) =
      algebraMap A T (algebraMap B A b))
    (hjE : ∀ c : U, algebraMap T F (j c) = iE (algebraMap U E c)) :
    Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField T) := by sorry

end RingTheory
