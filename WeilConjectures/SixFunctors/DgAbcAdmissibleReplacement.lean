/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SmallDgCategory
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-!
# Simultaneous admissible replacement of a finite dg diagram

Source: `literature/stacks-project/dga.tex`, Tags 09QJ and 09QN,
situation-ABC and lemma-analogue-sequence-maps-split
(blueprint: lem-coef-dg-abc-admissible-replacement).

The ABC data below use the existing enriched dg categories, their actual Hom complexes,
and signed tensor composition. Integral coefficients are `ULift ℤ`, allowing arbitrary
small universes without changing the category of integral modules.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

namespace CategoryTheory.Dg.ABC

/-- Integral coefficients at the chosen universe bound.
Source: Stacks, Tag 09QJ (blueprint: lem-coef-dg-abc-admissible-replacement). -/
abbrev Coeff := ULift.{u} ℤ

variable (A : Dg.Cat Coeff.{u})

/-- Axiom (A): an enriched zero object and dg binary biproducts. The structure maps
are closed degree-zero elements of the existing Hom complexes. Vanishing of both Hom
complexes is equivalent to being a zero object, by the identity and composition laws.
Source: Stacks, Tag 09QJ and definition-dg-direct-sum
(blueprint: lem-coef-dg-abc-admissible-replacement). -/
structure Sums where
  zero : A
  from_zero : ∀ (x : A) (n : ℤ), Subsingleton ((hom Coeff A zero x).X n)
  to_zero : ∀ (x : A) (n : ℤ), Subsingleton ((hom Coeff A x zero).X n)
  sum : A → A → A
  inl : ∀ x y : A, (hom Coeff A x (sum x y)).X 0
  inr : ∀ x y : A, (hom Coeff A y (sum x y)).X 0
  fst : ∀ x y : A, (hom Coeff A (sum x y) x).X 0
  snd : ∀ x y : A, (hom Coeff A (sum x y) y).X 0
  inl_closed : ∀ x y, (hom Coeff A x (sum x y)).d 0 1 (inl x y) = 0
  inr_closed : ∀ x y, (hom Coeff A y (sum x y)).d 0 1 (inr x y) = 0
  fst_closed : ∀ x y, (hom Coeff A (sum x y) x).d 0 1 (fst x y) = 0
  snd_closed : ∀ x y, (hom Coeff A (sum x y) y).d 0 1 (snd x y) = 0
  fst_inl : ∀ x y, mulAt Coeff rfl (fst x y) (inl x y) = unit Coeff A x
  snd_inr : ∀ x y, mulAt Coeff rfl (snd x y) (inr x y) = unit Coeff A y
  snd_inl : ∀ x y, mulAt Coeff rfl (snd x y) (inl x y) = 0
  fst_inr : ∀ x y, mulAt Coeff rfl (fst x y) (inr x y) = 0
  total : ∀ x y, mulAt Coeff rfl (inl x y) (fst x y) +
    mulAt Coeff rfl (inr x y) (snd x y) = unit Coeff A (sum x y)

/-- Axiom (B): strict dg shift functors and cochain isomorphisms
`A(x,y[n]) ≅ A(x,y)[n]`. Mathlib's cochain shift has degree `j+n` and differential
`(-1)^n d`. The two homogeneous composition laws spell out compatibility: precomposition
has no sign; shifted postcomposition has the Koszul sign `(-1)^(n*p)`. Differential
compatibility is part of `homIso`, and preservation of units and composition is part of
`Dg.Fun`. `HEq` only transports the equal integer degrees in the displayed laws.
Source: Stacks, Tag 09QJ, axiom (B)
(blueprint: lem-coef-dg-abc-admissible-replacement). -/
structure Shifts where
  shift : ℤ → Dg.Fun Coeff A A
  shift_zero : shift 0 = EnrichedFunctor.id _ A
  shift_add : ∀ n m : ℤ, shift (n + m) = (shift m).comp _ (shift n)
  homIso : ∀ (n : ℤ) (x y : A),
    hom Coeff A x ((shift n).obj y) ≅
      (CochainComplex.shiftFunctor (ModuleCat Coeff) n).obj (hom Coeff A x y)
  precomp : ∀ (n p q : ℤ) (x y z : A)
      (b : (hom Coeff A y ((shift n).obj z)).X p) (a : (hom Coeff A x y).X q),
    HEq ((homIso n x z).hom.f (p + q) (mul Coeff A p q b a))
      (mul Coeff A (p + n) q ((homIso n y z).hom.f p b) a)
  postcomp : ∀ (n p q : ℤ) (x y z : A)
      (b : (hom Coeff A y z).X p) (a : (hom Coeff A x ((shift n).obj y)).X q),
    HEq ((homIso n x z).hom.f (p + q)
      (mul Coeff A p q (((shift n).map y z).f p b) a))
      ((n * p).negOnePow • mul Coeff A p (q + n) b ((homIso n x y).hom.f q a))

/-- The five graded splitting identities for an admissible sequence. Neither splitting
map is required to be closed. All four maps are in the actual degree-zero Hom groups.
Source: Stacks, Tag 09QJ and Tag 09P6, lemma-get-triangle
(blueprint: lem-coef-dg-abc-admissible-replacement). -/
structure Splitting {x y z : A}
    (a : (hom Coeff A x y).X 0) (b : (hom Coeff A y z).X 0) where
  pi : (hom Coeff A y x).X 0
  s : (hom Coeff A z y).X 0
  pi_a : mulAt Coeff rfl pi a = unit Coeff A x
  b_s : mulAt Coeff rfl b s = unit Coeff A z
  total : mulAt Coeff rfl a pi + mulAt Coeff rfl s b = unit Coeff A y
  b_a : mulAt Coeff rfl b a = 0
  pi_s : mulAt Coeff rfl pi s = 0

/-- A closed degree-zero pair admitting a graded biproduct splitting.
Source: Stacks, Tag 09QJ (blueprint: lem-coef-dg-abc-admissible-replacement). -/
def IsAdmissible {x y z : A}
    (a : (hom Coeff A x y).X 0) (b : (hom Coeff A y z).X 0) : Prop :=
  (hom Coeff A x y).d 0 1 a = 0 ∧ (hom Coeff A y z).d 0 1 b = 0 ∧
    Nonempty (Splitting A a b)

/-- An admissible monomorphism is the first arrow of an admissible sequence.
Source: Stacks, Tag 09QJ (blueprint: lem-coef-dg-abc-admissible-replacement). -/
def IsAdmissibleMono {x y : A} (a : (hom Coeff A x y).X 0) : Prop :=
  ∃ (z : A) (b : (hom Coeff A y z).X 0), IsAdmissible A a b

/-- The boundary `pi * d(s)`, transported from degree one to a degree-zero arrow
into `x[1]` using the inverse of the axiom-(B) cochain isomorphism. This is a construction,
not an independent arrow or a freely asserted boundary field.
Source: Stacks, Tag 09P6, lemma-get-triangle
(blueprint: lem-coef-dg-abc-admissible-replacement). -/
def boundary (B : Shifts A) {x y z : A}
    {a : (hom Coeff A x y).X 0} {b : (hom Coeff A y z).X 0}
    (t : Splitting A a b) : (hom Coeff A z ((B.shift 1).obj x)).X 0 :=
  (B.homIso 1 z x).inv.f 0
    (mulAtDegree Coeff t.pi ((hom Coeff A z y).d 0 1 t.s) rfl)

/-- Axiom-(C) cone sequence with its actual graded splitting and boundary equation.
The equation says `pi * d(s) = f[1]` after the axiom-(B) identification.
Source: Stacks, Tag 09QJ, axiom (C)
(blueprint: lem-coef-dg-abc-admissible-replacement). -/
structure ConeData (B : Shifts A) {x y : A} (f : (hom Coeff A x y).X 0) where
  obj : A
  i : (hom Coeff A y obj).X 0
  p : (hom Coeff A obj ((B.shift 1).obj x)).X 0
  i_closed : (hom Coeff A y obj).d 0 1 i = 0
  p_closed : (hom Coeff A obj ((B.shift 1).obj x)).d 0 1 p = 0
  splitting : Splitting A i p
  boundary_eq : boundary A B splitting = ((B.shift 1).map x y).f 0 f

/-- Axiom (C) asks for cone data for every closed degree-zero arrow.
Source: Stacks, Tag 09QJ (blueprint: lem-coef-dg-abc-admissible-replacement). -/
def HasCones (B : Shifts A) : Prop :=
  ∀ (x y : A) (f : (hom Coeff A x y).X 0),
    (hom Coeff A x y).d 0 1 f = 0 → Nonempty (ConeData A B f)

/-- A homotopy equivalence is a closed degree-zero arrow invertible modulo boundaries.
`Dg.IsH0Iso` supplies the closed inverse and two degree-minus-one homotopies.
Source: Stacks, Tag 09QN and the definition of `K(A)` preceding Tag 09QJ
(blueprint: lem-coef-dg-abc-admissible-replacement). -/
def IsHomotopyEquiv {x y : A} (f : (hom Coeff A x y).X 0) : Prop :=
  (hom Coeff A x y).d 0 1 f = 0 ∧ IsH0Iso Coeff f

end CategoryTheory.Dg.ABC

namespace CategoryTheory

/-- Simultaneous admissible replacement of a finite closed dg diagram.
Source: Stacks, Tags 09QN (lemma-analogue-sequence-maps-split), 09QM (lemma-factor),
09QK (lemma-id-cone-null), 09P6 (lemma-get-triangle), and 09QJ (situation-ABC)
(blueprint: lem-coef-dg-abc-admissible-replacement).

Proof, with the six steps of the DAG node:
1. Differentiate the five splitting identities of a cone `y → C(f) → x[1]`.
Writing `theta : x → x[1]` and `eta : x[1] → x` for the inverse closed graded shift
maps of degrees -1 and 1, the boundary axiom gives `pi d(s) = f eta`.
Differentiating gives `b d(s) = 0`, `d(pi) a = 0`, and `d(pi) s = -pi d(s)`.
Insert `1 = a pi + s b` to obtain `d(s) = a f eta` and `d(pi) = -f eta b`.
2. For the cone of `1_x`, put `h = s theta pi`. Signed Leibniz and the preceding
identities give `d(h) = a pi + s b = 1_C`; the negative Leibniz sign on
`s theta` cancels the negative sign in `d(pi)`. Thus the identity cone is contractible.
3. For a closed `alpha : x → y`, put `M = y ⊕ C(1_x)`, `j = I alpha + J a`,
and `r = P`, using the four dg biproduct maps. Then `r j = alpha`, `r I = 1`,
and `H = J h Q` satisfies `d(H) = 1_M - I P`, so `r` is a homotopy equivalence.
4. Take `D = C(alpha)` with splitting `(pi',s')`. The quotient
`q = a'(P - alpha pi Q) - s' b Q` is closed: its two differential terms cancel
by Step 1: `d(pi) = -eta b` and `d(s') = a' alpha eta`, so
`d(q) = a' alpha eta b Q - a' alpha eta b Q = 0`. Also
`q j = a'(alpha - alpha pi a) - s' b a = 0`. The quotient is this cone.
5. Set `rho = pi Q` and `sigma = I pi' - J s b'`. Direct expansion gives
`rho j = 1`, `q sigma = 1`, `j rho + sigma q = 1`, `q j = 0`, and
`rho sigma = 0`. In particular `sigma q = I(P - alpha pi Q) + J s b Q`,
so `j rho + sigma q = IP + J(a pi + s b)Q = 1_M`.
The other identities follow from `pi a = 1`, `pi s = 0`, and
`a' pi' + s' b' = 1_D`. Hence `j` is an admissible monomorphism.
6. Induct on `N ≥ 1`. At `N = 1` keep `x_1` and its identity. At the next step
apply Steps 2--5 to `alpha = f_i r_i`, retain the earlier data, and obtain
`r_(i+1) j_i = f_i r_i` as an equality of actual degree-zero arrows. -/
theorem dg_abc_admissible_replacement
    (A : Dg.Cat Dg.ABC.Coeff.{u})
    (sums : Dg.ABC.Sums A)
    (shifts : Dg.ABC.Shifts A)
    (cones : Dg.ABC.HasCones A shifts)
    (N : ℕ) (hN : 1 ≤ N)
    (x : Fin N → A)
    (f : ∀ i : Fin (N - 1), (Dg.hom Dg.ABC.Coeff A
      (x (Fin.cast (Nat.sub_add_cancel hN) i.castSucc))
      (x (Fin.cast (Nat.sub_add_cancel hN) i.succ))).X 0)
    (hf : ∀ i : Fin (N - 1), (Dg.hom Dg.ABC.Coeff A
      (x (Fin.cast (Nat.sub_add_cancel hN) i.castSucc))
      (x (Fin.cast (Nat.sub_add_cancel hN) i.succ))).d 0 1 (f i) = 0) :
    ∃ (y : Fin N → A)
      (j : ∀ i : Fin (N - 1), (Dg.hom Dg.ABC.Coeff A
        (y (Fin.cast (Nat.sub_add_cancel hN) i.castSucc))
        (y (Fin.cast (Nat.sub_add_cancel hN) i.succ))).X 0)
      (r : ∀ i : Fin N, (Dg.hom Dg.ABC.Coeff A (y i) (x i)).X 0),
      y ⟨0, hN⟩ = x ⟨0, hN⟩ ∧
      HEq (r ⟨0, hN⟩) (Dg.unit Dg.ABC.Coeff A (x ⟨0, hN⟩)) ∧
      (∀ i : Fin (N - 1), Dg.ABC.IsAdmissibleMono A (j i)) ∧
      (∀ i : Fin N, Dg.ABC.IsHomotopyEquiv A (r i)) ∧
      (∀ i : Fin (N - 1), Dg.mulAt Dg.ABC.Coeff rfl
        (r (Fin.cast (Nat.sub_add_cancel hN) i.succ)) (j i) =
          Dg.mulAt Dg.ABC.Coeff rfl (f i)
            (r (Fin.cast (Nat.sub_add_cancel hN) i.castSucc))) := by
  sorry

end CategoryTheory
