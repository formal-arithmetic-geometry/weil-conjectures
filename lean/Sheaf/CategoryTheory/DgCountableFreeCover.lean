module

public import Sheaf.CategoryTheory.DgAlgebraDerivedCategory
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Data.Countable.Defs
import Mathlib.Data.Set.Countable

/-!
# Countable two-layer free covers of DG modules

Source: Stacks Project, dga.tex, Tag 09KN, lemma-good-quotient, and Tag 0CRM,
lemma-countable, proof (2) to (1) (blueprint: lem-sfb-dg-countable-free-cover).

The witness is an admissible short exact sequence with specified finite-support
coordinates on both layers. Its graded splitting gives the homogeneous basis of
Q indexed by the disjoint union U ⊕ V. No differential splitting is required.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace CategoryTheory.DgAlgebra

/-- The witnesses to the countable two-layer cover assertion. The layer coordinates
identify L and R with direct sums of A[-t], including action and differential.
The graded splitting identifies Q with L ⊕ R, with inclusion and quotient fixed.
Thus the generators from U are closed, and differentials of the generators from V
lie in L. The two types are regarded as disjoint by their tags in U ⊕ V.
Source: Stacks Project, dga.tex, Tag 09KN and Tag 0CRM, proof (2) to (1)
(blueprint: lem-sfb-dg-countable-free-cover). -/
structure CountableTwoLayerFreeCover (A : Algebra.{u}) (M : RightModule A) where
  Q : RightModule A
  map : Q ⟶ M
  U : Type u
  V : Type u
  countableU : Countable U
  countableV : Countable V
  degreeU : U → ℤ
  degreeV : V → ℤ
  L : RightModule A
  R : RightModule A
  inclusion : L ⟶ Q
  quotient : Q ⟶ R
  split (n : ℤ) : ((underlying A).obj Q).X n ≃+
    (((underlying A).obj L).X n × ((underlying A).obj R).X n)
  split_inclusion (n : ℤ) (x : ((underlying A).obj L).X n) :
    split n ((((underlying A).map inclusion).f n) x) = (x, 0)
  split_quotient (n : ℤ) (x : ((underlying A).obj Q).X n) :
    (((underlying A).map quotient).f n) x = (split n x).2
  split_action (n m : ℤ) (x : ((underlying A).obj Q).X n) (a : A.X.X m) :
    split (n + m) (act A Q n m x a) =
      (act A L n m (split n x).1 a, act A R n m (split n x).2 a)
  coordinateU (n : ℤ) : ((underlying A).obj L).X n ≃+
    DirectSum U (fun w ↦ A.X.X (n - degreeU w))
  coordinateV (n : ℤ) : ((underlying A).obj R).X n ≃+
    DirectSum V (fun w ↦ A.X.X (n - degreeV w))
  actionU (n m : ℤ) (x : ((underlying A).obj L).X n) (a : A.X.X m) (w : U) :
    HEq (coordinateU (n + m) (act A L n m x a) w)
      (act A (regular A) (n - degreeU w) m (coordinateU n x w) a)
  actionV (n m : ℤ) (x : ((underlying A).obj R).X n) (a : A.X.X m) (w : V) :
    HEq (coordinateV (n + m) (act A R n m x a) w)
      (act A (regular A) (n - degreeV w) m (coordinateV n x w) a)
  differentialU (n : ℤ) (x : ((underlying A).obj L).X n) (w : U) :
    HEq (coordinateU (n + 1) ((((underlying A).obj L).d n (n + 1)) x) w)
      ((degreeU w).negOnePow •
        (A.X.d (n - degreeU w) (n - degreeU w + 1)) (coordinateU n x w))
  differentialV (n : ℤ) (x : ((underlying A).obj R).X n) (w : V) :
    HEq (coordinateV (n + 1) ((((underlying A).obj R).d n (n + 1)) x) w)
      ((degreeV w).negOnePow •
        (A.X.d (n - degreeV w) (n - degreeV w + 1)) (coordinateV n x w))
  surjective (n : ℤ) : Function.Surjective (((underlying A).map map).f n)
  surjective_cycles (n : ℤ) (z : ((underlying A).obj M).X n)
      (hz : (((underlying A).obj M).d n (n + 1)) z = 0) :
    ∃ x : ((underlying A).obj Q).X n,
      (((underlying A).obj Q).d n (n + 1)) x = 0 ∧
        (((underlying A).map map).f n) x = z
  countableQ : Countable (Σ n : ℤ, (((underlying A).obj Q).X n : Type u))

/-- Every countable right DG module over a countable DG algebra admits the specified
countable two-layer free cover, surjective degreewise and on actual cocycles.
Source: Stacks Project, dga.tex, Tag 09KN, lemma-good-quotient, with the countability
refinement of Tag 0CRM, lemma-countable, proof (2) to (1)
(blueprint: lem-sfb-dg-countable-free-cover).

Proof: (1) For each homogeneous m in M^k introduce x_(k,m), y_(k,m) in degrees
k, k+1, and for each homogeneous cocycle z introduce s_(k,z) in its degree.
Let V consist of x symbols and U of y and s symbols; encode these countable sets
by the three symbol tags and an injection of the homogeneous elements into ℕ.
Take Q^n to be the finite-support families of coefficients A^(n-t_w).
(2) Define D(e_w a) = δ_w a + (-1)^t_w e_w d_A(a), with δ_x = e_y and
δ_y = δ_s = 0. Uniqueness of coordinates makes D additive and well-defined;
the algebra Leibniz identity gives the module Leibniz identity. Also d_A(1)=0.
(3) D squared vanishes on y and s by d_A squared equals zero. On x, the two
mixed terms have signs (-1)^k and (-1)^(k+1) and cancel. Thus Q is a DG module.
(4) Map x to m, y to d_M(m), and s to z, extending right A-linearly.
The three generator equations and the module Leibniz identity show this is a DG map.
(5) The x generators lift all homogeneous elements; the closed s generators lift
all actual cocycles, proving both surjectivity assertions.
(6) Encode a homogeneous finite-support vector by its degree and its finite list
of nonzero coordinate/coefficient labels, sorted by the coordinate labels.
The sets of lists of bounded length are countable. Apply lem-trf-countable-unions
(Set.countable_iUnion) over the length bound to obtain countability of Q.
(7) Let L be the span of U and R the quotient by that span. D preserves L, and the
coordinate projection onto L is graded A-linear. Both L and R have coordinate
differential (-1)^t_w d_A and unchanged action, hence are the stated sums A[-t_w].
The coordinate decomposition gives split, inclusion and quotient. -/
theorem exists_countableTwoLayerFreeCover (A : Algebra.{u})
    (hA : Countable (Σ n : ℤ, (A.X.X n : Type u))) (M : RightModule A)
    (hM : Countable (Σ n : ℤ, (((underlying A).obj M).X n : Type u))) :
    Nonempty (CountableTwoLayerFreeCover A M) := by
  sorry

end CategoryTheory.DgAlgebra
