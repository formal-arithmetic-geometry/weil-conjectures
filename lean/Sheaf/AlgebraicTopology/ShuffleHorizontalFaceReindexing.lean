module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Data.List.Count
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Prod

/-! # Horizontal deleted vertices of shuffle words

Source: the agent-written horizontal-face calculation in the DAG, proof steps 1–8
(blueprint: lem-sfb-shuffle-horizontal-face-reindexing). Its application is paragraph (3)
of the latest blueprint's `sk-thm-sf-ctf-stability-direct-images.proof.md`; that paragraph
does not itself state the combinatorial lemma. The requested Weibel reference is unavailable.

Letters are booleans: `false` means H and `true` means V. Words, marked vertices, prefix
counts, and evaluated strings are the literal objects introduced in this node. They do
not import the downstream lattice-path boundary theorem. Strings use arbitrary types
and retain repetitions. Their free integral module is Mathlib's finitely supported functions.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace AlgebraicTopology.ShuffleHorizontalFace

/-- The words with `a` H letters and `b` V letters; the length condition records `n=a+b`.
Source: the opening definitions of the agent-written DAG statement
(blueprint: lem-sfb-shuffle-horizontal-face-reindexing). -/
def Word (a b : ℕ) :=
  {w : List Bool // w.length = a + b ∧ w.count false = a ∧ w.count true = b}

/-- Horizontal prefix count `A_k`. Source: the opening definitions of the DAG statement
(blueprint: lem-sfb-shuffle-horizontal-face-reindexing). -/
def horizontalCount {a b : ℕ} (w : Word a b) (k : ℕ) : ℕ :=
  (w.val.take k).count false

/-- Vertical prefix count `B_k`. Source: the opening definitions of the DAG statement
(blueprint: lem-sfb-shuffle-horizontal-face-reindexing). -/
def verticalCount {a b : ℕ} (w : Word a b) (k : ℕ) : ℕ :=
  (w.val.take k).count true

/-- Number of V-before-H inversion pairs. Source: the opening definitions and proof step 5
of the agent-written DAG statement
(blueprint: lem-sfb-shuffle-horizontal-face-reindexing). -/
def inversions {a b : ℕ} (w : Word a b) : ℕ :=
  (((Finset.range w.val.length).product (Finset.range w.val.length)).filter
    (fun rs ↦ rs.1 < rs.2 ∧ w.val[rs.1]? = some true ∧
      w.val[rs.2]? = some false)).card

/-- Integral shuffle sign. Source: the opening definitions of the DAG statement
(blueprint: lem-sfb-shuffle-horizontal-face-reindexing). -/
def sign {a b : ℕ} (w : Word a b) : ℤ := (-1) ^ inversions w

/-- Horizontal marked vertices, including both endpoints. Option-valued letter access
makes the empty-word endpoint tests false, without a fictitious letter at position zero.
Source: the definition of `H_{a,b}` in the agent-written DAG statement
(blueprint: lem-sfb-shuffle-horizontal-face-reindexing). -/
def HorizontalFace (a b : ℕ) :=
  {p : Word a b × ℕ // p.2 ≤ a + b ∧
    ((p.2 = 0 ∧ p.1.val[0]? = some false) ∨
      (p.2 = a + b ∧ p.1.val[a + b - 1]? = some false) ∨
      (0 < p.2 ∧ p.2 < a + b ∧ p.1.val[p.2 - 1]? = some false ∧
        p.1.val[p.2]? = some false))}

/-- Evaluation of a word on two input strings. Prefixes are sublists of the full word,
so their counts give genuine bounded input indices, with no default values or choices.
Source: the definition of `z_{u,v}` in the agent-written DAG statement
(blueprint: lem-sfb-shuffle-horizontal-face-reindexing). -/
def evaluate {a b : ℕ} {X : Type u} {Y : Type v} (w : Word a b)
    (x : Fin (a + 1) → X) (y : Fin (b + 1) → Y) : List (X × Y) :=
  List.ofFn fun k : Fin (a + b + 1) ↦
    (x ⟨horizontalCount w k.val, by
      have h := (List.take_sublist k.val w.val).count_le false
      simpa only [horizontalCount, w.property.2.1] using Nat.lt_succ_of_le h⟩,
    y ⟨verticalCount w k.val, by
      have h := (List.take_sublist k.val w.val).count_le true
      simpa only [verticalCount, w.property.2.2] using Nat.lt_succ_of_le h⟩)

/-- The horizontal reindexing, with its exact forward and inverse word descriptions,
evaluated-string identity, inversion counts, endpoint labels, and integral signs.
The parameter `a` is the shorter horizontal degree: the positive degree is `a+1`.
The separate zero-degree clause includes the empty word.

Source: the agent-written DAG statement and proof steps 1–8
(blueprint: lem-sfb-shuffle-horizontal-face-reindexing), supplying the universal shuffle
input to paragraph (3) of the latest blueprint's direct-images proof.

Proof: remove the initial H, terminal H, or second H of an interior HH pair. This
removes one H and no V. At an interior mark the horizontal prefix count i lies between
1 and a, while the endpoint labels are 0 and a+1. Inverting the interior removal writes
the shorter word as P H Q at its i-th H, and replaces it by P H H Q with marked vertex
|P|+1. The endpoint inverses prepend or append H and mark that endpoint. The disjoint
label ranges prove both inverse identities and hence bijectivity of labeled pairs.
For an interior mark k, put t=B_k. Prefix counting gives k=i+t. Only inversion pairs
ending in the removed H are lost, and there are t of them. Initial removal loses none;
terminal removal loses b. Thus I(w)=I(shorter)+t, respectively I(shorter) or I(shorter)+b.
The sign equation follows from k=i+t and (-1)^(2t)=1; terminally k=a+1+b cancels the
two b contributions. For evaluated strings, before the omitted vertex the prefix
coordinates agree, and afterwards the horizontal coordinate is lowered by one while
the vertical coordinate is unchanged. Deleting input entry i restores exactly the
old horizontal values. At the endpoints the same calculation omits the first or last
vertex. This proves the string equality and hence the equality of its free basis symbols.
With one H there are no interior HH pairs, so only the endpoint inverses remain. With
no V all vertical counts and inversions vanish. With no H none of the marking tests
holds, including on the empty word. No step compares input values, so repetitions and
empty underlying types introduce no extra hypotheses. -/
theorem horizontal_face_reindexing (a b : ℕ) :
    IsEmpty (HorizontalFace 0 b) ∧
    ∃ Φ : HorizontalFace (a + 1) b ≃ Fin (a + 2) × Word a b,
      (∀ p : HorizontalFace (a + 1) b,
        (Φ p).1.val = horizontalCount p.val.1 p.val.2 ∧
        (Φ p).2.val = p.val.1.val.eraseIdx (min p.val.2 (a + 1 + b - 1)) ∧
        (0 < p.val.2 ∧ p.val.2 < a + 1 + b →
          1 ≤ (Φ p).1.val ∧ (Φ p).1.val < a + 1 ∧
          p.val.2 = (Φ p).1.val + verticalCount p.val.1 p.val.2 ∧
          inversions p.val.1 = inversions (Φ p).2 + verticalCount p.val.1 p.val.2) ∧
        (p.val.2 = 0 → (Φ p).1.val = 0 ∧ inversions p.val.1 = inversions (Φ p).2) ∧
        (p.val.2 = a + 1 + b → (Φ p).1.val = a + 1 ∧
          inversions p.val.1 = inversions (Φ p).2 + b) ∧
        sign p.val.1 * (-1 : ℤ) ^ p.val.2 = (-1 : ℤ) ^ (Φ p).1.val * sign (Φ p).2) ∧
      (∀ q : Fin (a + 2) × Word a b,
        (q.1.val = 0 → (Φ.symm q).val.1.val = false :: q.2.val ∧
          (Φ.symm q).val.2 = 0) ∧
        (q.1.val = a + 1 → (Φ.symm q).val.1.val = q.2.val ++ [false] ∧
          (Φ.symm q).val.2 = a + 1 + b) ∧
        (0 < q.1.val ∧ q.1.val < a + 1 → ∃ P Q : List Bool,
          q.2.val = P ++ false :: Q ∧ P.count false + 1 = q.1.val ∧
          (Φ.symm q).val.1.val = P ++ false :: false :: Q ∧
          (Φ.symm q).val.2 = P.length + 1)) ∧
      (∀ (X : Type u) (Y : Type v) (x : Fin (a + 1 + 1) → X) (y : Fin (b + 1) → Y)
          (p : HorizontalFace (a + 1) b),
        (evaluate p.val.1 x y).eraseIdx p.val.2 =
          evaluate (Φ p).2 (Fin.removeNth (Φ p).1 x) y ∧
        Finsupp.single ((evaluate p.val.1 x y).eraseIdx p.val.2) (1 : ℤ) =
          Finsupp.single (evaluate (Φ p).2 (Fin.removeNth (Φ p).1 x) y) (1 : ℤ)) := by
  sorry

end AlgebraicTopology.ShuffleHorizontalFace
