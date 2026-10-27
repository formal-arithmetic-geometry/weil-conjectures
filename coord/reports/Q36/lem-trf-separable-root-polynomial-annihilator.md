## Worker report

The module `Sheaf.FieldTheory.SeparableRootPolynomialAnnihilator` supplies the real
finite-sum definition `Polynomial.rootDividedDifference` and the statement
`Polynomial.separable_root_polynomial_annihilator`. The latter is the only theorem
and its proof is `sorry`. The helper is the polynomial explicitly introduced by
this very node, rather than a new independent notion. Both declarations are listed
in `lean.declarations`. No statement correction, dependency repair or new DAG node
is needed; only the item's `lean` field changes.

Source read: `literature/stacks-project/algebra.tex`, label
`lemma-separable-algebraic-diagonal` (Tag 0C2X), especially the displayed
factorization and nonvanishing in the finite-extension paragraph and the
algebraic-union paragraph. The node expands that calculation coefficientwise.
All four proof steps, including telescoping, the derivative calculation, Bezout
evaluation, and commutative evaluation in the target, appear in the docstring.

The correspondence with every hypothesis and clause is as follows:

| Node | Lean |
| --- | --- |
| Field L | `(L : Type u) [Field L]` |
| Commutative ring R, including the zero ring | `(R : Type v) [CommRing R]`; no nontriviality assumption |
| Unital ring map iota | `(ι : L →+* R)` |
| alpha and P in L and L[T] | `(α : L) (P : L[X])` |
| P(alpha)=0 and P separable | `(hP : P.eval α = 0) (hsep : P.Separable)` |
| Evaluation G(t) through iota | `G.eval₂ ι t`, whose source definition is the finite coefficient sum |
| Explicit polynomial D for every G | `rootDividedDifference G α := G.sum fun j c ↦ C c * ∑ h ∈ Finset.range j, X ^ (j - 1 - h) * C (α ^ h)` |
| Finite outer sum and j at least 1 | `Polynomial.sum` sums over `G.support`; at j=0 the inner range is empty |
| G(T)-G(alpha)=(T-alpha)D | First conjunct under `∀ G : L[X]`, with scalar embedding `C (G.eval α)` |
| D(alpha)=G'(alpha) | Second conjunct under the same `∀ G` |
| Q=D for P; P=(T-alpha)Q | `P = (X - C α) * rootDividedDifference P α` |
| Q(alpha)=P'(alpha) nonzero | Consecutive equality and `P.derivative.eval α ≠ 0` conjuncts |
| Every t with P(t)=0 | `∀ (t : R), P.eval₂ ι t = 0 → ...` |
| Every F with F(alpha)=0, H=D for F | `∀ (F : L[X]), F.eval α = 0 → ... rootDividedDifference F α ...` |
| F=(T-alpha)H | First conjunct under these quantifiers |
| Q(t)F(t)=P(t)H(t)=0 | Final two equality conjuncts; the chain is split into its two equalities |

The symbols Q and H are written as their specified definitions throughout, avoiding
opaque local `let` binders. Distinct universes `u` and `v` cover independent field
and target-ring sizes. `set_option autoImplicit false` verifies explicit binding.

Dependency declarations read and used:

- `def-weil-field`: `Field` in `Mathlib.Algebra.Field.Defs`, signature and docstring
  read, a commutative division ring with nontriviality inherited from DivisionRing.
- `def-weil-polynomial-ring`: recorded `Polynomial` in
  `Mathlib.Algebra.Polynomial.Basic`; it wraps finitely supported coefficient
  sequences. The same module defines the actual support sum used here.
- `def-pc-separable-polynomial`: its `mathlib_match` is `Polynomial.Separable`
  in `Mathlib.FieldTheory.Separable`, literally `IsCoprime f (derivative f)`.
  The derivative source in `Mathlib.Algebra.Polynomial.Derivative` and evaluation
  source in `Mathlib.Algebra.Polynomial.Eval.Defs` were read as well.

Edge cases checked before writing: G=0 and G constant have empty contributing
inner sums and D=0; F=0 therefore has H=0. For alpha=0 the h=0 term uses 0^0=1,
as required, and the remaining terms vanish. For j=1 the inner range is {0}
and its exponent is zero. In characteristic p the diagonal inner sum counts j
by repeated addition, agreeing with the formal derivative even when p divides j.
P=0 is excluded by separability over a field; a nonzero constant P cannot have
the assumed root. A linear P gives a nonzero constant Q. In the zero target ring
all evaluations and both final equalities are zero; no injectivity or cancellation
in R is assumed. No disputed statement or node fault was found.

Searches on 2026-10-24, through the required msearch wrapper:

- LeanFinder, query: "The explicit divided difference of a polynomial at a root
  factors the polynomial, evaluates to its derivative and yields annihilators in
  any commutative target ring". Eight hits, including `Polynomial.aeval_sumIDeriv`
  and split-polynomial derivative formulas; none states the explicit sum and all
  the required annihilation identities.
- Loogle, query: `Polynomial.Separable, Polynomial.eval`. Two hits:
  `Polynomial.eq_X_sub_C_of_separable_of_root_eq` and
  `IsSepClosed.of_exists_root`; neither is the statement.
- Grep in `Algebra/Polynomial`, query:
  `divided.?difference|divXSubC|divByMonic.*derivative|eval₂_derivative_ne_zero`.
  Two hits in FieldDivision for a derivative of a monic-division identity;
  these do not define the prescribed finite coefficient sum or state this result.
- LeanSearch, query: "The finite coefficient divided difference at a separable
  polynomial root gives a nonzero complementary factor annihilating any
  evaluation vanishing at the root". Eight hits, including
  `Polynomial.Separable.eval₂_derivative_ne_zero` and
  `Polynomial.mul_div_eq_iff_isRoot`; these provide ingredients only.
- Direct `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `divided.?[Dd]ifference|divXSubC|root_polynomial_annihilator|separable.*annihilat`
  found only unrelated references to annihilating polynomials in other modules.
  The required grep for this exact node id in `lean/WeilConjectures` found none.
  Exact name searches for both proposed declaration names in Mathlib,
  WeilConjectures, Sheaf and `dag/lean_names_upstream.json` found no collision.

Validation: scompile.py compiled both sandbox and library module modes successfully
on the server (12.3 s and 2.4 s), with no errors or warnings. The complete statement
uses only the dependency notions and standard polynomial operations.

## Second reading by Q36

I reread the node and completed module together. This is a self-review: the
dispatcher explicitly prohibited starting another agent; the maintainer's
independent delivery review remains separate. The table above was checked against
the actual theorem signature. The outer coefficient sum includes j=0 only with an
empty inner sum, so it is exactly the requested j≥1 sum. The chain of annihilator
equalities retains the middle product P(t)H(t), and the derivative equality and
nonvanishing are both present. Field and commutative-ring assumptions match, the
map is unital, and the target has no added nontriviality hypothesis. Every
quantified polynomial uses the recorded Mathlib type. No mismatch was found and
no correction was made during this reading. The module and declaration docstrings
identify the node, and the sole postponed theorem contains all four proof steps.
