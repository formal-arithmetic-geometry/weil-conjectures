## Worker report

This delivery states lem-sfb-weyl-word-operators without changing its informal statement,
statement dependencies, proof or proof dependencies. The module
`Sheaf.Algebra.Lie.WeylWordOperators` contains the concrete word weights and the three
rational linear endomorphisms, followed by
`LieAlgebra.WeylWord.commutator_relations` with the sole postponed proof (`sorry`).
The helper definitions belong to the explicit construction already introduced by this
node; they do not introduce a separate mathematical notion or a new DAG prerequisite.
All six declarations are listed in `lean.declarations`.

Clause-by-clause reading:

- The finite set is `{I : Type u} [Finite I]` in the theorem. The universe `u` is explicit
  and unrestricted; neither `Nonempty I` nor an enumerated `Fintype I` is assumed.
- The arbitrary rational matrix is `B : I → I → ℚ`, the usual curried matrix type;
  the weight is `lam : I → ℚ`. There are no conditions on either parameter.
- The rational vector space A(I) is exactly `List I →₀ ℚ`. Its vectors are finite
  rational linear combinations of words; its distinguished basis consists of
  `Finsupp.single w 1`. It includes `w = []`, representing the empty word called 1
  in the node. No algebra multiplication is required for this vector-space statement.
- `WeylWord.weight B i w = (w.map (B i)).sum` is beta_i(w). List summation counts repeated
  letters with their multiplicity and gives zero for the empty list.
- `WeylWord.lowering i = Finsupp.lmapDomain ℚ ℚ (List.cons i)` is the linear extension
  of prepending i; this is F_i and the node's t_i.
- `WeylWord.cartan B lam i` is the `Finsupp.linearCombination` extension of
  `(lam i - weight B i w) • Finsupp.single w 1`, precisely H_i on basis vectors.
- `WeylWord.raisingWord B lam i [] = 0`. Its `j :: w` branch is the lowering map
  applied to its recursively constructed value at the strict tail w, plus
  `(lam i - weight B i w) • Finsupp.single w 1` if i=j and zero otherwise.
  This is exactly the delta_ij correction. Lean uses structural recursion on the list;
  every output is genuinely constructed finite support, not chosen from a sorry.
- `WeylWord.raising B lam i` extends `raisingWord` by `Finsupp.linearCombination ℚ`.
  Thus E_i is a rational linear endomorphism of the same vector space.
- The theorem quantifies `∀ i j : I` and gives all four endomorphism equalities as a
  conjunction in the node's order. Its first clause is `[H_i,H_j]=0`.
- Its second clause is `[E_i,F_j]=(if i=j then H_i else 0)`, exactly delta_ij H_i;
  the third is `[H_i,E_j]=B i j • E_j`; the fourth is
  `[H_i,F_j]=(-B i j) • F_j`. The row/column order is i,j throughout, including
  the weights in the recursion. These are genuine equalities of endomorphisms,
  rather than only pointwise hypotheses on unspecified operators.
- The bracket `⁅ , ⁆` is Mathlib's ring commutator on linear endomorphisms, with
  multiplication given by composition. This realizes the recorded dependency
  def-wf-lie-algebra and fixes the sign as XY-YX.

Dependency declarations read and used:

- def-wf-lie-algebra is a Mathlib node. Its recorded `mathlib_match` supplies
  `LieRing`, `LieAlgebra` (Mathlib.Algebra.Lie.Basic) and the associative-algebra
  commutator construction `LieRing.ofAssociativeRing` /
  `LieAlgebra.ofAssociativeAlgebra` (Mathlib.Algebra.Lie.OfAssociative).
  Read their full signatures/docstrings, together with
  `LieRing.of_associative_ring_bracket`. The relevant exact clause of this dependency
  is End(V) with commutator XY-YX, used for both statement and proof plan.
- `Finsupp.lmapDomain` (Mathlib.LinearAlgebra.Finsupp.Defs, publicly imported through
  Mathlib.LinearAlgebra.Finsupp.LinearCombination) supplies linear prepending.
  `Finsupp.linearCombination` and its `linearCombination_single` law in that latter
  module supply extension from the word basis. Read their signatures and definitions.
- `Module.End`, `List`, `Finsupp.single`, rational modules and list sums are used as
  Mathlib's existing notions, with no replacement definitions or local notation.

Edge cases checked before writing:

- I empty: lists have only the empty word; A(I) is one-dimensional over Q. There
  are no i,j, so all four universal identities are vacuous. The construction needs
  no inhabitant of I.
- Empty word: beta=0, E=0, H_i acts by lam_i, F_i produces the one-letter word.
  Hence `[E_i,F_j]` on it is delta_ij lam_i times the empty basis vector.
- A singleton alphabet with B=(b): E(t)=lam·1 and
  E(t^2)=(2lam-b)t. In particular `[H,E](t^2)=b(2lam-b)t`, including b=0,
  lam=0, negative b and singular B. This checks the signs in the recursion.
- For distinct i,j, E_i(t_j)=0; the off-diagonal EF commutator vanishes.
  There is no symmetry or Cartan-matrix diagonal restriction hidden in the API.
- For all-zero B and lam all operators H and E vanish, while the prepending maps
  still exist. The formula is meaningful on the zero vector and all finite sums.

Source reading: Milne, Algebraic Groups (2017), printed p.504 (PDF page 516),
Theorem 23.63 first proof, was read locally. It gives the surrounding Weyl-only
presentation and cites Bourbaki VIII section 4 no.2 for normal form. As the node
explicitly says, the present word recursion and its arbitrary-matrix generality
are agent-supplied, not a quotation from Milne; the module docstring preserves
that distinction. Also read the current latest blueprint Lie-algebra definition
and the direct-images stability proof (3), which are the dependency and route
context, respectively. No unsupported Bourbaki text is claimed to have been read.

Searches actually run with msearch.py Q66 lem-sfb-weyl-word-operators:

- `grep` query: Verma|highest.weight|word. Result: 3 hits; Mathlib/Algebra/Lie/CartanExists.lean, Mathlib/Algebra/Lie/Ideal.lean, Mathlib/Algebra/Lie/Basis/Prod.lean.
- `loogle` query: Module.End, FreeAlgebra. Result: 0 hits; none.
- `leanfinder` query: For an arbitrary rational matrix and weight the recursively defined raising and Cartan endomorphisms on finite words satisfy Weyl commutator identities. Result: 8 hits; RootPairing.GeckConstruction.e_lie_u, RootPairing.GeckConstruction.lie_e_lie_f_apply, RootPairing.GeckConstruction.lie_h_e, CartanMatrix.Relations.adE, CartanMatrix.Relations.HF, CartanMatrix.Relations.adF, RootPairing.GeckConstruction.lie_h_f, RootPairing.GeckConstruction.lie_e_f_mul_ω.
- `leansearch` query: Linear operators on the free vector space of words satisfying the Cartan and Chevalley commutator identities by a recursive raising operator. Result: 8 hits; FreeLieAlgebra.Rel.recOn, UniversalEnvelopingAlgebra.Rel.recOn, UniversalEnvelopingAlgebra.Rel.rec, FreeLieAlgebra.Rel.rec, FreeLieAlgebra.lift, FreeLieAlgebra.liftAux_spec, FreeLieAlgebra, FreeLieAlgebra.instLieAlgebra.

The semantic hits were inspected in Mathlib.Algebra.Lie.SerreConstruction and
Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Basic/Relations. CartanMatrix.Relations
only defines formal relations in a free Lie algebra; it supplies neither these word
operators nor proofs of their identities. Geck's operators are matrices on the root
pairing construction, assuming crystallographic root data, not arbitrary B and lam
on the word space. Free Lie and enveloping-algebra recursors do not supply the missing
construction. Loogle found no hit.

Direct `rg` searches of `lean/WeilConjectures`, `lean/Sheaf`, and
`dag/lean_names_upstream.json` for WeylWord, weylWord, weyl_word, wordOperators and
commutator_relations found no existing declaration. The broader Verma/highest.weight
search found highest-weight statements on different spaces, not this construction.
`grep -rn lem-sfb-weyl-word-operators lean/WeilConjectures` returned no hit.
`rg` of the Mathlib Lie and Finsupp source located the standard linear-extension
APIs used above. No dependency interface repair, statement correction or disputed
statement is needed.

## Second reading by Q66

Author's second pass, not an independent review: reopened the node and completed
module together. The finite-index assumption appears only in the theorem, and
its omission from the constructive helpers permits exactly the same finite cases.
All parameters are explicitly bound with autoImplicit and relaxedAutoImplicit
disabled. The word space includes [], and the recursion uses the weight of the
tail, rather than of j::w, in its delta term. Verified the order of all four
conjuncts, the EF equality when i=j and when i differs from j, and especially
the minus sign in HF and the untransposed B i j in HE. The conditional expression
encodes the Kronecker delta without adding decidability as a mathematical
hypothesis; Classical is opened only for the declarations that need it.
The data definitions are total concrete constructions; the sole theorem is sorry.
No mismatch with the node was found. The first compiler pass caught the reserved
identifier λ and the broad Classical scope; these were repaired using lam and
per-declaration `open Classical in`, without changing any mathematical clause.
Maintainer review is the independent review required by this direct-worker brief.
