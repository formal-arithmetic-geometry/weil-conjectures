## Worker report

The module `Sheaf.FieldTheory.PIndependentRootQuotientField` states
`Algebra.ParameterRoot.isField_of_pIndependent`, with `sorry` as its only proof.
No definitions or auxiliary axioms are introduced. The mathematical statement is unchanged.
The landed definition `def-sfb-parameter-root-algebra` is added to `stmt_deps`.
The simultaneous-root theorem API remains only in `proof_deps`; its import is plain.

Hypothesis and conclusion correspondence:

- A prime p: `(p : ℕ) [Fact p.Prime]`.
- A field k of characteristic p: `(k : Type u) [Field k] [CharP k p]`.
  The universe `u` is explicit and unrestricted.
- A finite tuple of length r, including r = 0: `(r : ℕ) (b : Fin r → k)`.
- The subfield k^p is `(frobenius k p).fieldRange`. Mathlib's
  `RingHom.fieldRange` has underlying set `Set.range` of the ring homomorphism,
  and `frobenius` has value `x ^ p`; thus this is precisely the subfield in the
  node, not a larger field and not an arbitrary scalar algebra.
- Independence of the specified monomials: `hb : LinearIndependent
  (frobenius k p).fieldRange (fun e : Fin r → Fin p ↦ ∏ i, b i ^ (e i).val)`.
  Functions to `Fin p` index exactly the tuples of exponents 0 ≤ e_i < p.
- Every integer n ≥ 1: `(n : ℕ) (hn : 1 ≤ n)`. Natural numbers with this bound
  are exactly the allowed integers; no height is lost.
- The algebra C_n is `Algebra.pthRootAlgebra (p ^ n) r k b`. Reading that
  definition shows it is literally
  `MvPolynomial (Fin r) k ⧸ Ideal.span (Set.range (fun i ↦ X i ^ (p ^ n) - C (b i)))`.
  The inherited `Algebra k` is the canonical polynomial/quotient coefficient map.
- C_n is a field: `IsField (Algebra.pthRootAlgebra (p ^ n) r k b)`. This predicate on the existing
  commutative ring asserts nontriviality and inverses of every nonzero element;
  it does not choose a second ring structure.
- The stated k-basis: an existential `Module.Basis (Fin r → Fin (p ^ n)) k
  (Algebra.pthRootAlgebra (p ^ n) r k b)`, with each vector required to equal
  `∏ i, (Ideal.Quotient.mk _ (MvPolynomial.X i) :
  Algebra.pthRootAlgebra (p ^ n) r k b) ^ (e i).val`. These are the actual classes of X_i.
  This records the specified vectors, not merely finite freeness or a dimension.
- Every z has its p^n-th power in k: `∀ z, ∃ a : k, algebraMap k _ a = z ^ (p ^ n)`.
  Together with fieldhood the coefficient map is an inclusion; no arbitrary map
  or pre-existing injectivity assumption is supplied.
- The r = 0 convention: `r = 0 → Function.Bijective (algebraMap k (Algebra.pthRootAlgebra (p ^ n) r k b))`.
  Bijectivity of this canonical algebra map identifies C_n with k as a k-algebra.
  It is stated explicitly as well as being covered by the other conclusions.

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field` (`Mathlib.Algebra.Field.Defs`), and its
  proposition-valued form `IsField` (`Mathlib.Algebra.Field.IsField`).
- `def-weil-pbc-mv-polynomial-ring`: `MvPolynomial` and `MvPolynomial.algHom_ext`
  (`Mathlib.Algebra.MvPolynomial.Basic`), and `MvPolynomial.aeval`
  (`Mathlib.Algebra.MvPolynomial.Eval`); the canonical root algebra uses these.
- `def-weil-pbc-algebra-hom-quotient`: `AlgHom` (`Mathlib.Algebra.Algebra.Hom`),
  `Ideal.Quotient.algebra` and `Ideal.Quotient.mkₐ`
  (`Mathlib.RingTheory.Ideal.Quotient.Operations`). The quotient's existing
  instance is used rather than a new algebra structure.
- `def-weil-pbc-free-module`: `Module.Free` (`Mathlib.LinearAlgebra.FreeModule.Basic`)
  and the underlying `Module.Basis` (`Mathlib.LinearAlgebra.Basis.Defs`). The
  stronger, explicitly specified basis clause is rendered directly by `Module.Basis`.
- `def-sfb-parameter-root-algebra`: `Algebra.pthRootAlgebra`
  (`WeilConjectures.RingTheory.PthRootAlgebraLocal`), read with its full definition
  and docstring, and imported publicly. Its exponent is unrestricted, so it applies
  directly to p^n.
- `lem-sfb-simultaneous-root-algebra-api`: `root_pow`, `exists_basis`, and `emptyEquiv`
  (`Sheaf.RingTheory.ParameterRootAlgebra`), read with their signatures and definitions.
  This remains a proof dependency and its module is imported without `public`.
- `def-weil-ring-frobenius`: `iterateFrobeniusOfPrime` and
  `iterateFrobeniusOfPrime_apply` (`WeilConjectures.Mathlib.Algebra.CharP.Lemmas`)
  are imported as a proof dependency; they cover the quotient before nontriviality
  has been proved. Mathlib `frobenius` (`Mathlib.Algebra.CharP.Lemmas`) and
  `RingHom.fieldRange` (`Mathlib.Algebra.Field.Subfield.Basic`) give the exact
  coefficient subfield occurring in the statement.
- `lem-sfb-p-independent-higher-power-monomials` has no recorded Lean module in
  the read clone, so there is no import for it; its role in the future proof is
  documented in the theorem docstring. It supplies no missing statement object.

Edge cases checked mathematically before writing:

- r = 0: the indexing family `Fin 0 → Fin q` is a singleton, each empty product
  is 1, the ideal has no generators, and `emptyEquiv` identifies the quotient with k.
- n = 1: this is the ordinary p-root quotient, with p^r basis vectors.
- n = 0 is deliberately excluded exactly as in this node, not silently included.
- z = 0 is included in the power conclusion (choose a = 0).
- b_i = 0 is impossible for a nonempty independent tuple: the exponent vector
  with one exponent 1 gives a zero vector. For r = 0 there is no such restriction.
- Repeated tuple entries fail independence when their positions differ.
- Perfect k and nonempty r fail the independence premise; the empty tuple remains valid.
- p = 2 is included; p = 0 and p = 1 fail primality. A zero ring is not a field,
  so the base nontriviality assumption is exactly the source's field assumption.

Searches (2026-10-24):

- `msearch.py ... leanfinder "A finite simultaneous quotient adjoining p power roots
  of p independent field elements is a field with the bounded monomial basis"`:
  eight hits, chiefly `PerfectClosure.instField`, perfect closures, finite fields,
  and splitting fields. None states the given quotient result.
- `msearch.py ... loogle "MvPolynomial, IsField"`: zero hits.
- `msearch.py ... grep
  "pthRootAlgebra|pIndependent|p_independent|quotient.*isField|isField.*quotient"
  RingTheory`: 22 hits on general quotient-field criteria, localization, and
  unrelated ring results; no exact statement.
- `msearch.py ... leansearch "Adjoining p power roots of p independent field elements
  by polynomial quotient gives a field with bounded monomial basis"`: eight hits
  on `AdjoinRoot` power bases and field instances for irreducible univariate
  polynomials. These do not state arbitrary-height simultaneous-root fieldhood.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for p-independence,
  `pthRootAlgebra`, and quotient-field names: reused `ParameterRootAlgebra`.
  Read `Algebra.pthRootAlgebra_isField_finite_pow` in
  `WeilConjectures.RingTheory.PthRootFieldQuotient`: it addresses only exponent p,
  assumes independent differentials, and supplies finiteness rather than the
  specified bounded basis. It is not an exact existing declaration for this node.
- Search of `lean/WeilConjectures` for the item's blueprint ID: no match.
  Search of `dag/lean_names_upstream.json` and both project trees for the chosen
  declaration name: no prior declaration.

Source checked directly: `literature/stacks-project/more-algebra.tex`,
`proposition-epp-essentially-finite-type` (Tag 09II), its p-base preparation
paragraph. The supplied node provides the explicit finite-stage algebra argument
underlying that paragraph; all four steps are retained in the theorem's docstring.
The prescribed CompactObject example is now a withdrawn, declaration-free module
in the read clone; its node record was also read. Current module-mode conventions
from the standing brief are followed.

Validation: the delivered module compiled successfully through the prescribed
`scompile.py` against the live server build, in both the wrapper's sandbox and
library checks. No errors or unexpected warnings. No node fault or
STATEMENT-DISPUTED issue was found. No new nodes or dependency repairs are required.

## Second reading by Q153

Worker rereading of the node and finished Lean source (the maintainer
performs the independent delivery review; no additional agent was started).
Checked every correspondence above against the actual signature: prime and
characteristic hypotheses, the exact Frobenius image scalar field, exponent
bounds p and p^n, the positive height, the actual polynomial quotient, IsField,
the specified basis vectors, the power equality in the direction of the canonical
coefficient map, and the explicit empty-tuple bijectivity clause. No mismatch or
statement correction was needed. In particular the pre-existing height-one
quotient theorem was not misrecorded as an exact match, and no differential
independence hypothesis was substituted. `autoImplicit` is disabled, `u` is
explicit, and the source has no local notation, private construction, or diagnostic
commands. The only postponed proof is the named theorem for the assigned DAG node.

## Repair of return on 3978be65c243

H2 repaired: removed `lem-sfb-simultaneous-root-algebra-api` from `stmt_deps`,
leaving its existing `proof_deps` entry unchanged. Added only the landed
`def-sfb-parameter-root-algebra` definition node to the current base's statement
dependencies. The signature uses `Algebra.pthRootAlgebra (p ^ n) r k b` everywhere
and spells each root class as `Ideal.Quotient.mk _ (MvPolynomial.X i)`.
The owning definition module is a public import; the theorem API is a plain proof
import. The node's mathematical statement and proof are unchanged.

Compared the retained sandbox source and node record with the returned immutable
head shown in the return entry and with the current read-only main node. The
current main node still has no Lean record and retains the four original statement
dependencies. Regenerated the node copy from current main, preserving all of its
fields except the authorized `lean` record and addition of the landed definition
dependency. The Lean signature in the record is extracted verbatim from the file.
All previously reviewed hypotheses and conclusions are definitionally unchanged.
Rereading confirms no use of `Algebra.ParameterRoot.Ring` or `.root` remains in the
statement, and the only theorem proof remains `sorry`.
