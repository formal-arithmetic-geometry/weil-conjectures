## Worker report

The module lean/Sheaf/FieldTheory/PBasisDifferentialsBasis.lean states
KaehlerDifferential.exists_basis_differentials_of_pBasis with its sole proof `sorry`.
The node is unchanged except for its lean record. No new nodes or dependency modules
are needed: all objects are expressed using existing Mathlib constructions, without
defining another p-basis predicate or another compositum.

Clause-by-clause correspondence:
- A prime p is `(p : ℕ) [Fact p.Prime]`.
- The field extension K/k is `{k : Type u} {K : Type v} [Field k] [Field K]
  [Algebra k K]`. Both fields' characteristic p is `[CharP k p] [CharP K p]`.
- K^p is `Set.range (fun x : K => x ^ p)`.
- The subfield kK^p is `IntermediateField.adjoin k` of that range. Its definition is
  `Subfield.closure (Set.range (algebraMap k K) ∪ S)`, exactly the smallest subfield
  containing the image of k and all p-th powers. This is a concrete term, not an
  arbitrary intermediate field or an additional hypothesis.
- The indexed family is `{I : Type w} (t : I → K)`, with independent universes for
  the two fields and the index set and no finiteness or nonemptiness assumption.
- The bounded, finitely supported integer exponents are
  `{E : I →₀ ℕ // ∀ i : I, E i < p}`. Naturals encode precisely the nonnegative
  integers in the node. A finsupp has finite support even for infinite I.
- The monomial t^E is `E.val.prod (fun i e => t i ^ e)`, a product over the support;
  factors outside the support equal one and the zero exponent vector gives one.
- The monomials form a vector-space basis over kK^p exactly when `hmon` holds:
  there exists a `Module.Basis` on that exponent index whose E-th value is this
  monomial. This includes both independence and spanning, with no extra condition.
- Ω[K/k] and d are `KaehlerDifferential k K` and `KaehlerDifferential.D k K`.
- The conclusion is existence of a `Module.Basis I K (KaehlerDifferential k K)`
  with value at every i equal to `D k K (t i)`, exactly the asserted basis dt_i.

Dependencies read and used:
- def-pc-field-extension: Mathlib.Algebra.Algebra.Defs, `Algebra` (the field extension
  instances above). Imported transitively through IntermediateField.Adjoin.Defs.
- def-weil-pbc-kahler-differentials: Mathlib.RingTheory.Kaehler.Basic,
  `KaehlerDifferential`, `KaehlerDifferential.D`, and its recorded
  `KaehlerDifferential.linearMapEquivDerivation` universal property were read.
  The first two occur directly in the signature.
- Mathlib.FieldTheory.IntermediateField.Adjoin.Defs, `IntermediateField.adjoin`,
  and Mathlib.LinearAlgebra.Basis.Defs, `Module.Basis`, were also read.

Edge cases checked before writing: empty I has one exponent vector, with monomial
one; hmon then says K has basis {1} over kK^p, hence K = kK^p and Ω[K/k] = 0,
which has an empty basis. Infinite I is allowed and each monomial uses finite
support. A perfect K likewise admits the empty p-basis, without a perfection
assumption in the statement. Duplicate or zero entries in a nonempty t fail the
monomial independence hypothesis as expected. p=0 and p=1 are excluded by the
node's primality assumption. Distinct universes for k, K, I exclude no index set.

Source checked: https://stacks.math.columbia.edu/tag/07P1 (definition item 2) and
https://stacks.math.columbia.edu/tag/07P2 (a) implies (b), including the proof's
quotient presentation. The local literature/stacks-project/more-algebra.tex is
absent on this machine, so the authoritative web pages were opened. No statement
fault, correction, or STATEMENT-DISPUTED issue was found. The docstring carries
all four DAG proof steps and names their inputs for stage 3.

Searches on 2026-10-11:
- msearch.py leanfinder: "For a p-basis of a field extension in characteristic p,
  its differentials form a basis of the Kahler differentials". Eight hits:
  polynomial-ring bases and submersive-presentation/cotangent-space bases only;
  none assert the p-basis theorem.
- msearch.py loogle: "KaehlerDifferential, Module.Basis". Twelve hits, all for
  polynomial rings, generators or submersive presentations; no field p-basis result.
- msearch.py leansearch: "The differentials of a p-basis of a characteristic p field
  extension form a basis of its Kahler differentials". Service unavailable with
  Internal Server Error; no verdict from that service.
- msearch.py grep: "pBasis|p_basis|p-basis|pIndependent" throughout Mathlib.
  Twenty-five unrelated hits (galGroupBasis, expMapBasis, basisOfBasisRight and
  map_basis/exponential-pattern names); no p-basis notion or theorem.
- rg of "pBasis|p_basis|p-basis|PBasis" in the source WeilConjectures and local
  lean/Sheaf: source hits are unrelated basis lemmas; project hits merely cite
  this missing node in docstrings (IntersectionSubfieldsDifferentials,
  KaehlerDifferentialZeroIffPow, DetectNonPthPower). No existing declaration.
- rg of the exact node id in source WeilConjectures: no hit.
- rg of `exists_basis_differentials_of_pBasis` in dag/lean_names_upstream.json,
  Mathlib, source WeilConjectures and lean/Sheaf: no hit; the declaration name is free.

Server compilation via scompile.py completed in 1.3 seconds with exit code 0,
no errors and no warnings. Every variable and universe is bound explicitly.

## Second reading by C1

I independently read the node statement, its Stacks source (More on Algebra, Tags 07P1 and
07P2), and `Sheaf/FieldTheory/PBasisDifferentialsBasis.lean`.

- The prime object is rendered by `(p : ℕ) [Fact p.Prime]`; this is exactly a prime number.
- The field extension is `{k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]`,
  with the node's characteristic hypothesis rendered by `[CharP k p] [CharP K p]`.
- `K^p` is `Set.range (fun x : K => x ^ p)`, and `kK^p` is the concrete
  `IntermediateField.adjoin k` of that range, so no extra intermediate-field hypothesis is
  assumed.
- The family is `(t : I → K)` for arbitrary `I : Type w`; no finiteness or nonemptiness is
  added.  The bounded finitely supported exponent families are
  `{E : I →₀ ℕ // ∀ i, E i < p}`.  Naturals encode the node's integers with `0 ≤ e_i`, and
  `Finsupp` supplies finite support.  The monomial is `E.val.prod (fun i e => t i ^ e)`.
- The monomial basis hypothesis is exactly `∃ b : Module.Basis ... , ∀ E, ...`; it includes
  both spanning and independence over `kK^p` and adds no condition.
- The conclusion is exactly `∃ b : Module.Basis I K (KaehlerDifferential k K),
  ∀ i, b i = D k K (t i)`, matching the family of differentials.

No mismatch was found, so no source, node, or Lean statement was changed.  The empty index
case is covered (the exponent subtype has its zero element and the conclusion is an empty
basis); infinite indices are covered by `I : Type w` and finite support; perfect fields and
zero differentials require no extra hypothesis.  Primality excludes `p = 0` and `p = 1` as
in the source's prime-number assumption.  The independent universes do not remove any case.

I repeated the existing searches (LeanFinder/Loogle/LeanSearch and grep/rg through Mathlib,
`WeilConjectures`, and `lean/Sheaf`) for p-basis predicates and the differential-basis
statement.  They found only polynomial-ring or cotangent-space basis results and no existing
p-basis notion or theorem.  The module compiled cleanly with `scompile.py`; only its intended
`sorry` proof remains.
