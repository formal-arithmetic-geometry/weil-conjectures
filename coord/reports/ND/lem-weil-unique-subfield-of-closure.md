## Worker report

The module `Sheaf.FieldTheory.UniqueSubfieldOfClosure` states
`FiniteField.exists_unique_subfield_of_closure`, with one whole-proof `sorry`.
No definitions, new nodes, dependency replacements, or statement corrections are needed.
The module and declaration docstrings cite blueprint order 411 and give the DAG's six-step proof.

Hypothesis and clause correspondence:

- The prime `p`, positive integer `a`, and `q = p^a` are `(p a q : ℕ)`,
  `hp : p.Prime`, `ha : 1 ≤ a`, and `hq : q = p ^ a`.
- The field `k₀` with `q` elements is `[Field k₀] [Finite k₀]`
  and `hcard : Nat.card k₀ = q`. This allows any field of the given cardinality,
  rather than only Mathlib's chosen `GaloisField p a`.
- The algebraic closure `k` with structure map ι is `[Field k] [Algebra k₀ k]`
  and `[IsAlgClosure k₀ k]`; the named structure map is `algebraMap k₀ k`.
  The independent explicit universes `u v` allow arbitrary carriers for both fields.
- Every integer `n ≥ 1` is `(n : ℕ) (hn : 1 ≤ n)`; natural numbers encode
  precisely the positive integers under this bound.
- Clause 1 is `∃ E : Subfield k`, `∀ x : k, x ∈ E ↔ x ^ (q ^ n) = x`,
  and `Nat.card E = q ^ n`. The root condition is written directly as the
  equation defining the node's set: evaluating `X^(q^n)-X` at `x` is
  `x^(q^n)-x`, which vanishes exactly when this equation holds.
- Clause 2 is `∀ S : Subfield k, Nat.card S = q ^ n → S = E`.
- Clause 3 containment is `(algebraMap k₀ k).fieldRange ≤ E`.
  Equality of the base-field image with the roots at `n = 1` is
  `∀ x : k, x ∈ (algebraMap k₀ k).fieldRange ↔ x ^ q = x`.
  Its uniqueness is `∀ S : Subfield k, Nat.card S = q →
  S = (algebraMap k₀ k).fieldRange`.
- The consequence that the subfield is well defined follows from the existential
  and uniqueness clauses. The base-field algebra structure through ι is rendered
  by `∃ ι : k₀ →+* E, E.subtype.comp ι = algebraMap k₀ k`.
  A ring map into a field is exactly a field extension datum, and
  `RingHom.toAlgebra` equips it with the corresponding algebra structure;
  the composition equality specifies that it is through the original ι.
  This uses only Mathlib's existing notions, and chooses no data from a sorry theorem.

Dependency declarations read and used:

- `def-weil-finite-field-q-elements`: `GaloisField` and `GaloisField.card`,
  `Mathlib.FieldTheory.Finite.GaloisField`. These represent the chosen finite
  field; the statement allows any isomorphic finite field with that cardinality.
- `def-weil-algebraic-closure`: `IsAlgClosure`,
  `Mathlib.FieldTheory.IsAlgClosed.Basic`, exactly the dependency's recorded
  characterization of an arbitrary algebraic closure.
- `def-weil-polynomial-root`: `Polynomial.eval₂` and `Polynomial.IsRoot`,
  `Mathlib.Algebra.Polynomial.Eval.Defs`. Their evaluation equation reduces to
  the explicit power equation above; no second root predicate is defined.
- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs`,
  with `algebraMap` for the original extension and a ring hom for its corestriction.
- Proof dependencies: `FiniteField.frobeniusAlgEquivOfAlgebraic` and
  `FiniteField.pow_card` in `Mathlib.FieldTheory.Finite.Basic`;
  `galois_poly_separable` in `Mathlib.FieldTheory.Finite.GaloisField`;
  `Polynomial.Splits.eq_prod_roots` in `Mathlib.Algebra.Polynomial.Splits`.
  These Mathlib modules are reached by the two imports; no recorded Sheaf proof
  dependency modules exist for these nodes.

Edge cases checked mathematically: `p = 2`, `a = 1`, and `n = 1` all satisfy
all clauses, including characteristic two. At `n = 1` the subfield is precisely
`fieldRange`. A finite algebraically closed `k` cannot occur, as required by
`IsAlgClosure`; no extra finiteness hypothesis is imposed on `k`.
Zero exponents and non-prime `p` are excluded by exactly the node's hypotheses.
Infinite candidate subfields have `Nat.card S = 0`, so cannot spuriously meet
`Nat.card S = q ^ n` or `Nat.card S = q`, since `q ≥ 2`.
The zero ring is excluded by the field structure. No statement dispute was found.

Searches (all performed before writing; service results logged in `searches.jsonl`):

- msearch LeanSearch: “In an algebraic closure of a finite field with q elements
  the roots of X^(q^n)-X form the unique subfield with q^n elements”.
  Service unavailable (Internal Server Error).
- msearch LeanFinder: “unique subfield of cardinality prime power in algebraic
  closure finite field”. Eight hits, including `FiniteField.Extension`,
  `GaloisField`, `Subfield.fintypeBot`, and cardinality characterizations of fields.
  None states the full result in a prescribed algebraic closure.
- msearch Loogle: `Subfield, Nat.card`. Only `Subfield.card_bot`,
  which concerns the prime subfield, not subfields with arbitrary `q^n` elements.
- msearch grep in `FieldTheory`:
  `exists_unique.*Subfield|∃!.*Subfield|subfield.*card|fixedField`.
  Twenty supporting hits (prime subfield and fixed-field theory); no exact statement.
- rg in the upstream `WeilConjectures` and side-project `lean/Sheaf`:
  `unique_subfield|subfield.*card|Subfield.*card|lem-weil-unique-subfield-of-closure`.
  Only two upstream uses of `Subfield.card_bot`, in `SemilinearFrobenius.lean`.
  No declaration tagged with this node and no duplicate statement found.
- rg of the upstream declaration index for `unique_subfield_of_closure`: no hit.

Validation: `scompile.py ND lem-weil-unique-subfield-of-closure` compiled the
module cleanly on the server in 1.1 seconds, nice 19, two threads, 60-second limit.

## Second reading by ND

Independent second reader: I opened the DAG statement and all six proof steps,
the sandbox Lean file and node record, all four statement-dependency nodes,
and the recorded Mathlib declarations themselves. No mathematical mismatch was
found; the Lean module and node record are unchanged.

Source check: the actual source is the blueprint's
`sec-nagata-compactification/sk-prop-nagata-sketch-comp-category/def-weil-finite-field-fiber.md`,
order 411, rather than a Stacks statement of this whole lemma. Its opening fixes
p prime, a positive, q = p^a, k₀ a field with q elements, and k an algebraic closure,
then specifies the unique subfield of size q^n for every positive n. There are
no further standing hypotheses for this assertion. I also read Stacks
`fields.tex`, section `section-finite` (09HY), and `definition-extension` (09FV)
with `lemma-field-maps-injective` (09FU). These give the finite-field and
field-extension inputs, and introduce no extra conditions. Lang V §5 Theorem 5.1
is explicitly marked unavailable; I have not treated it as obtained evidence.

Object, hypothesis, and conclusion checklist (all verdicts: exact):

1. Prime p: `(p a q : ℕ)` and `(hp : p.Prime)`.
2. Positive integer a and q = p^a: `(ha : 1 ≤ a)` and `(hq : q = p ^ a)`.
   Natural numbers with this bound encode precisely the positive integers.
3. The fixed finite field k₀ of cardinality q: `(k₀ : Type u) [Field k₀]
   [Finite k₀] (hcard : Nat.card k₀ = q)`. A chosen arbitrary field with this
   cardinality is the dependency's notion, without forcing a particular model.
4. Its algebraic closure k and specified embedding ι: `(k : Type v) [Field k]
   [Algebra k₀ k] [IsAlgClosure k₀ k]`; `algebraMap k₀ k` is ι.
   I read `IsAlgClosure`: it asserts both algebraic closedness and algebraicity.
   Its torsion-free prerequisite is automatic for an algebra over a field and
   adds no restriction. The algebra structure encodes an arbitrary ring map.
5. Every integer n ≥ 1: `(n : ℕ) (hn : 1 ≤ n)` follows the field data.
6. Clause 1, roots form a subfield: `∃ E : Subfield k` with
   `∀ x : k, x ∈ E ↔ x ^ (q ^ n) = x`. This specifies exactly the root set:
   `Polynomial.IsRoot` is evaluation equal to zero, and evaluating
   `X^(q^n)-X` gives `x^(q^n)-x`. No separate root notion is introduced.
7. Clause 1, exactly q^n elements: `Nat.card E = q ^ n`.
8. Clause 2, uniqueness among all subfields of k: `∀ S : Subfield k,
   Nat.card S = q ^ n → S = E`. There is no extra containment condition on S.
9. Clause 3, base image lies in E: `(algebraMap k₀ k).fieldRange ≤ E`.
   I read `RingHom.fieldRange`; its carrier is exactly the set-theoretic image.
10. Clause 3, base image is k^(1): `∀ x : k,
    x ∈ (algebraMap k₀ k).fieldRange ↔ x ^ q = x`.
11. Clause 3, uniqueness with q elements: `∀ S : Subfield k,
    Nat.card S = q → S = (algebraMap k₀ k).fieldRange`.
12. Consequence, well-defined subfield and k₀-algebra through ι: the existential
    witness and uniqueness specify the subfield, and `∃ ι : k₀ →+* E,
    E.subtype.comp ι = algebraMap k₀ k` specifies the corestricted map.
    `RingHom.toAlgebra`, whose signature I read, gives precisely an algebra
    structure from this map; its injectivity follows because the domain is a field.
    No chosen data is defined from an existence theorem with a sorry proof.

Dependency audit: `GaloisField` and `GaloisField.card` implement the finite-field
model, while the statement uses its model-independent cardinality notion.
`IsAlgClosure` is explicitly named in the closure node's Mathlib match.
`Polynomial.eval₂` / `Polynomial.IsRoot` and `Algebra` / `RingHom.toAlgebra`
are the existing evaluation, root, and field-extension notions. Their universes
and assumptions admit the objects here. The proof dependencies record Mathlib
matches, not missing Sheaf modules. The existing two imports expose the relevant
Frobenius, finite-field power, separability and factorization declarations.
There are no new nodes, dependency replacements, or statement corrections to audit.

Edge cases: n = 1 identifies E with the base image; a = 1 includes prime fields;
p = 2 causes no sign or separability exception. The bounds exclude exactly
n = 0 and a = 0, and primality excludes p = 0,1. Fields exclude the zero ring.
Independent universes u and v allow every size of both carriers; subfields of k
have their subtype universe, with no restriction on the size of k₀. The closure
need not be finite. Since q ≥ 2, the positive value q^n excludes infinite S
from `Nat.card S = q^n` (infinite types have Nat.card zero). There is no index
family or scheme in the statement, so empty index sets and empty schemes do
not impose a further case. Existence of the subfield is concluded, not assumed.

Independent searches, with different queries from the first reader:

- msearch LeanFinder: "fixed points of powers of Frobenius in algebraically
  closed field form finite subfield of prescribed order". Eight hits, including
  `FiniteField.Extension.frob_apply`, `Extension.exists_frob_pow_eq`,
  `frobeniusAlgEquivOfAlgebraic_apply`, and `frobenius_pow`; these describe
  Frobenius maps or abstract finite extensions, not this whole assertion.
- msearch Loogle: `IsAlgClosure, Subfield`: zero hits.
- msearch grep: `IsAlgClosed.*Subfield|Subfield.*card_eq|fixedField.*card`:
  six hits, principally `IntermediateField.finrank_fixedField_eq_card`, a
  degree formula with finite-dimensional hypotheses, not this theorem.
- Direct rg over Mathlib FieldTheory, upstream WeilConjectures and project
  lean/Sheaf: `subfield.*(unique|cardinality|frobenius)|unique.*subfield|
  fixedPoints.*pow|exists.*subfield`, case insensitive. Hits concerned purely
  inseparable powers, finite-subfield directedness, and unrelated subfield
  models. None states the result. I also read `FiniteField.Extension` and its
  `natCard_extension`: this is a chosen abstract extension, not a unique
  subfield in the prescribed closure. The prime-subfield lemmas
  `Subfield.roots_X_pow_char_sub_X_bot` and `mem_bot_iff_pow_eq_self` only
  concern the prime field, not general q^n. The upstream name index has no
  `unique_subfield_of_closure` declaration.

H5/H6/H8/H9: there are no definitions and exactly one whole-proof sorry.
Both docstrings name the source and blueprint id; the statement docstring
renders all six DAG proof steps in order. Every universe and variable is bound;
there is no private notation, instance, or definition. The node's lean.statement
was compared programmatically with the file signature and is verbatim equal.
No repairs to correct existing work were warranted. Only this second-reading
section was added. Server compilation and delivery preflight are checked below.

Second-reader validation: scompile.py compiled the sole delivered module cleanly
in 1.1 seconds on the server, nice 19, two threads, 60 seconds per file.
The deliver2.py --no-push dry run printed OK: preflight passed and compilation
was clean. No additional sibling modules require compilation.
