## Worker report

The module `Sheaf.NumberTheory.Padics.CoprimeCongruenceKernelRigidity` states
`Padic.coprime_congruence_kernel_rigidity` with proof `sorry`. Its only auxiliary
declaration is the real definition `Padic.coefficientExtensionRepresentationReduction`,
the homomorphism `A_n` explicitly introduced by this node. It composes Mathlib's
entrywise general-linear-group map with `A`, using the canonical ideal quotient map.
It supplies no extra assumption and makes no arbitrary choice of a map.

Clause-by-clause correspondence:

- The prime is `(l : ℕ) [Fact l.Prime]`.
- The finite extension is `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`.
- The extending absolute value, integer ring, chosen uniformizer and positive-level
  quotient rings are exactly the recorded coefficient-extension constructions.
  `coefficientExtensionIntegers l E` is the integer subring for
  `coefficientExtensionAbsoluteValue l E`. `coefficientExtensionIdeal l E n`
  is `(Ideal.span {coefficientExtensionUniformizer l E}) ^ n`, equal to
  `Ideal.span {coefficientExtensionUniformizer l E ^ n}`. The target of the
  reduction is the existing `coefficientExtensionRing l E n`. Thus no independent
  integer ring, uniformizer or norm is introduced.
- The arbitrary group is `(H : Type v) [Group H]`, with universe independent of `E`.
  No topological structure or continuity assumption occurs.
- The nonnegative integer rank is `(r : ℕ)`. Rows and columns are `Fin r`.
- The representation is `A : H →* Matrix.GeneralLinearGroup (Fin r)
  (coefficientExtensionIntegers l E)`. Mathlib defines this general linear group as
  units in the matrix ring, with both inverse identities, exactly as requested.
- `A_n` is `coefficientExtensionRepresentationReduction l E H r A n`.
  Its body is `(Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk
  (coefficientExtensionIdeal l E n))).comp A`. Mathlib's `map_apply` says its
  `(i,j)` entry is the quotient of the original `(i,j)` entry.
- `Q_n` is `(coefficientExtensionRepresentationReduction l E H r A n).range`.
  `MonoidHom.range` is the subgroup whose underlying set is `Set.range A_n`.
- Finiteness at every positive level is the hypothesis `hfinite`, quantifying
  `∀ n : ℕ, 1 ≤ n → Finite ...range`.
- The hypothesis `hcoprime` quantifies over precisely the same levels and asserts
  `(Nat.card ...range).Coprime l`, which is the stipulated gcd condition.
  `Nat.card` counts the elements of the image subgroup, not the ambient matrix group.
- `K_n` is `A_n.ker`. Mathlib's kernel is exactly the subgroup of elements mapped
  to `1`, and the identity of the matrix unit group has identity matrix as its value.
- The conclusion quantifies `∀ n : ℕ, 1 ≤ n →` and asserts the conjunction
  `A_1.ker = A_n.ker ∧ A_n.ker = A.ker`. This is exactly `K_1 = K_n = ker A`.
  `A.ker` has the same identity-preimage interpretation for the integral matrix group.

Dependencies read and used:

- `def-weil-l-adic-coefficient-extension`: recorded module
  `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, declaration
  `Padic.finite_coefficientExtensionRing`; this publicly imports the actual
  constructions from `Sheaf.NumberTheory.Padics.CoefficientExtension`:
  `Padic.coefficientExtensionAbsoluteValue`, `Padic.coefficientExtensionIntegers`,
  `Padic.coefficientExtensionMaximalIdeal`, `Padic.coefficientExtensionUniformizer`,
  `Padic.coefficientExtensionIdeal`, `Padic.coefficientExtensionRing` and the
  transition homomorphisms. Their full definitions and docstrings were read.
- `def-weil-matrix`: `Mathlib.LinearAlgebra.Matrix.Defs`, `Matrix`; imported through
  `Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs`, which additionally supplies
  `Matrix.GeneralLinearGroup` and `Matrix.GeneralLinearGroup.map`.
- Canonical quotient and subgroup operations are `Ideal.Quotient.mk`,
  `MonoidHom.range`, and `MonoidHom.ker`; their defining signatures were inspected.
- Proof dependency `lem-weil-l-adic-extension-integers-dvr` is
  `Padic.extension_integers_dvr`, module
  `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`, already publicly imported by the
  coefficient constructions. Its entire statement and proof-plan docstring were read.
- Proof dependency `def-weil-l-adic-numbers` has Mathlib match `Padic`, from
  `Mathlib.NumberTheory.Padics.PadicNumbers`, already publicly available through the
  coefficient dependency. Its definition and completion docstring were read.
- Proof dependency `lem-sfb-finite-matrix-group-coprime-power` has Mathlib match
  `Nat.Coprime.pow_left_bijective`, module `Mathlib.GroupTheory.OrderOfElement`;
  its exact signature was read and its module is imported for the future proof.

Source inspection: `pdftotext -f 3 -l 3 literature/stanford-weil2-seminar/L19.pdf -`
confirms that Proposition 1.1.9 supplies the integral representation and finite-level
reduction context. As the DAG explicitly records, this algebraic kernel corollary is
an agent supplement, not a theorem asserted on that page. The theorem docstring
reproduces every step of the node's algebraic proof: `l ∈ π𝒪`, square-zero power
calculation, coprime-power kernel induction, norm separatedness, and assembly.

Edge cases checked before writing:

- `r = 0` remains allowed: `Fin 0` is empty; the unit group of empty matrices is
  trivial and all three kernels are the whole group.
- `n = 1` is included, with the first equality reflexive. `n = 0` is excluded by
  `1 ≤ n`; the auxiliary formula still makes sense at level zero without asserting
  rigidity there.
- The trivial group and the trivial representation satisfy the hypotheses and have
  the asserted kernels. An infinite abstract group is allowed without any restriction.
- Every prime, including `l = 2`, and ramified coefficient extensions are allowed.
  The proof only needs `l ∈ π𝒪`, not an equality between `l` and the uniformizer.
- Image cardinality is taken on the image subgroup itself. Finiteness and coprimality
  are explicitly required at all positive levels, not only at the first reduction.
- Both universes are explicitly declared and every binder is explicit or an explicit
  typeclass binder. No local notation, local instances, hidden lets or additional
  positive-rank assumptions occur.

Searches for an existing statement (all through the prescribed `msearch.py Q61
lem-sfb-coprime-congruence-kernel-rigidity` wrapper unless stated otherwise):

- `leanfinder`: "A representation over the integers of a finite extension of Q p
  whose reductions have finite order coprime to p has first congruence kernel equal
  to its kernel". Eight hits, including `PadicInt.ker_toZModPow`,
  `PadicInt.ker_toZMod`, Selmer-group kernel lemmas and
  `Representation.FiniteCyclicGroup.coinvariantsKer_eq_range`; none states this result.
- `loogle`: `Matrix.GeneralLinearGroup.map, Ideal.Quotient.mk, MonoidHom.ker`.
  Zero hits for that combined query; the individual operations were subsequently
  located and read directly in Mathlib source.
- `grep`: `(congruence|uniformizer).*(coprime|kernel)|(coprime|kernel).*(congruence|uniformizer)`.
  Twenty hits, all generic congruence-relation kernels or unrelated cardinality and
  kernel-pair material; no matching filtered matrix-kernel theorem.
- `leansearch`: "A matrix representation over a p-adic integer ring with all finite
  congruence images of order coprime to p has equal congruence kernels". Eight hits:
  generic ring congruence kernels, modular congruence groups, `PadicInt`, and scalar
  quotient-kernel lemmas; no matching theorem.
- Direct `rg -n` in both `lean/WeilConjectures` and `lean/Sheaf`, and in
  `dag/lean_names_upstream.json`, for coprime/congruence combinations,
  kernel/rigidity combinations and the proposed helper names. Only unrelated flat
  closed-fibre rigidity appeared. The new declaration names do not occur there.
- Required `grep -rn 'lem-sfb-coprime-congruence-kernel-rigidity'
  lean/WeilConjectures`: no result. Searches of coefficient-extension names found
  the recorded constructions, which are used directly.

No statement correction, new node, dependency repair or disputed statement is needed.
The original node is changed only in `lean`. The auxiliary definition is recorded in
`lean.declarations` and carries the owning node's blueprint/source docstring.

Validation: the delivered module compiled cleanly with the prescribed `scompile.py`
against the live published build, separately as a sandbox and library module
(7.3 s and 6.9 s). The theorem's whole proof is `sorry`; no theorem is proved here.

## Second reading by Q61

This is the worker's explicit final clause audit, not an independent-agent review;
the dispatch brief forbids starting another agent and assigns independent review to
the maintainer. Re-read the node and delivered file together. The prime, finite field
extension, recorded integer ring and chosen uniformizer, arbitrary abstract group,
rank including zero, integral representation, entrywise quotient homomorphism,
image finiteness and coprimality at every positive level all match as detailed above.
The two conjuncts give both equalities in the requested chain, as subgroup equalities
with exactly the prescribed identity preimages. No mismatch was found and no natural
language statement was changed. The helper uses the canonical Mathlib map rather
than an arbitrary reduction map. There is exactly one postponed theorem, with the
complete five-step proof in its docstring.
