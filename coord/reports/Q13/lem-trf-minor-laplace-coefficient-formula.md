## Worker report

The module `Sheaf.LinearAlgebra.Matrix.MinorLaplaceCoefficientFormula` states
`Matrix.det_eq_sum_complementaryMinors` with one `sorry`. It introduces no definitions.
The node's mathematical statement, dependencies, and proof are unchanged; only `lean`
is added. No statement dispute, missing notion, or dependency-interface fault was found.

Hypothesis and clause correspondence:

- The arbitrary commutative ring is `{R : Type u} [CommRing R]`; `u` is explicitly
  declared, and no nontriviality, domain, field, or characteristic hypothesis appears.
- The nonnegative integers are `{q s : ℕ}` and the upper bound is `(_hs : s ≤ q)`.
  `Q : Matrix (Fin q) (Fin q) R` is the given square matrix. The increasing relabelling
  from `Fin q` to the source's `[q]` sends `i` to `i.val + 1`.
- The arbitrary retained column subset is `(T : Finset (Fin q))` with
  `(hT : T.card = s)`. It need not be an initial segment or a singleton.
- The equality has left side `Q.det`, rather than an ideal-membership conclusion.
- The sum `∑ I : {I : Finset (Fin q) // I.card = s}, ...` indexes exactly the
  subsets of size `s`, with one term per subset. The membership proof is propositionally
  irrelevant, so this subtype does not multiply the number of summands.
- Its sign is the explicitly cast integer power
  `(((-1 : ℤ) ^ ((∑ i ∈ I.val, (i.val + 1)) + ∑ j ∈ T, (j.val + 1))) : R)`.
  Thus the exponent uses the actual one-based labels in the node, not an undocumented
  parity adjustment, and the sign is mapped along the canonical integer ring map.
- The first minor is `Q.submatrix (I.val.orderEmbOfFin I.property)
  (T.orderEmbOfFin hT)`. Both maps enumerate their subsets increasingly and have domain
  `Fin s`; the matrix is square, with the rows and columns in the required order.
- The second minor uses `(I.valᶜ).orderEmbOfFin (k := q - s)` and
  `(Tᶜ).orderEmbOfFin (k := q - s)`. The cardinality certificates simplify
  `Finset.card_compl` using `I.property` and `hT`; these are actual proof terms,
  with no postponed theorem or extra hypothesis. Both domains are `Fin (q - s)`.
- The summand is precisely the sign multiplied by those two determinants.
  The standard determinant and finite-product conventions handle the empty cases;
  the statement does not exclude them or assert an additional conclusion.

Dependency declarations read and used:

- `def-weil-matrix`: `Matrix`, in `Mathlib.LinearAlgebra.Matrix.Defs`.
- `def-weil-submatrix`: `Matrix.submatrix`, in the same module. The recorded general
  reindexing interface applies directly to the canonical increasing embeddings.
- `def-weil-pbc-matrix-determinant`: `Matrix.det` and its column-index Leibniz formula
  `Matrix.det_apply'`, in `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`.
- The ordering API is Mathlib's `Finset.orderEmbOfFin` in
  `Mathlib.Data.Finset.Sort`; its definition/docstring specifies the increasing
  bijection onto the subset. No private submatrix or ordering construction is added.
- The already recorded proof dependency `Equiv.Perm.sign_orderedBlocks` in
  `Sheaf.GroupTheory.OrderedBlockPermutationSign` is imported without `public`.
  Its complete signature and proof docstring were read, including the matching
  one-based exponent and the increasing complementary enumerations.

Source checks: read `literature/stacks-project/more-algebra.tex`,
`lemma-ideals-generated-by-minors` (Tag 07Z7), including its omitted-proof
row/column-expansion hint. The generalized coefficient identity and its four-step
Leibniz proof are explicitly agent-supplied in the accepted DAG node, not a verbatim
Stacks assertion. Read the nearest ancestor's statement and proof in the current
`literature/blueprint/latest/.../sk-i-curve-zero/lem-trf-local-term-locality` files;
they contain no replacement determinant statement. The module accurately records
this provenance and includes all four proof steps from the node.

Edge cases checked mathematically before finalizing the statement:

- `s = 0`: `T` and the only summation row subset are empty; the exponent is zero,
  the first determinant is one, and the complementary determinant is `Q.det`.
- `s = q`: both selected subsets are full; the exponent is twice the sum of all
  labels, the complementary determinant is one, and the selected matrix is `Q`.
- `q = 0`: the bound forces `s = 0`; the sum has one empty-subset term and all
  determinants are empty determinants, so both sides equal one.
- For a two-by-two matrix and the second retained column, the formula is
  `-Q(1,2)*Q(2,1) + Q(2,2)*Q(1,1)`, giving the required determinant and sign.
- Zero rings, characteristic two, singular matrices, and nonunits are allowed.
  Nothing in the statement requires cancellation or invertibility.

Searches made with the prescribed `msearch.py Q13 <item>` wrapper:

- `leanfinder`: "Laplace determinant expansion along an arbitrary subset of columns
  as a signed sum of products of complementary minors". Eight hits included
  `Matrix.det_succ_column`, `Matrix.det_succ_row`, the zero-index versions,
  row/column-sum formulas, `Matrix.adjp_apply`, and an adjugate formula.
  These do not state the expansion along arbitrary column subsets.
- `loogle`: `Matrix.det, "submatrix"`. Eight hits concerned simultaneous reindexing,
  absolute determinants, the one-entry adjugate formula, principal submatrices,
  and special row/column-sum identities. No exact statement match.
- `leansearch`: "Generalized Laplace determinant expansion along a fixed subset of
  columns by complementary minors". Eight hits concerned one-row/one-column
  expansion, adjugates, `Matrix.det`, and block reindexing; no exact match.
- `grep`: `laplace|Laplace|complementary.*minor|minor.*complement`, restricted to
  Mathlib `LinearAlgebra/Matrix`. Three hits: one `detp` row expansion in
  `SemiringInverse.lean`, and two first-column expansion references in
  `Determinant/Bird/Correctness.lean`. No arbitrary-subset identity.
- `rg -n -i 'laplace|complementary.*minor|minor.*complement'` in the project's
  `lean/WeilConjectures` and `lean/Sheaf`: hits concern complex-splitting by invertible
  complementary minors, single-column Cech calculations, and geometric rank proofs;
  none states this coefficient identity. A node-id grep in `lean/WeilConjectures`
  returned no matches. The proposed declaration name was also absent from Mathlib,
  `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`.

Validation: `scompile.py Q13 <item> <module>` successfully compiled both the sandbox
and module-path versions on the server, with no errors or warnings. The first
elaboration probe needed the complementary enumeration size made explicit as
`k := q - s`; that repair is present in the delivered signature.

## Second reading by Q13

This is the author's second pass; the dispatcher brief forbids starting another
agent and assigns the independent review to the maintainer after delivery.
I reread the node and the complete final module together. The ring, sizes, upper
bound, square matrix, selected column cardinality, all row subsets of that size,
integer sign, both ordered minors, and equality conclusion match the correspondences
above. In particular, the summation subtype is finite and counts each subset once;
the exponent uses `i.val + 1`; both complementary matrices are indexed by exactly
`Fin (q - s)`. No empty case, ring characteristic, or retained column subset is
excluded. The only implementation repair was supplying the explicit complementary
size to avoid unresolved elaboration metavariables. No mathematical mismatch was
found, and no node correction, new node, or dependency module was necessary.
