## Worker report

Module: `Sheaf.RingTheory.ExistsNegativeValuationOfTensorSurjective`.
Declaration: `IsDiscreteValuationRing.exists_negative_valuation_of_tensor_surjective`.
This states the item with a sorry proof; no definitions or auxiliary results are introduced.

Hypothesis and conclusion correspondence:
- A field K: `{K : Type u} [Field K]`, with explicit universe `u`.
- A subring A of K: `(A B : Subring K)`; both embeddings are the canonical subring inclusions.
- K is the fraction field of A: `[IsFractionRing A K]`, using the canonical subring algebra.
- B is a DVR: `[IsDiscreteValuationRing B]`. Its integral-domain structure is inherited
  from the field K; the class supplies the local principal ideal ring and nonfield conditions.
- K is the fraction field of B: `[IsFractionRing B K]`.
- The normalized valuation: Mathlib's `(IsDiscreteValuationRing.maximalIdeal B).valuation K`
  has values in the multiplicative integers with zero. The corresponding additive valuation
  on nonzero elements is its negative `WithZero.log`. A uniformizer has multiplicative
  value `WithZero.exp (-1)`, so this expression is 1 on a uniformizer, as required.
  Thus choosing the canonical normalized valuation does not restrict the valuation:
  the normalized valuation associated with a DVR is unique.
- Surjectivity of the canonical tensor map: `h : Function.Surjective
  (Algebra.TensorProduct.productMap A.subtype.toIntAlgHom B.subtype.toIntAlgHom)`.
  It is over ℤ, the unadorned tensor product of rings in the source, and sends a pure
  tensor to the product of its images in K.
- There is a nonzero x in A: `∃ x : A, x ≠ 0 ∧ ...`.
- Its normalized valuation is negative:
  `-WithZero.log ((maximalIdeal B).valuation K (x : K)) < 0`.
  Nonzero x remains nonzero in K, so the logarithm's arbitrary value at zero is irrelevant.

Dependency used: `def-sc-discrete-valuation-ring` is a Mathlib leaf, with declaration
`IsDiscreteValuationRing` in `Mathlib.RingTheory.DiscreteValuationRing.Basic` (read lines
56–60 and the uniformizer equivalence at lines 91–96). This is imported transitively by
`Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing`.
Other existing interfaces read and used: `IsDiscreteValuationRing.maximalIdeal` in that
latter module; `IsDedekindDomain.HeightOneSpectrum.valuation` in
`Mathlib.RingTheory.DedekindDomain.AdicValuation` (definition and docstring, lines 315–325);
`WithZero.log` in `Mathlib.Algebra.GroupWithZero.WithZero`;
`Algebra.TensorProduct.productMap` in `Mathlib.RingTheory.TensorProduct.Maps`
(definition, docstring and pure-tensor formula, lines 803–816);
`RingHom.toIntAlgHom` in `Mathlib.Algebra.Algebra.Hom`.

Source checked: https://stacks.math.columbia.edu/tag/09N5, proof, induction base case r=1.
The local literature/stacks-project/varieties.tex is not present on this machine; the
Stacks page gives the same base-case argument. No source or node statement correction
was needed.

Edge cases checked: A=B cannot satisfy surjectivity, since its image is B, a proper
subring of K. A=K has the inverse of a uniformizer as witness. Zero cannot be a witness.
A field B is excluded by the DVR class exactly as in the dependency. Positive and zero
characteristic are both covered, and no finiteness or Noetherian condition on A is added.

Searches (2026-10-11):
- msearch.py leanfinder: "surjective tensor product of subrings of a field implies an
  element has negative discrete valuation": eight hits on generic valuation results,
  valuation surjectivity and DVR membership; none state the tensor-surjectivity result.
- msearch.py loogle: "IsDiscreteValuationRing, Valuation": twelve hits, including
  DVR membership and adic valuation results, none stating this item.
- msearch.py grep: "tensor.*surject.*valuation|surject.*tensor.*fraction": zero hits.
- msearch.py leansearch: "surjective tensor product of subrings into a fraction field
  gives negative DVR valuation": unavailable (Internal Server Error); no verdict claimed.
- rg in pinned Mathlib, WeilConjectures and lean/Sheaf for
  `exists_negative_valuation_of_tensor_surjective|tensor.*surject.*valuation|surject.*tensor.*valuation`:
  no hits. Also searched the source for the node id with grep: no hits, and searched
  dag/lean_names_upstream.json for tensor-surjectivity/negative-valuation names: no hits.

Validation: scompile.py compiled the module cleanly, exit code 0, in 1.6 seconds.
No node faults or disputed statements found. No new nodes or dependency modules needed.


## Second reading by E1

Independent reading on 2026-10-11, with the original node, sandbox node and Lean module
open. Verdict: the Lean signature says exactly what this node says; no statement,
module, dependency or node-record repair was needed. Only this review was appended.

Source: Stacks `varieties.tex`, `lemma-create-globally-generated` (Tag 09N5),
read from https://raw.githubusercontent.com/stacks/stacks-project/master/varieties.tex,
and checked against https://stacks.math.columbia.edu/tag/09N5. The local literature
checkout has no Stacks tex file. The source starts with domains with common fraction
field, reduces the B_i to DVRs, and then proves the r = 1 case by contradiction:
if there is no negative valuation in A, then A is contained in B and tensor
multiplication cannot cover K. No Noetherian or finiteness assumption on A occurs.
The Noetherian, dimension-one and local conditions on B are already consequences of
being a DVR, so they require no additional binders here.

Object/hypothesis/conclusion inventory and correspondence (H3):

- Field K: `{K : Type u} [Field K]`. Correct, arbitrary universe.
- Subring A of K: `(A B : Subring K)` introduces A as an actual subring, not an
  abstract ring with an unspecified map. Correct; its domain structure is inherited.
- Fraction field of A is K: `[IsFractionRing A K]`. Read the abbreviation in
  `Mathlib.RingTheory.Localization.FractionRing`: localization at the nonzero
  divisors, with the canonical subring algebra. Correct, no extra algebra binder.
- DVR B with fraction field K: `B : Subring K`, `[IsDiscreteValuationRing B]` and
  `[IsFractionRing B K]`. Correct: the embedding implicit in the node's canonical
  map is expressed by the subring inclusion.
- Dependency `def-sc-discrete-valuation-ring`: its exact recorded Mathlib leaf is
  `IsDiscreteValuationRing`, `Mathlib.RingTheory.DiscreteValuationRing.Basic`.
  Read the declaration and `irreducible_iff_uniformizer`: a local principal ideal
  domain whose maximal ideal is nonzero, precisely the node's notion, not a field.
  The imported valuation module uses that same class. No replacement is needed.
- Associated normalized valuation on K nonzero: the conclusion uses
  `-WithZero.log ((maximalIdeal B).valuation K (x : K))`. Read `maximalIdeal`
  in `Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing`, `valuation`,
  `valuation_of_algebraMap` and `intValuation_singleton` in
  `Mathlib.RingTheory.DedekindDomain.AdicValuation`, and `log`/`log_exp` in
  `Mathlib.Algebra.GroupWithZero.WithZero`. A uniformizer has multiplicative
  value `exp (-1)`, so this additive expression equals 1. Correct sign and scale.
  The normalized valuation associated with B is unique, so using this canonical
  expression rather than binding an arbitrary normalized representative changes
  neither hypothesis nor conclusion. No new definition or private copy is needed.
- Tensor multiplication is surjective: the binder `h : Function.Surjective
  (Algebra.TensorProduct.productMap A.subtype.toIntAlgHom B.subtype.toIntAlgHom)`.
  Read `RingHom.toIntAlgHom` and `productMap` with its pure-tensor formula:
  the domain is A tensor over Z B and a pure tensor maps to `(a : K) * (b : K)`.
  Correct: unadorned ring tensor product and the canonical inclusions, not tensor
  over A or B and not an arbitrary surjective linear map.
- Existential nonzero element in A: `∃ x : A, x ≠ 0 ∧ ...`. Correct order of
  quantification; coercion into K is injective, so this is nonzero in K as well.
- Negative integer valuation: the second conjunct is the displayed additive
  expression `< 0`. Correct, strict inequality in Z, with no omitted clause.

Edge cases: zero cannot be a witness, so `log 0 = 0` has no effect. A = B cannot
satisfy the surjectivity hypothesis since all products and sums remain in the proper
subring B. A = K is covered, with inverse of a uniformizer as a witness. Subrings of
a field are nonzero unital domains, and a field B is excluded exactly by the DVR
notion; no zero-ring case is discarded beyond the stated hypotheses. Both positive
and zero characteristic are covered. There is no index set, scheme or integer n
in this single-DVR statement; empty indices, empty schemes and n = 0 introduce no
additional cases. Arbitrary `u` covers every ambient field and its subrings, without
a finiteness or countability restriction.

Independent H4 searches, with wording different from the first worker:

- LeanFinder via msearch.py: "multiplication map from tensor product of subrings onto
  field forces an element outside valuation ring". Eight hits, including
  `exists_lift_of_le_one`, valuation-ring containment and integer-lifting results;
  none states this tensor-surjectivity implication.
- Loogle via msearch.py: `Algebra.TensorProduct.productMap, Function.Surjective`.
  Zero hits.
- LeanSearch via msearch.py: "If multiplication A tensor B to K is onto and B is a
  valuation ring then A contains an element outside B". Service unavailable with
  Internal Server Error; no absence verdict inferred from it.
- rg in pinned Mathlib RingTheory, WeilConjectures and repository lean/Sheaf for
  `tensor.*(valuation|Valuation)|[Ss]urject.*productMap|negative.*valuation|valuation.*negative`.
  Only unrelated tensor-evaluation documentation and adic-valuation documentation;
  no existing statement. Also checked `dag/lean_names_upstream.json` and lean/Sheaf
  for tensor/valuation combinations and the full declaration name: no matches.

H5/H6/H8/H9: no definitions, auxiliary theorems, hollow data or proved results are
introduced. The only theorem has a `sorry` proof as required for stage 2. Both
module and declaration docstrings name 09N5 and the blueprint id. The declaration's
proof text covers all three node proof steps, including the inverse uniformizer,
finite tensor expression, nonnegative-product contradiction (with all three proof
nodes named), and the resulting witness. The namespace, topic directory and imports
follow the project conventions. All variables and the universe are explicitly bound.
There are no new nodes, dependency modules or statement_change to review (H12/H13).

Validation: scompile.py compiled the delivered module on the server, exit code 0,
with no warnings, in 1.6 seconds. Independently checked that `lean.statement` is
verbatim the signature preceding `:= by` in the file. No mismatches found; unchanged
Lean and node retained rather than rewritten.
