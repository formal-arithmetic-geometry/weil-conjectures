## Worker report

This delivery states `ValuationSubring.primeSpectrum_comap_orderIso_of_isAlgebraic` in
`Sheaf.RingTheory.ValuationAlgebraicHeight`. Its only theorem has proof `sorry`.
There are no new definitions, helper theorems, extra nodes, dependency modules, or
statement changes. The copied item differs from the base only in `lean`.

### Hypotheses and clauses

| Natural statement | Lean rendering |
| --- | --- |
| Fields K and E, and the specified field extension E/K | `(K : Type u) (E : Type v) [Field K] [Field E] [Algebra K E]`; the embedding is `algebraMap K E`. Universes u and v are independent. |
| The extension is algebraic | `[Algebra.IsAlgebraic K E]`, whose field is `∀ x : E, IsAlgebraic K x`. |
| V is a valuation subring of E, with the membership-or-inverse-membership alternative for every nonzero element | `(V : ValuationSubring E)`. Mathlib's bundled condition quantifies over every element; at zero it is automatic since every subring contains zero. It is equivalent to the node's nonzero-element formulation. |
| A = V intersect K | `V.comap (algebraMap K E)`. Mathlib defines its underlying subring as the inverse image of V. Because the field structure map is injective, this is precisely the stated intersection with the embedded K. |
| A is a valuation ring of K | The same `ValuationSubring.comap` has type `ValuationSubring K`, carrying its proved valuation alternative. This clause is supplied by the canonical construction, without assuming a new hypothesis on A. |
| Contraction of prime ideals gives an order isomorphism onto the prime ideals of A, ordered by inclusion | `∃ e : PrimeSpectrum V ≃o PrimeSpectrum (V.comap (algebraMap K E)), ...`. The following equality for every `p` requires `e p` to be `PrimeSpectrum.comap` of the restriction of `algebraMap K E` from A to V. Thus the isomorphism is exactly contraction, rather than an unspecified correspondence. |
| V and A have the same height, the supremum of the lengths of finite strict prime chains | `ringKrullDim V = ringKrullDim (V.comap (algebraMap K E))`. Mathlib defines `ringKrullDim R` as `Order.krullDim (PrimeSpectrum R)`, which is the supremum of lengths of `LTSeries`. |
| Both heights are finite, or both infinite | The equality is in `WithBot ℕ∞`, retaining the value `⊤`. Both rings are nonzero domains, so both spectra contain the zero prime and the extra value `⊥` cannot occur. Hence equality includes exactly the stated finite/infinite alternative. |

The restricted field map is constructed with the existing `RingHom.restrict`.
Its membership witness `fun _ hx ↦ hx` is the defining preimage membership of A,
not a new assumption, arbitrary map, choice, or postponed construction.
No local notation, local instance, `let`, `show`, auto-implicit variable, or
universe equality occurs in the signature.

### Dependencies and declarations read

- `def-pc-field-extension`: `Mathlib.Algebra.Algebra.Defs`, `Algebra`. I read its
  full class declaration and docstring; the node's record specifies the field
  instance convention used here.
- `def-weil-algebraic-element`: `Mathlib.RingTheory.Algebraic.Defs`, `IsAlgebraic`,
  and the extension form `Algebra.IsAlgebraic` explicitly recorded in its match
  and note. I read both declarations and docstrings. The extension form means
  every element is algebraic; no finite-degree or separability hypothesis occurs.
- The additional standard APIs are `ValuationSubring`, `ValuationSubring.comap`,
  `RingHom.restrict`, `PrimeSpectrum.comap`, and `ringKrullDim`. I read their
  source definitions and docstrings in Mathlib's valuation-subring, subsemiring,
  prime-spectrum ring-homomorphism, and Krull-dimension modules respectively.
- The proof dependency `lem-trf-valuation-value-group-torsion` has no recorded
  Lean module or Mathlib match in the current DAG. It is therefore not imported,
  as permitted for an unstated proof dependency by stage 2 rule 7. Its exact
  positive-power-times-unit statement is included in the proof plan; its module
  should be added as a proof-only import when that node is stated. No statement
  dependency is missing.

The theorem docstring carries all six proof steps of the node, including the
explicit inverse `q ↦ radical(qV)`, the two inverse identities, both order
directions, and the comparison of all finite chain lengths.

### Edge cases and source check

Checked E = K (identity restriction); V = E (both spectra have only the zero
prime and dimension zero); the zero prime in a nonfield valuation ring; ramified
DVR extensions; purely inseparable extensions; and infinite-degree algebraic
extensions and arbitrary/infinite height. There is no nontrivial-valuation,
Noetherian, discreteness, rank-one, separability, finite-generation, finite-degree,
or characteristic restriction. A chain of length zero is allowed. The rings
cannot be zero rings because they are subrings of fields.

I read Stacks `algebra.tex`, lemma-valuation-ring-cap-field (Tag 052L), and
lemma-characterize-valuation-ring (Tag 090Q), plus `more-algebra.tex`,
lemma-etale-extension-valuation-ring (Tag 0ASJ), first proof paragraph, which
corroborates the finite-index power-times-unit input. The node's Temkin PDF is
absent from the local literature; I do not claim to have read it. The existing
node and N0 report already record that absence and the agent-origin ideal proof.
No source-based correction is needed: the natural statement is true, and the
Lean states it unchanged. No STATEMENT-DISPUTED finding.

### Searches

The following actual queries were run under group Q56 and this item:

- `msearch.py leanfinder`: “For an algebraic extension of fields and a valuation
  ring upstairs, contraction is an order isomorphism of prime spectra of the
  valuation ring and its restriction, and their Krull dimensions agree”. Eight
  results; none is the statement. The results include localizations, the
  valuation-ring/overring correspondence, and maximal-ideal contraction for
  compatible valuations.
- `msearch.py leansearch`: “In an algebraic extension E of a field K, contraction
  of prime ideals of a valuation subring V of E to V intersect K is an order
  isomorphism and preserves Krull dimension”. Eight results. The localization
  correspondences concern localization rather than restriction to an algebraic
  subfield; `ValuationSubring.primeSpectrumOrderEquiv` has an order-dual spectrum
  and compares it with overrings inside one field. I read its signature and
  definition and the ring-equivalence `PrimeSpectrum.comapEquiv`; neither is
  this statement.
- `msearch.py loogle`: `ValuationSubring, Algebra.IsAlgebraic`; zero results.
- `msearch.py grep` in `RingTheory/Valuation`:
  `comap.*(algebraic|IsAlgebraic)|((algebraic|IsAlgebraic).*(height|krullDim|primeSpectrum))`;
  zero results.
- Direct `rg` in `WeilConjectures` and `lean/Sheaf` for
  `valuation.*(algebraic|height)|[Ii]sAlgebraic.*ValuationSubring|primeSpectrum.*[Aa]lgebraic|algebraic.*primeSpectrum`:
  only unrelated references to algebraically closed valuation fields and the
  Temkin proof plan. Direct item-id search in `WeilConjectures`: no match.
- Direct Mathlib, upstream, and side-library search for the chosen full-name
  suffix `primeSpectrum_comap_orderIso_of_isAlgebraic`: no existing declaration.

### Validation and previous delivery diagnosis

`scompile.py Q56 lem-trf-valuation-algebraic-height` compiled the delivered file
cleanly, both sandbox and library-path passes, with no errors or warnings.
The signature is copied verbatim into `lean.statement`; all lines of the module
are at most 100 characters. Only the item's `lean` record is changed.

The previous attempt reported that N0 had already merged the item. I checked the
node, the N0 report, the ledger and delivery log: that merge split the DAG in
stage 1 and supplied no Lean record or module. It therefore does not complete
this stage-2 statement task. This packet adds the missing Lean declaration.

## Second reading by Q56

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
