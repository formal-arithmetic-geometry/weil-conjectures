## Worker report

The item is already stated by the exact declaration
`WeilConjectures.sixFunctorProjection_reduction_rational` in
`Sheaf.Paper.ProjectionFormulaCoherence` (the shared project source,
`lean/Sheaf/Paper/ProjectionFormulaCoherence.lean`, lines 1192–1197). I therefore
added no module. The node's `lean` record points to that declaration with
`existing: true`; the sorried proof is retained as a stage-2 statement.

The declaration's hypotheses and conclusion match the node clause by clause:

- The finite-field datum, coefficient datum, field, algebra, finite-dimensionality,
  positive integer level, and six-functor datum are the section parameters
  `{D : FiniteFieldDatum.{u}}`, `{C : D.CoefficientDatum}`, `{E : Type u}` with
  `[Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E]`,
  `{n : ℕ} {hn : 1 ≤ n}`, and `(S : SixFunctorDatum D C E n hn)`.
- `f : X ⟶ Y` with `{X Y : SixFunctorSpace D}` and
  `[IsSeparated f.hom.left]` is exactly the separated finite-type morphism
  hypothesis. `c : Compactification f.hom.left` is the supplied compactification.
- `K`, `L`, and `N` have exactly the raw rationalized constructible categories
  in the node: `sfRationalConstructibleCategory C.l E X.obj.left` for `K` and
  `sfRationalConstructibleCategory C.l E Y.obj.left` for `L,N`.
- The conclusion is exactly
  `sixFunctorProjectionRationalReductionSquare S f c K L N`, whose definition
  expands to the normalized rational associators, rational pullback tensor
  comparison, and compact-support projection components in the displayed tensor
  action equation. It quantifies over arbitrary `N`; there is no finite-Tor,
  flatness, invertibility, or quotient restriction.

The recorded dependency declarations used by the predicate are the existing
interfaces: `WeilConjectures.SixFunctorDatum` from
`Sheaf.Paper.SixFunctorDatum`; `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage`
from `Sheaf.Paper.ExchangeProjectionSuppliedDomains`; the compact-support
projection component from `Sheaf.Paper.ConstructibleProjectionMates`;
`WeilConjectures.canonicalCommonStagePullbackTensor` from
`Sheaf.Paper.CompletedPullbackTensorComparison`; and
`WeilConjectures.sfRationalConstructibleCategory` from
`Sheaf.Paper.SfRationalizationKaroubi`. The fixed operation datum and its
normalization data are inherited by `SixFunctorDatum`.

Edge cases checked against the statement and definition: `N` is arbitrary,
including zero and the tensor unit; `f` may be an identity morphism; the source
scheme may be empty; and the formula has no excluded characteristic or finite-Tor
case. The source docstring explicitly says that constant quotient tensors are
included as special cases and that the theorem is for all `N`.

Searches made:

- `msearch.py ... leanfinder "rational constructible projection map tensor associativity compactification"`:
  only unrelated Proj pullback associativity declarations; no match.
- `msearch.py ... loogle "CategoryTheory.MonoidalCategory.associator, CategoryTheory.Adjunction"`:
  zero hits (the query also reports the unknown identifier).
- `msearch.py ... grep "sixFunctorProjection_reduction_rational|sixFunctorProjectionRationalReductionSquare" Sheaf`:
  zero hits in the search subdirectory; direct `rg` in the project then located the
  exact declaration in `Sheaf/Paper/ProjectionFormulaCoherence.lean`.
- Direct `rg` over the shared `lean/WeilConjectures` and `lean/Sheaf` trees found
  no competing declaration in the upstream source and found the exact shared
  declaration recorded above.

No new node, dependency module, statement correction, or
`STATEMENT-DISPUTED` flag is needed.

## Second reading by NH

In a second pass I reread the node and the source declaration. The binder order,
separatedness instance, compactification, three rational constructible inputs,
and exact reduction-square conclusion all agree. The predicate definition uses
the datum's rational tensor, support, pullback, normalized associators, and
rational pullback comparison, so it renders every clause of the node's displayed
equation and preserves the arbitrary-third-input requirement. No hypothesis is
added or omitted, and the existing declaration is used rather than recreated.


The full formula was checked by expanding the predicate (source lines 1153–1178).
Writing `TX = S.higher.rationalTensor X`, `TY = S.higher.rationalTensor Y`,
`F = S.higher.rational.support f c` and `U = S.higher.rational.pull f`, its left
side is `(TY.flip.obj N).map (compactSupportProjectionComponent ... K L)`
followed by `compactSupportProjectionComponent ... ((TX.obj K).obj (U.obj L)) N`.
The first factor is precisely `P(K,L) ⊗ 1_N`, and the second is
`P(K ⊗ UL,N)`. Its right side first applies the hom of the normalized `aY`,
then `P(K,L ⊗ N)`, then `F.map ((TX.obj K).map (sixFunctorProjectionRationalMu
S f L N).hom)`, then the separate `F.map` of the inverse normalized `aX`.
Thus the final two images under F remain separate and in the exact order of
the node. The source and target are `(FK ⊗ L) ⊗ N` and
`F((K ⊗ UL) ⊗ UN)`. The `letI` witnesses in the existing predicate derive
invertibility of ell from the field-base hypotheses; they impose no assumption
on the theorem's inputs. The helper `sixFunctorProjectionRationalMu` uses
`canonicalRationalPullbackTensor` and conjugates by the specified operation
equalities; `sixFunctorProjectionTensorAssociator` similarly transports the
canonical rational associator by the specified tensor equality. No arbitrary
comparison is substituted.

Additional searches run on 2026-10-28 UTC:

- LeanSearch: “Projection formula right tensor action associativity rational
  constructible sheaves”; eight general monoidal action and tensor results,
  none about this compactification projection.
- Corrected Loogle: `CategoryTheory.Adjunction, "projection"`; zero hits.
- Mathlib grep: `projection.*([Tt]ensor[Aa]ction|[Aa]ssociat)|rational.*projection`;
  five unrelated projection/tactic hits.

The exact current blueprint statement and proof for `prop-sf-pf-coherence` were
read. Its final clause refers to `prop-sf-pf-reduction` (1); the item's recorded
source expands its rational-stage tensor-action content. There is no released
repair note for this item in the shared read clone.
