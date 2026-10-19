## Worker report

The module `Sheaf.AlgebraicGeometry.BlowupChartRegularSequencePresentation` states the
Tag 0BIQ affine blowup chart presentation as
`AlgebraicGeometry.blowupChartRegularSequencePresentation`. Its proof is `sorry`, as
required for stage 2; no definition data is introduced.

The ring is `{R : Type u}` with `[CommRing R]`. The finite sequence is represented by
`s : ℕ` and `a : Fin (s + 1) → R`; the regular-sequence hypothesis is exactly
`hreg : RingTheory.Sequence.IsRegular R (List.ofFn a)`, so `a 0` is the distinguished
first element and `a i.succ` are the remaining elements. The chart ideal is the span
of `Set.range a`, and the chart algebra is the recorded
`AlgebraicGeometry.AffineBlowup.chartRing (Ideal.span (Set.range a)) (a 0)`.

The polynomial ring is `MvPolynomial (Fin s) R`, with variable `i` representing
`y_(i+2)`. The relation ideal is
`Ideal.span (Set.range (fun i => MvPolynomial.C (a 0) * MvPolynomial.X i -
MvPolynomial.C (a i.succ)))`, rendering every relation `a y_i - a_i`. The conclusion
is an `R`-algebra equivalence from the quotient by this ideal to the chart algebra.
For each `i`, the displayed equation says that the image of the quotient generator
`Ideal.Quotient.mk _ (MvPolynomial.X i)` has underlying localization fraction
`chartFraction (a 0) 1 (a i.succ)`, i.e. `a_i/a`. This records the canonical generator
correspondence while retaining the exact chart object from the dependency. Any two
such algebra maps agree on constants because they are `R`-algebra maps, and agree on
all quotient variables by this equation and injectivity of the chart subtype inclusion.
Polynomial induction and surjectivity of the quotient map then make them equal. Thus
the existential equivalence with its generator formula specifies the canonical map,
including when there are no variables.

Dependency declarations used:

- `Mathlib.RingTheory.Regular.RegularSequence`,
  `RingTheory.Sequence.IsRegular`, for the regular-sequence hypothesis.
- `WeilConjectures.Blowup.Affine.ChartAlgebra`,
  `AlgebraicGeometry.AffineBlowup.chartRing` and
  `AlgebraicGeometry.AffineBlowup.chartFraction`, for the affine chart and its
  fraction notation. The complete source declaration and docstring were read.

The proof plan in the theorem docstring follows every node proof clause: extend the
regular sequence to the polynomial ring coefficientwise; use Koszul regularity for the
explicit degree-one syzygy calculation; deduce that the relation quotient has no
`a 0`-power torsion; evaluate at `a i.succ/a 0` and compute the localization kernel;
and conclude bijectivity and canonicity. The `s = 0` edge case is included: both
`Fin 0` families are empty, the relation ideal is zero, and the presentation reduces
to the one-element chart. I also checked `s = 1` via the regular sequence `(2,T)` in `ℤ[T]`; the one-element sequence
`(2)` in `ℤ`; and arbitrary coefficient characteristic, e.g. `(x,y)` over `𝔽₂[x,y]`.
The zero ring is excluded by the nonzero-final-quotient clause of `IsRegular`.
The distinguished element cannot be zero or a zero divisor under regularity, and a
unit would make the final quotient zero. Rings themselves may have zero divisors;
no domain or Noetherian hypothesis is introduced. The theorem only states the
nonempty sequence case present in the node (`a` is always supplied).

Searches made using `msearch.py Q91
lem-trf-blowup-chart-regular-sequence-presentation`:

- LeanFinder: "The affine blowup chart along a regular sequence is the polynomial
  quotient by a y_i minus a_i". Eight hits on affine open covers, standard etale
  presentations, elliptic-curve quotients, and affine space; no exact chart theorem.
- Loogle: `RingTheory.Sequence.IsRegular, MvPolynomial`. Zero hits.
- grep: `blowup|Blowup|chartRing` in `RingTheory`. One hit: the introductory
  future-blowup comment in `Mathlib/RingTheory/ReesAlgebra.lean`; no declaration.
- LeanSearch: "A blowup chart for a regular sequence has presentation by the relations
  a y_i minus a_i". Eight hits on generic algebra/module presentations and standard
  etale presentations; none has this regular-sequence chart statement.
- Direct `rg` over `WeilConjectures/`, `lean/Sheaf/`, and the upstream name inventory
  for the item id, theorem name, `0BIQ`, and regular-sequence chart presentations:
  no duplicate theorem. A proof docstring in `PermissibleCoordinateChart.lean`
  references this item, but does not state its algebra presentation. The published
  `WeilConjectures.Blowup.Affine.ChartAlgebra` source was read in full through
  `scompile.py --source`; the older local checkout has no copy of that module.

Sources checked: Stacks `more-algebra.tex`, lines 7883--7933, Tag 0BIQ, and
`algebra.tex`, lines 17249--17271, Tag 0G8S. Tag 0BIQ allows the more general
H1-regular hypothesis and explicitly includes regular sequences as an example;
this node is exactly that regular-sequence case, so no correction is needed.
The recorded Mathlib `IsRegular` source was read at lines 131--148, including its
successive-injectivity condition and nonzero-final-quotient condition.

The proof imports are `WeilConjectures.AlgebraicGeometry.KoszulComplex`
(`ExteriorAlgebra.koszulComplex`, full current source read with `scompile.py --source`)
and `Sheaf.RingTheory.RegularSequenceKoszulRegular`
(`RingTheory.Sequence.IsRegular.isKoszulRegular`, full local source read).
Both are imported privately because they belong to the proof plan.

No new nodes, dependency modules, statement correction, or `STATEMENT-DISPUTED` finding
was needed. `scompile.py` compiles the module cleanly; the only postponed proof is the
expected theorem `sorry`.

## Second reading by Q91

This is a self-check because the dispatcher started this worker without a second agent;
the maintainer supplies the independent review. I reread the node, both dependency
records, the complete chart algebra source, and the final theorem signature. Every
hypothesis is present exactly once: a commutative ring, finite sequence length and
entries, and regularity of `List.ofFn a`. Every conclusion clause is present: the exact
polynomial variables, the relation ideal, the quotient-to-chart `R`-algebra
isomorphism, and the generator-to-fraction equation. The quotient uses `C (a 0)` for
scalar multiplication, so it is well-typed for arbitrary commutative rings. No
Noetherian, field, domain, or hidden characteristic assumption was added. The finite
indexing covers the empty-variable and one-variable cases, and the chart algebra is
the recorded canonical construction rather than a private replacement.
