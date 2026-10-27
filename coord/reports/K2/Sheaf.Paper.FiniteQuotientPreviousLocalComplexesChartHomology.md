## What changed

Proved `AlgebraicGeometry.Scheme.finiteQuotient_previous_local_complexes_chart_homology`
with its existing signature and public imports unchanged. All additions are private,
proved helpers in the item module. Added proof imports for exact slice restriction,
commutative constant realization, the ordinary coefficient adjunction, derived-functor
uniqueness, and exact algebraic restriction of scalars. The existing normalized
coefficient adjunction is reused through a proof-only `import all` of
`Sheaf.Paper.CompletedAdicCoefficientDatum`.

The argument computes homology using the canonical localization representatives,
transports the supplied derived slice comparison, and uses the compatibility square
to identify the successor coefficient action. The constant-restriction comparison is
constructed by the module-sheafification adjunction and proved invertible by local
bijectivity. No flatness of the quotient map is assumed. A private generic transport theorem
keeps the assembly independent of the adic definitions. Local irreducibility of the
chosen derived-category and scalar-extension data avoids expanding their construction
during elaboration, without altering any shared definition. Updated the item's DAG proof
to describe this argument and its actual dependencies.

## Proved and sorry left

Closed the one existing hole in
`AlgebraicGeometry.Scheme.finiteQuotient_previous_local_complexes_chart_homology`
(node `lem-weil-pbc-finite-quotient-previous-local-complexes-chart-homology`).
Added zero holes; no `sorry` remains in the delivery. This is a proof, not a decomposition.

Validation: the complete item module compiled cleanly through `lcompile.py` in
46.5 seconds, below the unchanged 60-second file limit. The theorem signature
and public imports were also compared verbatim with the shared source.

## No longer needed

None. The original public imports remain necessary for the statement. The original
four proof dependencies are all used, and no node or module is withdrawn. No boundedness,
projectivity, finiteness, or covering argument is needed for this homology transport;
these belong to the existing parent chart argument.

## Where the brief, the DAG or earlier work was wrong

The already-proved ordinary coefficient adjunction from `sec-smooth-purity` is used
as a general ringed-site algebra tool: the proper-base-change unit has no separate
normalized ordinary extension/restriction adjunction. Its source and statement are
unchanged.

No statement correction was needed. Exactness here is exactness of restriction of
scalars along the quotient, not flatness of that quotient. Ordinary scalar extension
is exact only where used along the assumed coefficient isomorphisms. The supplied
comparison need not come from a map of the chosen complexes: it is used as an
isomorphism in the derived category via the homology functor.

The construction works for the zero module, zero coefficient rings, an empty slice,
all integer homology degrees, and n = 0. Its sheafification maps and the inverse-ring
restrictions use no nontriviality or nonemptiness assumption.

## Related modules compiled before delivery

3 related module(s) compiled against this delivery by deliver3.py: 3 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FiniteQuotientPreviousLocalComplexesChartHomology": "5f3d0572a5eb1deb42b30dac1910ce62ab595bc6"}, "results": {"Sheaf.AlgebraicGeometry.DiscreteConstantPresentationLifting": {"hash": "858429f71b9670b1576d281d5ef61632c572f34a", "status": "OK"}, "Sheaf.Paper.DiagonalSourceQuotientNormalization": {"hash": "e493663b21d9409cd36c8939658cc6108a34871b", "status": "OK"}, "Sheaf.Paper.FiniteQuotientPreviousLocalComplexesAux": {"hash": "6743e61a20945dfac2347156c748aa7f39728e30", "status": "OK"}}, "seconds": 112, "time": "2026-10-28T06:36:41+0800", "transitive": 2, "version": 1}
```

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
