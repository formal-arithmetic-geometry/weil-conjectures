## What changed

Replaced the proof hole in `AlgebraicGeometry.etaleBrownLevelComparisons` by a
combining proof from four local comparison statements, each in its own new module.
The existing theorem's statement and public imports are unchanged. The proof
constructs the open extension comparison as the inverse mate of the given
inverse-image comparison, using the proved
`CategoryTheory.isIso_inverseMate_of_equivalences`. It proves the open mate equation
by the inverse law of `mateEquiv`.

The final compact-support equation is proved by expanding the two pasted
isomorphisms. Naturality of the proper realization moves the open projection past
it. The local open and proper scalar squares then apply, and naturality of
`scalarMate` identifies their composite with `compactScalarMap`. Cancellation of
the scalar realization and level comparison gives exactly the original five-factor
transport equation. This pasting calculation is complete Lean, not a new assumption.

Added private proof imports of `EtaleBrownLevelRealization`,
`EtaleBrownImageRealization`, `EtaleBrownProperScalarTransport`,
`EtaleBrownOpenScalarTransport`, and the existing `InverseMateEquivalence`.
Updated only the item's own DAG proof route and added the four local nodes.
No existing shared definition, statement, instance, attribute or public import changed.
The wrapper subtype types are unfolded only in the local pasting proof; no
reducibility attributes are changed.

Validation: the four new modules compiled individually in 5.3–8.4 seconds, and
the main combining proof compiled in 26.5 seconds, using the server compiler.
The original theorem signature and the DAG declaration/signature records were
checked against the source. The finite-field characteristic and torsion hypotheses
remain unchanged; the stronger local comparison statements do not need them.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.etaleBrownLevelComparisons`.
Its module has zero remaining holes. This is a decomposition, not a complete proof
of the mathematical theorem: four strictly smaller obligations were added, so the
packet closes one hole and adds four (net minus three).

Every remaining hole added by this delivery is a public theorem with proof exactly
`by sorry`, a source, a proof in words, and its own node:

- `AlgebraicGeometry.etaleBrownLevelRealization_exists` —
  `lem-pur-etale-brown-level-realization`: realization at one scheme, with no
  geometric image or projection assertion.
- `AlgebraicGeometry.etaleBrownImageRealization_exists` —
  `lem-pur-etale-brown-image-realization`: realization of one geometric image,
  with no scalar projection or compact-support assertion.
- `AlgebraicGeometry.etaleBrownProperScalarTransport` —
  `lem-pur-etale-brown-proper-scalar-transport`: only the proper scalar mate and
  its local transport square, assuming the realizations.
- `AlgebraicGeometry.etaleBrownOpenScalarTransport` —
  `lem-pur-etale-brown-open-scalar-transport`: only the open scalar projection and
  its local square, assuming the realizations and open comparison. It contains
  no proper-image or compact-support pasting conclusion.

The new statements were checked on identity coefficient maps, the zero quotient
ring, identity scheme maps, and the empty open. No nonzero-ring, regularity,
completeness, Tor-amplitude, boundedness or separated-target assumption was added.
The proper local step uses finiteness of the source quotient ring, which suffices
for the published proper scalar projection theorem. The supplied finite-field and
torsion assumptions are retained verbatim in the original theorem.

## No longer needed

No existing Lean module was withdrawn and no existing import was removed.
No global module-pruning claim is made.

The original direct proof dependency
`lem-pur-coefficient-system-derived-comparison` is not applied: its Lean theorem
constructs evaluation/image packages under regularity and completeness assumptions,
whereas this item compares an arbitrary supplied package over an arbitrary O and t.
The supplied package's universal derived units and transpose equations are the
appropriate inputs to the local image comparison instead.

The original constant-ring equivalence, exact-localization, proper tensor-unit,
open scalar-exchange, conjugation and mate-pasting nodes remain ingredients of the
four local proof plans. Their dependency edges now occur at those local nodes.
The original theorem itself needs only the four local statements and the existing
inverse-mate equivalence theorem; its last pasting step is elementary naturality
and cancellation. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The current server queue assigns one proof hole. The archived build-error file
reports a bad import of `EtaleBrownProjectionRealization`; the unchanged original
module compiled against the current dependency state, so that historical failure
was not reproduced. The rework archive and all existing attachments are preserved.

The planned application of `coefficientSystemDerivedComparison` does not fit the
arbitrary supplied packages, as explained above. The four local statements make
that comparison work explicit instead of silently identifying separately chosen
packages. None is the full original conclusion under another name: geometry,
scalar projection, and the composite calculation have separate mathematical roles.
The module now proves the composite calculation and the open inverse-mate step.

## New nodes

`lem-pur-etale-brown-level-realization` records the constant-ring and exact-localization
construction for one supplied coefficient evaluation package, in
`Sheaf.Paper.EtaleBrownLevelRealization`.

`lem-pur-etale-brown-image-realization` records the ordinary sectionwise comparison,
universal right-derived unit comparison, and inverse mate for one morphism and
one coefficient level, in `Sheaf.Paper.EtaleBrownImageRealization`.

`lem-pur-etale-brown-proper-scalar-transport` records the proper scalar mate's
invertibility and its single-factor realization square, in
`Sheaf.Paper.EtaleBrownProperScalarTransport`.

`lem-pur-etale-brown-open-scalar-transport` records the open scalar projection and
its single-factor realization square, in `Sheaf.Paper.EtaleBrownOpenScalarTransport`.
All four inherit the original source and unit and include the executed searches.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.EtaleBrownImageRealization": "f7527741b0db43cb55136431b0294b4aa1a8d7e5", "Sheaf.Paper.EtaleBrownLevelComparisons": "e09d064564846ac276b9f0c7829c8466ee06fa2d", "Sheaf.Paper.EtaleBrownLevelRealization": "95c153213423d75448028ba9ba5384a25e4eab26", "Sheaf.Paper.EtaleBrownOpenScalarTransport": "5896654c9db2867acb3ff221e1c677feb268abd5", "Sheaf.Paper.EtaleBrownProperScalarTransport": "cc5df7cf35acf5f465216736128631b58c49ba0f"}, "results": {"Sheaf.Paper.EtaleBrownGeometricComparisons": {"hash": "25963ce8089e94e3831cf1beade33a99f1ea4963", "status": "OK"}}, "seconds": 167, "time": "2026-10-28T01:08:15+0800", "transitive": 0, "version": 1}
```

## Second reading by M6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
