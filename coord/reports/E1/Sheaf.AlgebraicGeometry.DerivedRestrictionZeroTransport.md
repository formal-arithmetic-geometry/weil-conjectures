## What changed

Proved `AlgebraicGeometry.Etale.RawRestrictedComparison.derivedRestriction_zero_transport`
in `lean/Sheaf/AlgebraicGeometry/DerivedRestrictionZeroTransport.lean`, without changing
its signature or any definition. The five private helpers are fully proved: single
composition, single natural-isomorphism transport, the resulting single square,
degree-zero right-derived naturality, and their combination for an abstract exact square.
The final theorem specializes that calculation to the displayed inverse-image functors
and the explicit `rawAffineRestrictedCoefficient` formula.

The existing public import of `RawRestrictedCohomologyComparisonMap` supplies all the
interfaces and proved localization lemmas needed. No imports were added or removed.
The DAG's existing proof plan is followed unchanged; no node update or new node is needed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.RawRestrictedComparison.derivedRestriction_zero_transport`
(node `lem-sbc-derived-restriction-zero-transport`). No `sorry` remains in the delivered
module, and no holes were added. This is a proof, not a decomposition.

The private helpers `single_comp`, `single_nat`, `single_square`,
`zero_single_naturality`, and `square_zero_transport` all have complete proofs.
The single-square argument uses the proved localization factorization lemmas and checks
the remaining complex equations in degree zero. Degree-zero naturality follows from
the proved bounded-below comparison naturality and `rightDerivedZeroIsoSelf` naturality.
No invertibility of the coefficient morphism, nonemptiness of a scheme, or extra
geometric hypothesis enters the proof.

Validation: the full module compiled without warnings using `lcompile.py` in 37.6 seconds
before the final documentation pass. The first delivery dry check also passed compilation
and the axiom probe. Its static review flagged added `open` and local `attribute` commands;
these were removed, and the helpers now use the fully qualified abelian-category class.
The final dry check repeats compilation, the axiom probe, and the static checks. Search used LeanFinder, Loogle, the launcher grep service, and local `rg`;
none supplied the entire statement, while local search found the factorization lemmas
and bounded-below single comparison naturality used in the proof.

## No longer needed

None. No imports, nodes, or modules were pruned. The original proof dependencies
`def-weil-pbc-inverse-image`, `lem-weil-pbc-inverse-image-composition`,
`def-sbc-raw-affine-restricted-cohomology`, and
`def-sbc-raw-restricted-cohomology-comparison-map` remain needed. The unit's route is
unchanged; its `realized` record contains no additional obligation for this helper.

## Where the brief, the DAG or earlier work was wrong

No mathematical or statement error was found. The planned single-object localization
calculation and degree-zero naturality give the statement exactly as written.
Broad rewriting through the scheme-level coefficient formula caused expensive definitional
comparisons. Keeping the calculation abstract and specializing it with the actual raw
pullback projections reduced compilation to within the existing 60-second limit.


## Second reading by E1

1. Compared the delivered module with the repository using `diff`, and separately
   compared the complete public theorem signature byte for byte. Verdict: unchanged
   signature, definitions, visibility, and imports; only five private proved helpers
   and the replacement proof are added. No change record is required.
2. Read all five helper proofs and the specialization. Compiled the module locally
   through `lcompile.py`; inspected a scratch copy with `#print axioms` for every
   helper and the public theorem. No `sorry`, forbidden declaration, hollow definition,
   or data chosen from an unproved existence statement is present. The delivery probe
   additionally checks every generated constant before pushing.
3. No statements were split off and no holes were added. The abstract helper results
   express composition compatibility, natural-isomorphism compatibility, and naturality
   for arbitrary coefficient morphisms. Their proved hypotheses include precisely the
   exactness and resolution assumptions used. Identity and zero coefficient morphisms
   require no special hypothesis; the specialization also permits empty schemes.
4. Checked the localization factors, `Evaluation.zeroIso`, the bounded-below inclusion
   comparison, and the explicit `rawAffineRestrictedCoefficient` definition. Local `rg`
   searches in Mathlib's derived-category sources, upstream algebraic geometry, and
   `lean/Sheaf` found constituent naturality results but no complete replacement for
   this calculation. The sole public import supplies names occurring in the original
   signature and remains necessary. All four old proof dependencies remain used, so
   `## No longer needed` is complete. Read `dag/units/sk-lem-failure-field.json`:
   no realized unit statement or step is bypassed by this helper calculation.
5. Read `lem-sbc-derived-restriction-zero-transport.json` together with the Lean proof.
   Its localization/single-comparison and degree-zero naturality plan, dependency union,
   and source attribution agree with the implementation. No node update is necessary.

Second reading changed only this report: recorded the independent signature, proof,
import, DAG, unit-route, and axiom checks. No Lean repair was needed.
