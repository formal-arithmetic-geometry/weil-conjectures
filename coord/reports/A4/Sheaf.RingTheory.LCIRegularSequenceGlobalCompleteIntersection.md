## What changed

Kept the existing target signature and docstring byte for byte. Replaced its sorry by a
reduction combining three separate steps: the regular-sequence dimension-at-point formula,
a principal neighborhood attaining that dimension, and the algebraic localization presentation.
All three imports are proof-only. The first two steps are proved in new modules; only the
algebraic presentation remains open. No definition or existing statement changed.

The first worker's new helper bundled the presentation and the dimension conclusion under
exactly the target's hypotheses. The second reading replaced it with
`Algebra.exists_principal_localization_presentation_of_local_generators`, which has only
local ideal-generation hypotheses and asserts only the presentation, uniformly under further
localization. Its docstring now supplies the entire clearing-denominators and kernel argument.

## Proved and sorry left

Hole closed: `Algebra.exists_globalCompleteIntersection_of_regularSequence`.
Hole added: `Algebra.exists_principal_localization_presentation_of_local_generators`, node
`lem-weil-pbc-lci-regular-sequence-global-complete-intersection-presentation`.
This is a decomposition: one upper hole closed and one strictly smaller algebraic hole added,
net zero new hole reduction. The target is not claimed axiom-free.

New theorems proved with no local sorry:
`Algebra.regularSequence_dimensionAtPoint` and
`PrimeSpectrum.exists_mul_away_dimension_eq`.
The original proposed helper
`Algebra.exists_principal_localization_presentation_of_regularSequence` is not delivered.
No sorry occurs inside any definition, private helper, or partial proof.

## No longer needed

Removed direct proof-only imports from the item:
`Sheaf.RingTheory.PolynomialQuotientDimensionAtPointHeightDifference` and
`WeilConjectures.Mathlib.Topology.KrullDimension`. Both remain needed transitively by the new
proved dimension steps, so this delivery claims no module pruned from the target import closure.
The new algebraic-presentation module also drops the first worker's unused public imports of
regular sequences and complete intersections; its signature requires neither concept.

The following old proof_deps are no longer direct dependencies of the item; the new node
records retain the appropriate ones within the corresponding lower steps:

- `def-weil-pbc-noetherian-ring`
- `def-weil-pbc-mv-polynomial-ring`
- `lem-weil-pbc-finite-type-algebra-noetherian`
- `def-weil-pbc-localization-at-prime`
- `lem-weil-pbc-localization-noetherian`
- `def-weil-pbc-regular-sequence`
- `lem-weil-pbc-surjective-image-noetherian`
- `lem-weil-pbc-dimension-quotient-nonzerodivisor`
- `def-weil-pbc-krull-dimension-ring`
- `lem-weil-pbc-localization-dimension-chains-below-prime`
- `lem-weil-pbc-polynomial-quotient-dimension-at-point-height-difference`
- `def-kun-topological-dimension-at-point`
- `def-weil-affine-spectrum`
- `lem-weil-pbc-spec-irreducible-closed-subsets-primes`
- `lem-weil-pbc-open-subspace-dimension-monotone`
- `lem-weil-pbc-principal-localization-open-immersion`
- `def-weil-ring-localization-away`
- `def-kun-topological-krull-dimension`
- `lem-weil-pbc-polynomial-coefficient-map-kernel`
- `lem-weil-pbc-localization-away-polynomial-quotient`

`def-weil-pbc-complete-intersection-over-field` remains a direct dependency. The direct proof
uses the three new nodes instead of listing every detail of those arguments at the top node.
No unit-level realized node is bypassed or altered.

## Where the brief, the DAG or earlier work was wrong

The first worker's single presentation-and-dimension hole was essentially the original item
with its conclusion unfolded. Its docstring and node also omitted the actual argument behind
clearing denominators and the dimension choice. The repaired delivery proves the dimension
parts and leaves just the algebraic construction. Searches found the Mathlib regular-sequence
formula and quotient-localization instance, which carry the first proved step. The existing
`Algebra.exists_localization_presentation` in `Sheaf.RingTheory.EquationCountLocalizePresentation`
starts with globally given generators; it does not replace the remaining local-generator step.
LeanSearch returned an internal server error, recorded as unavailable rather than a no-match.

The local literature files are not installed on this machine. Sources were checked online:
[Stacks 00SC](https://stacks.math.columbia.edu/tag/00SC) and
[Stacks 0055](https://stacks.math.columbia.edu/tag/0055).

## New nodes

`lem-weil-pbc-lci-regular-sequence-global-complete-intersection-presentation`: local generators
produce the polynomial presentation on a principal neighborhood and all further localizations;
its only hole is in `Sheaf.RingTheory.LocalCompleteIntersectionPresentation`.

`lem-weil-pbc-regular-sequence-dimension-at-point`: dimension n-e and e≤n from the local
regular sequence, proved in `Sheaf.RingTheory.RegularSequenceDimensionAtPoint`.

`lem-weil-pbc-principal-neighborhood-dimension`: a principal subneighborhood attaining local
dimension, proved for an arbitrary commutative ring in
`Sheaf.RingTheory.PrincipalNeighborhoodDimension`.

No change record is required: the only existing declaration is unchanged in signature.

## Second reading by A4

1. Compared the delivered target with the repository using diff and compared its entire
   signature as raw strings: byte-identical. Its public imports and docstring are unchanged.
   The other three modules are new to the repository. No definition was introduced or changed.
   Verdict: pass.
2. Compiled every delivered file in import order with lcompile.py; no errors or warnings.
   Scanned for forbidden declarations and confirmed that the only delivered sorry is the
   named algebraic-presentation theorem. Explicit #print axioms checks are recorded below.
   Verdict: pass, conditional on the reported hole and upstream open statements.
3. Reviewed the remaining new statement independently against 00SC and its full docstring
   proof: finite generation of I permits a common denominator A with A I⊆(F_i), and the
   identity u=-u(ABx-1)+xB(Au) computes the kernel. It does not assert dimension or regularity.
   Edge cases: e=0 uses the empty ideal and empty products; b=0 gives the relation -1 and
   the zero localization; n=0 works with constant polynomials. I=top admits no prime in S.
   The two proved dimension statements also admit e=n=0; e>n is ruled out by the proved
   inequality. The neighborhood proof handles infinite dimension by well ordering WithBot ENat;
   in a zero ring there is no prime q. Searched Mathlib with LeanFinder, Loogle and grep,
   attempted LeanSearch, and searched the project by dimension and localization terminology.
   No full duplicate found. Verdict: pass.
4. Replaced the bundled hole with a real top-down reduction. The regular-sequence dimension
   formula is used directly from Mathlib; the existing polynomial-quotient height formula is
   used as stated. Proved the neighborhood step from ciInf_mem, the basic-open basis,
   inducing dimension monotonicity, and the localization embedding. Removed unused imports.
   Read dag/units/sk-thm-p1.json: the item realizes no unit-level statement or step, and the
   unit's realized lists are unchanged. Verdict: pass; no closure pruning claimed.
5. Updated the target's proof, proof_deps and proof_origin to the actual three-step reduction.
   All three new nodes have exact verbatim Lean signatures, source, complete proof steps,
   search records, blueprint origin, and created/lean metadata. Verdict: pass.

Changed on second reading: split presentation from dimension, proved both dimension steps,
repaired the remaining helper's mathematical proof and node, removed unused imports, and
corrected the report to call this a net-zero decomposition.

Explicit axiom probes on scratch copies: the principal-neighborhood theorem uses only
`propext`, `Classical.choice`, `Quot.sound`. The dimension-at-point theorem uses those plus
`sorryAx` through the existing polynomial-quotient dimension infrastructure. The remaining
presentation theorem and the target use those plus `sorryAx`, as expected from the named hole.
No other axiom occurs.
