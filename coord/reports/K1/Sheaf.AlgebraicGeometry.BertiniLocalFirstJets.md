## What changed

Proved `AlgebraicGeometry.exists_bertiniLocalFirstJets` with its original signature,
definitions and public imports unchanged. The proof constructs W as the inverse
image of a projective standard chart and uses the corresponding section as the
frame. The section-preserving projective pair identifies its coefficients with
coordinate ratios. Surjectivity on stalks and affine stalk localization give
polynomial-fraction presentations in their germs.

Added the fully proved module `Sheaf.AlgebraicGeometry.DifferentialFibreLocalFractions`.
Its generic theorem proves that such polynomial-fraction generators span the actual
relative differential fibre. Polynomial induction, Leibniz and multiplication by a
unit denominator prove the algebraic assertion. `import all` reuses the existing
proved private `fieldDifferentialsSelfFibreEquiv` and its germ formula from
`ConormalSequenceSmoothImmersion`; neither that module nor its declarations change.

The item obtains a stalk basis directly from the proved smooth differential
local-freeness theorem, then base changes the basis to the residue field. The
chosen coefficient is 1, so its first jet is (1,0). A proved span argument supplies
the residue-field summand and all differential columns. No closed-point,
algebraic-closure, or dimension-positivity assumption is added.

Both modules compile individually on the project server, without errors or warnings
(the item in 7.3 s, the generic lemma in 3.5 s). The delivery command also runs its
compile and axiom probes. Existing theorem signatures and public imports were
compared textually. All Lean lines are at most 100 characters. No existing shared
interface changes, so no consumer adaptations or change records are needed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_bertiniLocalFirstJets`
(node `lem-zl-bertini-local-first-jets`).

Added zero holes. The new
`AlgebraicGeometry.Scheme.Hom.span_differentialFibreGerm_of_localFractions`
(node `lem-zl-differential-fibre-local-fractions`) is proved completely, as are all
private helpers. There are zero textual sorries in both delivered modules.
This is a proof, not a decomposition into further unfinished obligations.

## No longer needed

No existing import or module is withdrawn; all original public imports remain.
Every added proof import is used. The following former proof dependencies are
unnecessary for this argument:

- `lem-weil-pbc-invertible-generating-sections-fibre` and its module
  `WeilConjectures.AlgebraicGeometry.InvertibleGeneratingSectionsFibre`: the
  classified section-preserving pair and standard chart cover directly supply
  the required generating section and its local frame.
- `lem-weil-pbc-smooth-differentials-free-rank-fibre-dimension` and its module
  `Sheaf.AlgebraicGeometry.SmoothDifferentialsFreeRankFibreDimension`: the prescribed
  smooth relative dimension gives the already proved constant-rank differential
  sheaf theorem directly; taking a local basis and its residue base change suffices.

The conormal short exact sequence theorem itself and a local closed-immersion
factorization are unnecessary. Its module remains needed for the actual fibre
constructions and the proved stalk-to-Kahler comparison used by the new lemma.
The node remains a dependency of that lemma for these proved helpers. These are
local dependency removals, not assertions that other users can be pruned. No
source-library declaration is changed or removed.

## Where the brief, the DAG or earlier work was wrong

The original plan described a conormal-surjection route, but the existing public
interfaces do not directly give its coordinate-generation glue. A direct
polynomial-fraction argument is shorter: it uses the actual classified projective
pair, chart generators, surjective stalk maps and the proved universal-derivation
stalk comparison. The differential calculation is proved rather than split off.
The final argument works at arbitrary residue fields; the closed-point,
algebraically-closed-field first-jet theorem is therefore not used.

Edge cases: the basis construction permits d=0 and its empty differential basis.
The generic differential lemma permits empty or infinite coordinate sets and
requires neither smoothness nor rationality of the point. It cancels actual
R-units, so it does not silently identify the residue field with k. The target
has a nonempty Fin(r+1) family; an empty source open has no z and needs no witness.
The unit's statement and realized proof steps are unchanged.

## New nodes

`lem-zl-differential-fibre-local-fractions`, in
`dag/nodes/sec-deligne-laumon-general/lem-zl-differential-fibre-local-fractions.json`,
is a fully proved criterion for differential-fibre generation from polynomial
fractions. Its sources are Stacks Algebra 00RM (defining differential relations),
00RT (localization and the quotient rule), and Constructions 01UM (the differential
sheaf). LeanSearch, Loogle, Mathlib grep, local library search and blueprint search
found infrastructure but no duplicate. The source proof is expanded as polynomial
induction, the differentiated fraction relation, unit cancellation, differential
span induction and tensor induction. It adds no sorry. The item's node records
the actual route and its remaining dependency union.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
