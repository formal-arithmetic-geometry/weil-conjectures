## What changed

Proved `AlgebraicGeometry.Scheme.GaloisCover.exists_ordinarySectionEvaluation`
in `Sheaf.ConstructibleSheaf.TorsorOrdinaryEvaluation`, preserving its complete
signature and existing docstring. Added proof-only imports of
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.ConstantSheaf`, and
`Mathlib.Algebra.Module.ZMod`.

The proof follows the node's existing plan. Identify inverse image along the
étale cover with restriction using `Etale.upperStarIsoLocalizationRestriction`.
Forget to abelian sheaves, using `constantCommuteCompose`, and apply the already
proved `Scheme.Etale.constantSheafIsoContinuousMapSheaf` with the discrete topology
on the coefficient group. Evaluation at a point of the connected cover identifies
continuous global functions with coefficients, giving an additive equivalence
between `F(Y)` and the coefficient group. Pull a section back along the first
projection, apply the continuous-function comparison, and compose values with the
inverse of that equivalence. The private, fully proved helper `uliftZModLinear`
uses `ZMod.map_smul` after scalar restriction to make this additive map linear over
`ULift (ZMod ℓ)`.

Naturality follows from the site-adjunction counit's naturality and the
continuous-function comparison's naturality. For normalization, use the diagonal
as a morphism from the terminal étale object upstairs: its composite with the
first projection is the identity. Naturality therefore identifies evaluation on
the diagonal with the original section's global function, whose values agree at
all points by connectedness.

The construction uses no choice from an unproved existence theorem: its only
choices are the supplied trivialization and a point supplied by the connectedness
hypothesis. Empty étale objects require no choice of a point. Zero coefficients,
identity torsors, and coefficients of arbitrary dimension use the same formulas.
The finite group and primality hypotheses remain exactly as in the original
signature, although this ordinary evaluation construction only needs étaleness
and connectedness of the cover.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.GaloisCover.exists_ordinarySectionEvaluation`
(node `lem-weil-pbc-torsor-ordinary-evaluation`). No holes were added, no holes
remain in the delivered module, and no intermediate statements were split off.

The prescribed single-file compiler accepts the module without warnings.
Both source-library proof imports pass `tools/import_direction.py may`.
`#print axioms` reports exactly `propext`, `Classical.choice`, and `Quot.sound`;
the theorem has no transitive `sorryAx` dependency.

## No longer needed

None. Both original public imports remain needed for the unchanged statement and
its torsor section objects. No planned intermediate nodes were imported or
introduced: the source library already supplies the planned restriction and
constant-function comparisons. The original mathematical route and unit route
are unchanged, so no DAG node changes are required.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or interface correction was needed. The one-step proof
plan is implementable directly from existing source-library and Mathlib results.
A separate module-valued constant-function comparison is unnecessary here:
additivity implies linearity over `ZMod ℓ`, including after lifting the coefficient
ring, so the existing abelian comparison suffices.

## Second reading by D3

1. **No accidental interface changes.** Compared the delivered module with the repository version. The theorem signature and all existing declarations are byte for byte unchanged; only proof-only imports, a private helper, and the theorem proof were added.

2. **Proof validity.** Compiled the module with `lcompile.py` successfully. The module has no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. The proof uses only the permitted existing foundations transitively; no new hole was introduced.

3. **Statements and nodes.** The sole theorem statement remains exactly the existing node statement and is proved directly. No split-off statements or nodes were added, so there are no duplicate or weakened intermediate claims to review.

4. **Route and pruning.** The proof follows the existing ordinary evaluation route through restriction, the supplied constant-sheaf trivialization, continuous locally constant functions, connectedness, and the diagonal. Both added imports are used by the proof; no existing import or planned route can be removed.

5. **DAG agreement.** The theorem declaration, blueprint node, proof origin, and proof dependencies agree with the implementation. The unit `sk-thm-p1` route is preserved, and no definition or target statement changed.

I changed only this report section after the review: no Lean source, DAG node, or imports were changed during second reading.
