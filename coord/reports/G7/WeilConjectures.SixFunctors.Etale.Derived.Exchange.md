## What changed

Flagged `AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerShriek`
as `STATEMENT-DISPUTED` in the item module. The disputed theorem
and every existing public import keep their original signatures and proof bodies. The two already-proved principal-ideal corollaries now use the existing quotient
comparison API directly through the proved private helper
`isDualizable_constantSingle_principalQuotient`. This replaces the longer compact-support
compactification/associator construction and shares the zero/nonzero generator case split. This packet reports a source/interface
dispute; it does not claim a proof or a mathematical counterexample.

The original module was copied into the assigned sandbox and compiled successfully through
`lcompile.py` (40.3 seconds). The searches and the precise mismatch are recorded below.

## Proved and sorry left

Holes closed: **0 of 1**. Holes added: **0**. Split-off statements: **0**.

The one original hole remains:
`AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerShriek`.
It is a theorem, not a definition. No matching node attachment was found: searching all
`dag/nodes` for the module and declaration finds neither, and `dag/lean_audit.json` records
this declaration with `nodes: []`. The older unit record `sk-prop-sf-pf-reduction` lists its
name, but its statement concerns finite coefficient stages. The current proposition node
`prop-sf-pf-reduction` is attached to the different pro-etale theorem
`WeilConjectures.projectionFiniteReduction` in `Sheaf.Paper.ProjectionFiniteReduction`.

The finite-ring and principal-ideal-of-domain variants in the item were already proved.
Their statements are preserved; both principal-ideal proofs are simplified,
and neither is counted as a newly closed hole.

## No longer needed

None. No imports, modules, nodes, or declarations are withdrawn. Both principal-ideal
corollaries now apply the existing dualizable-quotient comparison after the proved private
helper checks dualizability once. The helper uses the already-imported zero-ideal and
span-power dualizability theorems. The compact-support corollary no longer assembles the
direct-image and open-factor isomorphisms with functor associators. No attached DAG node
was found for either corollary. The mathematical route (perfect quotient coefficients)
and all public statements are preserved. In particular the unused
unrestricted theorem is preserved under the source-library boundary. No replacement lemma
or proof-dependency import is added.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the sole remaining theorem claims a natural isomorphism on the entire
unbounded derived categories for every commutative ring `Λ`, every ideal `J`, and every
compactifiable scheme morphism. Its cited finite-reduction source does not state that.

The unit `dag/units/sk-prop-sf-pf-reduction.json` and the corresponding archived blueprint
unit concern `A_{E,n} -> A_{E,m}` for finite rings and constructible finite-Tor objects. The
unit's argument invokes the finite projection formula. It supplies neither arbitrary rings
nor an arbitrary-ideal unbounded theorem. The current blueprint proof of
`lem-fix-operation-reduction` also uses standard DVR quotients, which are perfect. Thus
there is no numbered node plan proving the actual unrestricted Lean hole from the stated
dependencies. The missing node attachment is a separate audit defect.

The shortest existing proof routes were checked by reading their actual declarations:

- `isIso_rightDerivedLowerStarProjectionMap_of_isProper`, in
  `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula`, requires
  `IsAddTorsion Λ`. This hypothesis is not available for arbitrary `Λ`.
- `isIso_rightDerivedLowerShriekReductionModIdealMap`, in
  `WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction`, requires
  `[Finite Λ]`. It proves the already-present finite variant.
- `isIso_rightDerivedLowerShriekDerivedTensorRightMap_of_isDualizable` in that module
  requires the constant quotient complex to be dualizable. An arbitrary ideal does not
  provide that hypothesis.
- The span-power variants require a nonzerodivisor; the module's domain/principal variant
  and `LowerShriekReduction`'s weakly-regular-sequence variant implement precisely that
  route. Arbitrary quotient modules need not have a finite projective resolution.
- `ConstantTensorProjection` requires a noetherian ring and preservation of countable
  coproducts by the derived direct image. Neither is assumed by the hole. The proper
  coproduct theorem in `LowerShriekLeftAdjoint` again requires additive torsion.

Edge cases `J = 0`, `J = top`, identity morphisms, finite coefficient rings, and regular
principal quotients do not refute the theorem. A singular quotient such as the residue
field of `Q[e]/(e^2)` shows that perfectness cannot simply be inferred; it is **not**
presented as a counterexample to the theorem. No counterexample to the full unrestricted
assertion was established. The dispute is that this is an additional stronger assertion,
unsupported by the named source and the currently stated proof dependencies, not that a
failed proof search proves it false. No false intermediate statement is introduced.

Source checks: [Stacks 0F0G](https://stacks.math.columbia.edu/tag/0F0G),
[095U](https://stacks.math.columbia.edu/tag/095U), and the local file
`literature/stacks-project/etale-cohomology.tex`, labels
`lemma-projection-formula-proper-mod-n` (Stacks 0F0G),
`lemma-cohomological-dimension-proper` (095U), and `lemma-pull-out-constant-mod-n`.
The unbounded proper projection theorem explicitly assumes a torsion ring. The general
ringed-topos projection formula
([Stacks 0943](https://stacks.math.columbia.edu/tag/0943)) requires a perfect second factor. These
sources do not justify applying either result without those hypotheses.

Searches actually run through `msearch.py` for this group and item:

- LeanFinder: `proper derived pushforward commutes with tensor quotient by arbitrary ideal
  coefficient ring` returned eight ordinary tensor/quotient and completion lemmas, none a
  derived pushforward comparison.
- Loogle: `"reductionModIdeal"` returned zero hits.
- Mathlib grep: `projection.*(constant|isProper)|PreservesColimits.*rightDerivedLowerStar`
  returned seven unrelated locally-constant-function and normed-module hits.
- Direct `rg` over both Lean roots found no general replacement; the applicable source
  declarations and their hypotheses are listed above.

The source-library exception list contains no entry for this declaration. Accordingly this
packet does not add a finite/torsion/perfectness hypothesis, remove the declaration, replace
its body by a different assertion, or modify the exception list. The independent reader
should resolve the source/interface dispute and missing node attachment before assigning
an unrestricted proof or authorizing a corrected upstream statement.

Compilation follow-up: the first dry run passed compilation and preflight. Several later
full-file attempts hit the unchanged 60-second limit. An imports-only scratch diagnostic
passed in 25.9 seconds. A full scratch copy with `profiler` and `trace.profiler` enabled then
passed in 56.4 seconds: cumulative elaboration was about 1.06 seconds, type checking about
51.1 seconds, and private-module linting about 48.8 seconds (asynchronous phases overlap).
A tested proof-local transparency option did not cure the timeout and was removed. The
final optimization instead shares principal-quotient dualizability in a private proved helper and gives each comparison an explicit `IsIso` type. The full final module compiled
cleanly in **39.2 seconds**. No profiler or transparency setting remains in it. No limits or checks
were increased or disabled, and no diagnostic scratch module is delivered.

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
