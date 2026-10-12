## What changed

Proved `AlgebraicGeometry.Scheme.picard_h1_restriction_compatibility` by constructing the
invertibility witness via uniqueness of tensor pullback, using pullback of free generators,
and reducing the Picard equality to an equivariant generator-torsor map. Added the intermediate
module `Sheaf.AlgebraicGeometry.UnitsTorsorClosedRestriction`, which explicitly constructs the
direct-image units torsor and states the remaining closed-immersion H¹ comparison.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Scheme.picard_h1_restriction_compatibility`.
Added one strictly simpler hole below: this is a decomposition (one hole closed and one
added), not a net decrease of holes or a claim of an axiom-free target proof.
The item module has no remaining `sorry`; its complete combining proof compiles.
The new theorem `AlgebraicGeometry.Scheme.unitsTorsor_closed_restriction_class` remains `sorry`
and is recorded by node `lem-sc-units-torsor-closed-restriction-class`.
The definition `unitsTorsorClosedPushforward` is a concrete construction with no `sorry` data.

## No longer needed

Removed the item's proof-only imports `Sheaf.CategoryTheory.Sites.TorsorH1Functoriality`
and `Sheaf.Topology.ClosedImmersionPushforwardCohomology`.
The item no longer directly needs node `lem-sc-torsor-h1-functoriality`: its change-of-group
part is supplied by the source library's proved `Sheaf.Torsor.classH1_eq_map_of_equivariant`,
and its direct-image part is now precisely the new comparison lemma.
The item no longer directly needs `lem-sc-cohomology-closed-immersion-pushforward`, whose
current theorem states existence of an isomorphism, not the required value of the specified
canonical comparison. Closed-pushforward comparison theory remains in the new lemma's proof
plan via `lem-sc-closed-pushforward-boundary-naturality`; it is not globally pruned.
Hilbert 90 and tensor pullback remain needed. No blueprint unit statement or step is bypassed.
Removed the unused proof import `Mathlib.Topology.Sheaves.SheafCondition.Sites` from the
new module after verifying compilation without it.
Removed the redundant item import
`WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator`: it is already publicly
imported through GmPicard and ProjectionFormula.
No claim is made that a removed module is unreachable from all other targets.

## Where the brief, the DAG or earlier work was wrong

The current `CategoryTheory.Sheaf.torsor_h1_functoriality` signature quantifies over arbitrary
`eG`, `eG'`, `hφ`, `push`, `eF`, `eIF`, `hI`, and `direct` without hypotheses specifying their
compatibility with the canonical constructions. In particular its first clause would assert
compatibility for an arbitrary map of H¹ sets and an arbitrary torsor map. This is not usable
as a sound functoriality theorem; this delivery does not use it or alter its signature.
The report flags that declaration as STATEMENT-DISPUTED: missing canonical-map hypotheses.
The replacement intermediate fixes both class maps to `Sheaf.Torsor.classH1` and fixes the
comparison to `unitsPushforwardCohomologyComparison`, with the direct-image torsor constructed
explicitly. It is strictly smaller than the item: it contains no line bundle, module pullback,
Picard class, generator map or units-restriction cohomology map.
The original three proof steps require this concrete compatibility theorem; the existing
closed-embedding theorem supplies only an existential isomorphism with a different Ext
universe, not this equality. The replacement node's third step explicitly records the need to
identify the boundary comparison with the inverse-image/counit map. The direct-image torsor construction must handle opens disjoint from
the closed image separately; this is included in its definition and proof documentation.

## New nodes

`lem-sc-units-torsor-closed-restriction-class` records the remaining comparison theorem, with
source Tags 02FQ and 02UV as used in Tag 09NY. Its module is
`lean/Sheaf/AlgebraicGeometry/UnitsTorsorClosedRestriction.lean`.

Searches used the project's logged wrappers: LeanFinder returned ring-theoretic Picard
functors and no sheaf torsor comparison; Loogle returned no `classH1` or `Torsor, Sheaf`
match; Mathlib grep found only ordinary algebraic torsor pushforwards. LeanSearch was
unavailable (HTTP internal-server error), recorded as unavailable rather than no match.
The source library supplied the proved `IsFreeGenerator.pullback_unit_app` and
`classH1_eq_map_of_equivariant` lemmas. The repository contains only literature indexes on
this machine; Stacks Tags 09NY, 02FQ, 02UV and 0095 were read from their official pages.
The new lemma's edge cases checked in words are identity immersion, empty Z, and nonreduced
closed subschemes; neither surjectivity on global units nor triviality of the line bundle
is assumed. Both modules compile with the project wrapper without errors or warnings.

## Second reading by A3

1. Compared the delivered item with the repository by diff and extracted the existing
   theorem signature: it is byte for byte identical. No existing definition, statement,
   public import or target was changed. No change record is required. Verdict: pass.
2. Compiled both modules in dependency order using lcompile.py, without errors or warnings.
   Independently compiled scratch copies with #print axioms for the item, new construction,
   and comparison. The construction uses only propext, Classical.choice and Quot.sound;
   the two theorems additionally use sorryAx from open theorem dependencies. The only
   textual hole is unitsTorsor_closed_restriction_class. No prohibited declaration or
   sorry data occurs. The adjunction witness used in the item determines its left adjoint
   up to natural isomorphism; it is not arbitrary existence data. Verdict: pass.
3. Read the new comparison and its complete proof docstring against Stacks Tags 02FQ,
   02UV and 09NY (https://stacks.math.columbia.edu/tag/02FQ,
   https://stacks.math.columbia.edu/tag/02UV,
   https://stacks.math.columbia.edu/tag/09NY). The canonical inverse-image/counit map has
   the asserted direction; naturality of boundaries and the constant-one comparison
   give the stated equality. Identity, empty Z, disjoint opens and nilpotent thickenings
   cause no exception. The construction extends a trivializing open using closedness
   and uses the unique empty-open section off the image. This is strictly a part of the
   Picard argument, with no line bundle or change-of-units-sheaf clause. Independent
   LeanFinder search for boundary naturality under inverse image, Loogle search for
   classH1 and mapFunctor, Mathlib grep for torsor pullback/comparison, and rg across
   lean/ found no proved replacement. The existing boundary/pushforward declarations
   do not identify the specified Ext comparison directly. No closure in a few minutes
   was available. Verdict: pass as a decomposition, not an axiom-free proof.
4. Read the source classH1_eq_map_of_equivariant theorem and the free-generator pullback
   route. The combining proof uses those proved results directly and retains Hilbert 90
   and tensor pullback. No simpler applicable proved theorem was found. No longer needed
   lists both old proof-dependency nodes removed from the item. The unit
   dag/units/sk-thm-curveestimate.json realizes thm-sc-proper-cohomology and has no steps;
   none is removed or bypassed. Verdict: pass after removing two redundant proof imports.
5. Compared the old and delivered DAG records. The item's proof steps and proof_deps
   describe the actual adjunction, generator map and final comparison; proof_origin
   matches the source. The new node matches its theorem and construction and has its
   source, proof, dependency union, searches, status, created, blueprint, chapter, unit
   and Lean fields. Existing statement and statement dependencies are unchanged.
   Verdict: pass.

Removed the new module's unused proof import of
Mathlib.Topology.Sheaves.SheafCondition.Sites and the item's redundant proof import of
WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator; added this review and
the pruning entries.
One original hole is closed and one strictly smaller hole added: net zero holes.
