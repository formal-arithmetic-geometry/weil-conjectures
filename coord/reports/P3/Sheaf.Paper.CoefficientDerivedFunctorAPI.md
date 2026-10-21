## What changed

Restored the complete quarantined Sheaf.Paper.CoefficientDerivedFunctorAPI module to
lean/Sheaf/Paper/CoefficientDerivedFunctorAPI.lean. The rework assignment identifies
its missing live source after a cluster restore. All 18 recorded declarations remain,
including the named local Profinite instance, derived pullback and pushforward,
adjunction, composition and square interfaces, and coherent-pullback records.
Both public imports, every definition body, signature and attribute are unchanged
relative to the preserved archive. This restores the missing mathematical API;
it is not an empty stub or a withdrawal of the item.

Reproved coefficientAmbientSquare_app by rewriting coefficientAmbientSquare_eq and
reflexivity of the objectwise components. Reproved coefficientAmbientSquare_hom_app
by the same rewrite and coefficientIsoTransThree_hom_app. These proofs use the
public defining equation instead of unfolding the cached square. Updated only
proof/proof_origin of def-weil-pbc-coefficient-derived-functor-api to match.

The archived module compiled against the current library in 18.0 seconds. The final
module compiled in 17.2 seconds. An independent importing-module compile passed in
2.2 seconds with the archived ambient_square_eq consumer proof and the etale square
consumer described below. The stage-3 declaration differencer confirms empty
interface, statement_changed, added, removed, public_imports_changed and new_sorry
lists relative to the quarantine baseline. No foreign module is adapted.

Change record: coord/changes/P3-coefficient-derived-functor-api-restoration.md.

## Proved and sorry left

This is a zero-hole restoration/definition repair: 0 original holes, 0 holes closed,
0 holes added, 0 split off, and 0 holes left in the delivered Lean source.

The restored proved equations are coefficientDerivedAdjunction_eq,
coefficientIsoTransThree_hom_app, coefficientIsoTransThree_eq,
coefficientAmbientSquare_eq, coefficientAmbientSquare_app and
coefficientAmbientSquare_hom_app, all in namespace
AlgebraicGeometry.ProEtale.CondensedRing. The last two have the revised complete
proofs above; none is counted as a newly closed hole. No sorry-bearing declaration
is introduced. Existing mathematical inputs of the upstream derived-functor
construction are preserved without restating or splitting their obligations.

## No longer needed

None. Both public imports are needed by the restored API: the upstream derived
functors/adjunction/composition, and the finite-discrete realization categories and
functor used in its records. No declaration, module, import, node or dependency is
withdrawn. All parent dependencies remain valid, including quarantined parents;
the unit route in sk-thm-properbasechange is unchanged.

LeanFinder returned the existing underived sheaf-module pullback composition and
adjunction interfaces, which do not replace these concrete derived wrappers. Loogle
for NatIso.trans_app and the launcher grep search returned no new alternative.
The shorter proof uses the already present objectwise definition and its equation.

## Where the brief, the DAG or earlier work was wrong

The live item file was absent, as recorded by coord/rework.tsv; it was restored from
quarantine/Sheaf/Paper/CoefficientDerivedFunctorAPI.lean, not treated as withdrawn.
The preserved archive already compiled against the current library, so no alteration
of its mathematical definitions was necessary. The substantive repair is restoration
of the missing complete module, with its existing Lean attachment preserved.

The consumer check also found that the archived FiniteDiscreteCoefficientSquareCoherence
helper etale_square_eq cites Etale.pullbackSquareComparison_def, which no longer
exists upstream. The upstream pullbackSquareComparison definition is now exposed.
In the temporary consumer check only, replacing that rewrite with
unfold Etale.pullbackSquareComparison makes the helper compile; its companion
ambient_square_eq compiles unchanged against the restored API. This pre-existing
quarantined-consumer repair is not forced by any API change here, and that consumer
and its source dependencies remain reserved for their own restoration assignments.

The first attempt to rewrite both the square equation and NatIso.trans_app exhausted
heartbeats while converting concrete derived functors. Reducing the existing
objectwise constructor after the square-equation rewrite avoids that conversion;
the final file compiles within the unchanged limit and options.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
