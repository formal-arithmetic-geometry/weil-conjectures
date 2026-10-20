## What changed

Proved `SheafOfModules.KFlatConeComparison.augmentation_square` completely. The proof uses the
mapping-cone isomorphisms, the acyclic-cone criterion, K-flatness, the derived representative
isomorphism supplied as a hypothesis, and the naturality calculations. The total tensor is
implemented by the direct simultaneous `mapBifunctorMap` formula; `totalBifunctor`,
`uncurry_map_eq`, `totalSingleIso`, and `totalSwap` expose the generic constructions needed by the proof. The
signed transposition is kept folded behind its proved component and naturality lemmas to keep
specialization below the file limit. The unused derived-tensor existence import was removed.

The final implementation compiled cleanly as a full scratch module in 17.6 seconds and
at its canonical module path in 30.7 seconds. An isolated two-module check compiled
the replacement again in 26.5 seconds and confirmed that `augmentation_square`,
`totalSingleIso`, and `totalSwap` use only `propext`, `Classical.choice`, and `Quot.sound`. The final theorem signature is textually
identical to the shared source. The interface changes are recorded in
`coord/changes/B8-kflat-cone-total.md`. No consumer source adaptation is required. The final dry run passed compilation and
server preflight (review class CODEX).
The retained `PurityFiniteKummerLevel` consumer compiled against an earlier equal
implementation in 11.6 seconds. Its final recheck reached a missing published dependency
`Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`, before consumer elaboration;
that consumer source and dependency are also absent from the current shared checkout.
The consumer was used only for validation and is not included in the delivery. The current
`tools/downstream.py` scan reports zero downstream modules; the node still records the
finite-Kummer-level parent that needs this comparison, so this delivery retains its proof.

## Proved and sorry left

Closed: `SheafOfModules.KFlatConeComparison.augmentation_square` (1 original sorry).
Added: none. The delivered module contains zero textual `sorry` declarations.

## No longer needed

Removed `Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent` and
`Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`; the representative
comparison is a theorem hypothesis, so its existence proof is not used. Removed proof dependency and tool-use approval
`lem-weil-pbc-site-derived-tensor-descent` from this node, since its representative comparison
is supplied in the theorem hypotheses. Its statement-dependency reference remains. No other
planned proof dependency or consumer is pruned.

## Where the brief, the DAG or earlier work was wrong

The original uncurry total-map definition caused expensive dependent transports in cone
comparisons. The direct map formula is equal as functors, as proved by
`uncurry_map_eq` and `total_eq_uncurry`; it preserves all public statements. The final implementation also names the unchanged monoidal structure as an irreducible
local instance and uses a generic degree-zero tensor identification. The canonical cone
map is expressed directly by `mappingCone.map`; it has the original two components.
`comparison` and the private cone isomorphisms use irreducibility attributes with proved
APIs. The final change record reflects these attributes and constructions exactly.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
