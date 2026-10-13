# Sheaf.Algebra.Homology.LocalizedTensorComparisonClosureCoproduct

## Reason

The stage-3 preflight classifies the delivery as CODEX because the module's proof-only
imports and scoped commands are visible to static analysis. The interfaces and theorem
signatures are unchanged; the proof requires the direct-sum-square declaration supplied
in the new module.

## Old

The existing theorem declarations had the same signatures, with proof holes.

## New

The same declarations and signatures, with complete proofs except for the explicitly
split direct-sum-square theorem in its own module.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.LocalizedTensorComparisonClosureCoproduct | C1 | proof imports and proof body updated |
| Sheaf.Algebra.Homology.LocalizedTensorComparisonDirectSumSquare | C1 | new required intermediate declaration |

## Status

landed 20261013T190135-L-3214267 2026-10-13 (merge of deliver/C1/Sheaf.Algebra.Homology.LocalizedTensorComparisonClosureCoproduct)
