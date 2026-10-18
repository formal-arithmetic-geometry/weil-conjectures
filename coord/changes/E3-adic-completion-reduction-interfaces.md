# Sheaf.Paper.AdicCompletionReduction

## Reason

The target proof is decomposed into three strictly smaller public interface theorems:
the derived scalar Hom equivalence, the restricted Koszul tower isomorphism, and
conservativity of exact scalar restriction. Each interface is a named stage-3 node and
has its own proof plan. The target statements and all existing declaration signatures
are unchanged. A declaration-local linter option suppresses a style warning for the
required local `IsIso` and `ReflectsIsomorphisms` instances.

## Old

The item contained the two target statements with their original proof holes and no
intermediate interface declarations.

## New

The two target statements are proved from the three interfaces. The interfaces retain
all definitions and hypotheses from the proof plan and are documented with their source,
blueprint node, and proof route. No existing consumer requires adaptation.

## Users

No existing module is adapted. The new declarations are used only by
`Sheaf.Paper.AdicCompletionReduction` itself and by the parent proof recorded in its DAG
node.

## Status

landed 20261018T091359-L-3253907 2026-10-18 (merge of deliver/E3/Sheaf.Paper.AdicCompletionReduction)
