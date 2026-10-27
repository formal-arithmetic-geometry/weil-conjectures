## What changed

Restored Sheaf.Paper.IntegralStrictCompletionComparison from the quarantine path recorded
in coord/rework.tsv. Preserved every existing declaration signature, definition body,
instance and public import. The quarantine archive itself is untouched.

Replaced integral_strict_completion_comparison's sorry by a proof from two separate
strict-model invariants, imported privately from the two new modules named below.
The proved private comparison_of_complete_and_triangle lemma supplies the actual glue:
triangle exactness and orthogonality give the strict augmentation's Hom bijections;
the existing completion adjunction factors the augmentation; those bijections prove the
factor invertible in the full subcategory; uniqueness proves naturality. The inverse
natural isomorphism has exactly the original theorem's type.

The two new lemmas assert independently necessary pieces of the argument, rather than
renaming its natural-isomorphism conclusion. Completeness alone is satisfied by the zero
functor. The augmentation-cone condition alone is satisfied by the identity functor with
zero cone. Neither property specifies the completion without the other. All data chosen
from these existential conclusions are confined to proofs; no new definition chooses an
undetermined witness. No source-library module or target statement changes.

Validation: lcompile.py --all compiled all three delivered modules successfully, taking
41.9 s, 47.0 s and 41.3 s respectively, each within the 60 s per-file limit. There were no
warnings in the delivered modules; the private overlay printed existing unused-simp
warnings from the unchanged SfP1ChartExchange dependency. The generic reflection helper
also compiled independently in 4.4 s. A text audit checked that the original theorem
signature and public imports are unchanged and that node signatures and dependency unions
agree with the delivered Lean.

## Proved and sorry left

Closed the original hole in
AlgebraicGeometry.ProEtale.integral_strict_completion_comparison
(node lem-sfb-integral-strict-completion-comparison). The item has zero remaining holes.
The generic private comparison_of_complete_and_triangle is proved without sorry.

Added two holes, so this delivery is a decomposition (one upper hole closed, two lower
holes added, net minus one), not a complete proof of the strict-model mathematics:

- AlgebraicGeometry.ProEtale.integral_strict_limit_complete in
  Sheaf.Paper.IntegralStrictLimitComplete,
  node lem-sfb-integral-strict-limit-complete.
- AlgebraicGeometry.ProEtale.integral_strict_limit_augmentation_triangle in
  Sheaf.Paper.IntegralStrictLimitAugmentationTriangle,
  node lem-sfb-integral-strict-limit-augmentation-triangle.

Both are public theorems whose entire proof is `by sorry`. Each has its source and a
complete natural-language proof in its docstring and corresponding DAG node.

## No longer needed

No module, declaration or public import is withdrawn. No transitive mathematical dependency
is pruned. The diagonal-derived-reduction existence theorem is no longer a direct dependency
of the comparison proof, but remains required by the two strict-model invariants. The
source completion adjunction remains a direct dependency; its orthogonal criterion is
also used directly. The unit's strict simultaneous reduction and inverse-limit route is kept.

## Where the brief, the DAG or earlier work was wrong

The item source was quarantined, rather than withdrawn; the rework row supplies the source
restored here. Its absence from lean/ did not justify deleting its declaration or dependencies.
The stated existence theorem constructs simultaneous reductions, but does not itself identify
their derived inverse limit with the source completion. The source completion adjunction
likewise supplies the reflector, not that strict-model identification. The two new invariant
nodes make those missing parts explicit. The source theorem
DerivedCategory.rightOrthogonal_and_exists_smulInvertible_cone_of_isHomotopyLimit explains
the cone argument once the strict tower and its natural augmentation are identified.

Edge cases: the zero complex and empty scheme give zero derived objects and zero cones;
all statements remain valid. No nonempty-site, boundedness or invertibility-on-the-base
hypothesis was added. The split lemmas allow any additive integer coefficient equivalence,
which respects integer multiplication by additivity and is exact as an equivalence.

## New nodes

lem-sfb-integral-strict-limit-complete records the completeness of the actual strict derived
limit, using the quotient/tensor comparison and principal orthogonality. Its Lean module is
Sheaf.Paper.IntegralStrictLimitComplete.

lem-sfb-integral-strict-limit-augmentation-triangle records a natural strict augmentation
with prime-invertible cone, using normalized quotient projections, Koszul transitions and
the modulo-prime pro-isomorphism argument. Its Lean module is
Sheaf.Paper.IntegralStrictLimitAugmentationTriangle.

The existing comparison node's proof and proof_deps now describe the proved reflection glue.
There are no interface changes to existing declarations and no change record is necessary.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
