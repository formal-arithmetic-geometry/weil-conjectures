## What changed

Restored the assigned module from its current quarantine archive, as required by
coord/rework.tsv. Its existing public theorem signature and public import are unchanged.
No source-library file or other existing Lean module is changed.

Proved the reflector conclusion from the existing source-library completion adjunction,
its principal orthogonal criterion, and a new strict-model comparison. The proof constructs
the natural unit by fully faithful transport and proves both output orthogonality and the
Hom bijection. Private, completely proved helpers establish invariance of orthogonality
under an additive equivalence, transport of a reflector, and conversion of natural-number
scalar multiplication. The scalar-conversion lemma is stated on a general site to avoid
specialized instance elaboration mismatches, without altering any shared instance.

The new module Sheaf.Paper.IntegralStrictCompletionComparison constructs the additive
coefficient equivalence, proves that the prime is a nonzerodivisor in the lifted integers,
and defines the canonical integral module completion using the already proved source
construction. Its remaining theorem is a natural comparison of the strict reduction/limit
model with this fixed completion. It does not assume or restate the reflector conclusion.

The original module privately imports the comparison module and Mathlib.Logic.Small.Defs
(with import all to expose the Shrink definitions used by the source adjunction).
The new module publicly imports the existing interface, source completion, derived
coefficient equivalence and sheaf-whiskering APIs required by its definitions and signature.

Compilation: the comparison module compiled in 42.8 seconds; the final assigned module
compiled in 8.4 seconds. No shared interface was changed, so no consumer adaptation is needed.

## Proved and sorry left

Closed the original hole in
AlgebraicGeometry.ProEtale.integral_strict_completion_reflector
(node lem-sfb-integral-strict-completion-reflector), preserving its full signature.
There are zero sorries in the assigned module.

Added one named public sorry:
AlgebraicGeometry.ProEtale.integral_strict_completion_comparison
(node lem-sfb-integral-strict-completion-comparison), in its own new module.
Its docstring gives the strict cokernel/tensor comparison, the common flat-term K-flat
resolution, the universal derived-functor comparisons, and the cofinal exponent shift.
The remaining obligation is specifically identification of the two completion models;
the completion reflector, scalar conversion and equivalence transport are proved.

This is a decomposition: one original hole closed, one lower hole added, net zero.
No definition contains sorry. The new coefficient and completion constructions use proved
source constructions and equivalence data, not arbitrary witnesses from unproved existence.

The two additional source-attachment nodes introduce no Lean declarations and no holes:
DerivedCategory.derivedCompletionAdjunction and
DerivedCategory.derivedComplete_iff_rightOrthogonal already have complete source proofs.

## No longer needed

No original import was removed and no module is withdrawn.

The parent's old direct proof dependencies are replaced as follows:

- lem-cbc-constant-ring-module-sheaves
  (Sheaf.CategoryTheory.ConstantRingModuleSheaves) is unnecessary: the proof uses modules
  over the fixed lifted integers and never changes to a constant ring sheaf.
- lem-sf-principal-strict-limit-reflector
  (Sheaf.SixFunctors.PrincipalStrictLimitReflector) is unnecessary: the proved source
  completion adjunction already supplies the fixed-coefficient reflector.
- lem-pur-native-principal-cone-criterion
  (Sheaf.CategoryTheory.NativePrincipalConeCriterion) is unnecessary: the source
  derivedComplete_iff_rightOrthogonal gives exactly the criterion needed.
- lem-sfb-diagonal-derived-reduction-exists
  (Sheaf.Paper.DiagonalDerivedReductionExists) moves from the parent's direct dependencies
  to the comparison node's proof plan, for the resolving-class computation. It remains
  needed there and is not claimed as globally pruned.

The first three are pruned from this argument, not removed from the library or claimed
unreachable from every target. No upstream declaration or import is deleted.

## Where the brief, the DAG or earlier work was wrong

The module is quarantined, not withdrawn. Its current archive was the source of the repair;
its Lean attachment and original statement are retained.

The original ringed-module route was longer than necessary for the integral-only statement.
The adopted source tree already proves the principal completion adjunction and an exact
orthogonal criterion for fixed coefficients. The old native cone criterion has additional
hypotheses and does not directly state the orthogonal equivalence needed here. Reusing the
source criterion removes that detour without changing the unit's reduction/completion route.

The source completion is defined by its proved distinguished-triangle reflector, rather
than syntactically as the specified total right derived strict inverse limit. Consequently
the strict comparison is genuine mathematical work and is explicitly left as the lower
obligation; no definitional equality or unproved reflector property is asserted in its place.

Edge cases of the comparison: zero inputs give zero on both sides; already complete inputs
are fixed up to natural isomorphism; ell-invertible inputs have zero reductions and zero
completion. No boundedness, product-exactness or input-completeness hypothesis is introduced.
The exponent-zero term of the source tower does not affect its derived inverse limit.

## New nodes

lem-sfb-integral-strict-completion-comparison states the remaining comparison in the new
Sheaf.Paper.IntegralStrictCompletionComparison module, together with the concrete coefficient
and completion definitions it uses. Its proof is the strict quotient/tensor and derived-limit
comparison from Stacks 099M; no universality or orthogonality conclusion is included.

lem-sfb-source-principal-completion-adjunction attaches the already proved source declaration
DerivedCategory.derivedCompletionAdjunction in
WeilConjectures.CategoryTheory.DerivedCategory.Complete.Completion. It adds no Lean file.

lem-sfb-source-principal-completion-orthogonal attaches the already proved source declaration
DerivedCategory.derivedComplete_iff_rightOrthogonal in
WeilConjectures.CategoryTheory.DerivedCategory.Complete.Principal. It adds no Lean file.

The existing reflector node's proof, proof_deps and proof_origin follow the implemented
argument. No other existing node fields or existing modules are changed; no change record
is required.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
