## What changed

Proved `Module.exists_free_away_of_finitePresentation` in
`Sheaf.RingTheory.FinitelyPresentedAlgebraModuleGenericFreeness`, preserving its entire
signature and all existing public imports. Three proved private helpers handle localization
of a base change, passage from a Noetherian model to its image domain, and approximation
when the base and algebra have the same universe. Shrinking the finite-type algebra proves
the full universe-polymorphic statement.

The proof uses the existing `Algebra.limitModuleFinitePresentation` (Stacks 00R1), chooses
one stage, and base-changes that stage to the image of its base ring in R. This gives the
Noetherian domain needed by `Module.noetherian_algebra_module_generic_freeness` (051R).
Localization-tensor equivalences and tensor cancellation transport the resulting basis.
No flatness of the coefficient inclusion is assumed, and no finite-rank assumption is used.
The zero module and zero algebra are allowed; the image base is a domain because R is.

Added proof-only imports for finite-presentation approximation, ring and module shrinking,
localization/base-change compatibility, finite-type base change, and preservation of free
modules under base change. Updated the existing DAG node and its proof docstring to match
this route. Namespace/notation openings are scoped to the private helpers.
No other module, definition or public interface changed.

Validation: the complete proof compiled cleanly through lcompile.py in 4.7 seconds.
The public theorem signature is textually identical to the original; there are zero
sorry tokens, no lines over 100 characters, and proof_deps equals the union of step uses.

Searches: LeanFinder for finite-presentation module descent and generic freeness; Loogle
for `Module.FinitePresentation, IsBaseChange`; launcher grep and local rg for generic
freeness and finite-presentation models. The base-finite generic-freeness results require
finite presentation over R itself and do not apply to this potentially infinite-rank
R-module. Existing algebra/module approximation supplies the shorter route.

## Proved and sorry left

Closed one of one holes: `Module.exists_free_away_of_finitePresentation`
(node `lem-pur-fp-algebra-module-generic-freeness`). Added zero holes and zero split-offs.
Every new private helper is proved. No `sorry` remains in the delivered Lean module.
The proof still depends on the existing named
`Module.noetherian_algebra_module_generic_freeness`; its proof remains the next obligation,
as intended by stage 3. This delivery is a proof from existing declarations, not a decomposition.

## No longer needed

No existing import is removed: both original proof imports are used, and all original
public imports are retained for the statement's interface. No dependency module is pruned.

The hand-written polynomial/coefficient presentation construction in original steps 1–3
is replaced by the already available `Algebra.limitModuleFinitePresentation`. The ordinary
finite-presentation definition remains a statement dependency, but is no longer separately
listed in proof_deps. The ring and module localization definitions, finite-type Noetherian
permanence, scalar-extension universal property and Noetherian generic freeness all remain
used. There are no now-unused stated theorem dependencies.

## Where the brief, the DAG or earlier work was wrong

The original mathematical plan is sound. Its presentation descent can be replaced by the
existing, proved approximation theorem (Tag 00R1), followed by passage to the image of a
stage base ring. A stage base ring need not itself inject into R, so directly applying
Noetherian-domain generic freeness to it would be invalid. The proof explicitly repairs
that gap by base-changing to its image subring; Noetherianity descends through the surjection.

`Algebra.limitModuleFinitePresentation` states the final module equivalence with the
R-action composed through A. Lean requires an explicit additive-equivalence conversion
to the given compatible R-action; this is provided using `IsScalarTower.algebraMap_smul`.
Its equal-universe restriction is handled by shrinking A, not by restricting the theorem.

The new use of `lem-weil-pbc-limit-module-finite-presentation` is a general algebra tool,
not a replacement for any unit statement or step. The item's unit `sk-prop-sf-cbc` has
empty realized statement/steps; no unit route is bypassed. Maintainer-owned `tool_uses`
approvals are unchanged, as required. The DAG now records this dependency in proof_deps.

## Second reading by R7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
