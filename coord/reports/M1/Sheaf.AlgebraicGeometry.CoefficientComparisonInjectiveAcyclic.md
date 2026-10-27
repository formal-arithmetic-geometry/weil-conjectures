## What changed

Replaced the proof hole in
`AlgebraicGeometry.ProEtale.coefficientComparison_injectiveAcyclic` without changing its
signature, universes, hypotheses, conclusion, or existing public imports.

The ordinary unit clause is proved for every module, before using injectivity. The proof
reuses `additiveUnitIso` and `ringPresentation`, proved private helpers of
`ConstructibleComparisonModuleExact`, through a private `import all`. It transports the
abelian adjunction through the two AsSmall sheaf equivalences, obtains full faithfulness,
uses the module inverse-image comparison's actual unit equation, and reflects invertibility
through the underlying abelian-sheaf functor. Full faithfulness then proves the unit clause
for the supplied arbitrary adjunction.

For acyclicity, the proof chooses an injective resolution of the pullback. It reduces each
positive direct-image homology to exactness of its degree short complex, forgets modules,
transports the etale site model, and restricts to the affine etale dense subsite. Local
positive derived-evaluation vanishing makes the associated presheaf short complex exact.
Exact sheafification identifies it with the restricted sheaf complex. Faithful exact
restriction reflects exactness back to the module complex.

The local vanishing input is stated in the new module
`Sheaf.AlgebraicGeometry.CoefficientComparisonAffineSections`. It is the affine-restriction
and Cech-computation part of the original argument. It has no unit claim and no conclusion
about a higher-direct-image sheaf. Its coefficient universe is kept independent of the
scheme universe. The two module files and both corresponding DAG nodes form this packet.

Repair validation: `lcompile.py --all` compiled both files successfully (12.2 seconds for
the
affine-sections module, 28.0 seconds for the item), below the 60-second limit. The original
theorem signature and docstring were checked unchanged, and each DAG Lean statement matches
its module verbatim. The returned unit-proof failure was repaired by binding one canonical
module adjunction and passing the reflected `IsIso` instance explicitly to
`isIso_of_reflects_iso`; this removes both the fresh-adjunction typeclass timeout and the
unsolved unit goal.

## Proved and sorry left

Closed the body hole of
`AlgebraicGeometry.ProEtale.coefficientComparison_injectiveAcyclic`
(node `lem-pe-coefficient-comparison-injective-acyclic`). Its unit clause and the full
local-to-global assembly are proved.

Added one named hole:
`AlgebraicGeometry.ProEtale.coefficientComparison_affineSections_vanishing`
(node `lem-pe-coefficient-comparison-affine-sections`). Its proof is exactly `by sorry`,
with the source and complete argument in the docstring and node. This is positive derived
sections over an affine etale object, computed in the intrinsic module category.

Actual holes: item module 0; new module 1; closed 1, added 1, net 0. This is a decomposition,
not a completed proof of the geometric vanishing theorem. There are no new definitions,
no holes in definitions, and no changed existing statements.

## No longer needed

No existing public import was removed, and no existing module was withdrawn.

The item's former direct proof dependencies `det-pe-classical-sheaves-modules` and
`lem-pe-comparison-injective-left-modules-acyclic` are replaced by the actual unit and
local-evaluation argument. Their fixed-coefficient declarations do not directly instantiate
at the item's arbitrary coefficient universe and intrinsic constant-ring presentation.
This removes those direct planned edges; it does not claim that their modules are globally
unreachable. Existing upstream declarations and all existing dependencies of other modules
are preserved. The new local lemma retains the affine Cech route of the source.

## Where the brief, the DAG or earlier work was wrong

The two planned declarations are fixed-scalar sheaf statements whose Lean coefficient
Hom universe is tied to the scheme universe's successor. The assigned item instead uses
constant-ring modules on AsSmall models and permits a strictly larger independent
coefficient universe. Thus the planned 'transport' is not a one-line application of either
recorded declaration. No mathematical statement has been weakened to bridge this gap.
The existing exactness module already supplies the independent-universe abelian unit
calculation and the constant-ring presentation, so those are reused rather than restated.

The new affine vanishing statement was checked on the empty scheme, the zero ring and
zero module, positive degrees including degree one, and arbitrary discrete coefficients.
The proof uses no claim that forgetting an injective module gives an injective abelian
sheaf: it uses the derived-evaluation comparison and section acyclicity instead.

## New nodes

`lem-pe-coefficient-comparison-affine-sections`, in
`dag/nodes/sec-proetale-coefficients/lem-pe-coefficient-comparison-affine-sections.json`,
is the local affine-derived-evaluation step of Stacks 099U/099V. The original item node is
updated to record the proved unit transport and local-to-global assembly. The source read
was `literature/stacks-project/proetale.tex`, lemma-affine-vanishing and the first paragraph
of lemma-relative-comparison, and the current blueprint's injective-acyclicity proof.
The whole-blueprint search found the broader reduction node
`det-pe-injective-acyclicity-reduction`, which has no Lean attachment; its local vanishing
part is what this new coefficient-sized statement isolates. Mathlib searches used
LeanSearch, LeanFinder, Loogle, and source grep; none supplied the local theorem.

There are no change records because no existing statement or definition changes, no new
definition nodes, and no forced adaptations of modules held by other groups.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
