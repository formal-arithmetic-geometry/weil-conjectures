## What changed

Reduced `ordinaryScalarComparison` to three dependent intermediate arguments:
`ordinaryScalarRestriction`, `ordinaryScalarAdjunctions`, and
`ordinaryScalarProperOpen`. The main proof assembles all original fields on the same
restriction functor and the same geometric comparisons. The original theorem's
signature is preserved; `ordinaryScalarComparison_unique` is proved by the
section-normalized component isomorphisms.

Moved the original public definitions and `OrdinaryScalarComparison` structure
without changing their bodies into `SemilinearScalarOrdinaryInterface`, publicly
reexported by the original module, to keep imports acyclic. The change record is
`coord/changes/G8-scalar-ordinary-interface.md`. The one direct consumer,
`SemilinearScalarDerivedComparison`, retains its source unchanged; it is checked
against the extracted interface and completed assembly.

Proved `ordinaryScalarRestriction` by constructing `Functor.ofOpSequence` on the
original semilinear transitions followed by the scalar-composition identification.
Its section formulas, additivity and finite limit/colimit preservation are proved
componentwise. The private transition, tower and level-isomorphism definitions have
explicit section and exactness APIs, with local irreducibility preventing repeated
expansion of their large functor terms. The restriction module respects these
transparency boundaries and disables the competing general sheafification instance
locally, using the coefficient-universe instances already supplied by the system API.
The section proof applies its scalar-composition lemma directly. The transition
is constructed componentwise, and its naturality follows from the existing system
transition and the scalar-composition isomorphism.

The projector `scalarOrdinaryPi` is constructed as a composite of natural
transformations, and its defining equation is proved by reflexivity in the assembly.
The geometric record omits redundant unit and counit fields:
proved `OrdinaryScalarAdjunctions.unit` and
`OrdinaryScalarAdjunctions.counit` derive them from the mate equation.

## Proved and sorry left

The current shared baseline has three holes. This delivery closes
`AlgebraicGeometry.ProEtale.VaryingRing.scalarTowerOpen_congr` by substitution,
`AlgebraicGeometry.ProEtale.VaryingRing.ordinaryScalarComparison_unique` by natural
isomorphism and tower extensionality, and
`AlgebraicGeometry.ProEtale.VaryingRing.ordinaryScalarComparison` by the assembly
proof. The existence proof is a decomposition.
The new lower theorem
`AlgebraicGeometry.ProEtale.VaryingRing.ordinaryScalarRestriction` is also proved,
including every section and transition prescription. Two named holes remain (two
added; three current holes closed; net one hole removed).

Validation: the extracted interface compiles. The clean dependency-order check
compiled scalar restriction (52.0 s), adjunction comparisons (8.5 s), proper/open
comparisons (9.5 s), the assigned module (12.4 s), and the unchanged derived
consumer (37.1 s), with no errors or warnings. The final componentwise transition construction also compiled on the project
server in 43.5 s, with no errors or warnings. Original theorem signatures and the
extracted definition/structure block were compared with the current source.

Remaining holes:

- `AlgebraicGeometry.ProEtale.VaryingRing.ordinaryScalarAdjunctions`
  (`lem-sf-semilinear-scalar-adjunctions`): normalized inverse/direct-image and
  open-extension comparisons.
- `AlgebraicGeometry.ProEtale.VaryingRing.ordinaryScalarProperOpen`
  (`lem-sf-semilinear-scalar-proper-open`): intrinsic beta, clopen projector and alpha
  with their compatibility equations.

The existence theorem is a decomposition, not a claim that its entire dependency
closure is sorry-free. The uniqueness, congruence and restriction proofs are complete.
The geometric and proper/open results are genuine lower arguments depending on the
constructed restriction package. The additional
proved declarations are `OrdinaryScalarAdjunctions.unit` and
`OrdinaryScalarAdjunctions.counit`; `scalarOrdinaryPi` is a real natural transformation
with no proof placeholder in its definition.

## No longer needed

No mathematical module is withdrawn. The geometric and proper/open intermediate
arguments still need their original dependency declarations. For exact restriction,
`SemilinearSystemModels` already proves evaluation and scalar-restriction exactness;
the separate sheafification and kernel/cokernel construction steps are unnecessary
for that restriction proof. They are still retained where the geometric comparison
uses them. The parent node now depends on the three intermediate results and the
unchanged interface; its former direct proof dependencies occur at those results.
`Mathlib.CategoryTheory.Functor.OfSequence` is a proof import of both the original
module (for uniqueness) and the restriction module (for the tower construction).

Removed the original direct proof imports
`Sheaf.CategoryTheory.LocalizedModuleExactForSystems`,
`Sheaf.CategoryTheory.RingedSiteModules`,
`WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`, and
`Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`: the main module uses
the intermediate comparisons instead. The original public import
`Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows` moves to the interface module,
which is publicly reexported. No dependency node or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

Return repair: took the current shared module after the batch take-out as the
source, extracted its current interface, and reapplied the proofs to its unchanged
theorem statements and docstrings. The node copy likewise starts from the current
node and changes only the delivery-owned route and Lean attachment fields. This
restores both small proofs that the take-out removed, as well as the existence
assembly. No stale delivered source is used as the baseline. The extracted
interface was compared byte for byte against the current source block, allowing
only the completed congruence proof; the comparison passed.

No statement correction. The original DAG's geometric and coherence steps are
independent substantial arguments; they were not direct applications of a single
existing semilinear-system comparison declaration. The implemented decomposition
retains those arguments without changing coefficient, scheme, or square hypotheses.
The single-sheaf ring-change comparison was checked as an ingredient, but does not
itself give the tower and open coherence package.

Edge cases checked in the statements: empty schemes, zero coefficient rings when
the given maps exist, identity scalar maps, identity scheme maps, and arbitrary
nonflat compatible scalar maps. The constructions retain actual section actions;
no choice of a witness from a mere existence theorem appears in a definition.

## New nodes

`lem-sf-semilinear-scalar-restriction`: the strictly smaller exact levelwise
restriction construction, now proved, with the original transitions and section formulas.

`lem-sf-semilinear-scalar-adjunctions`: normalized geometric/open adjunction
comparisons for a restriction package. Unit and counit preservation are proved from
the mate equation rather than retained as assumptions of this intermediate record.

`lem-sf-semilinear-scalar-proper-open`: the intrinsic proper/open words and their
compatibility for a given restriction and normalized adjunction package. Its proof
contains the compositor and transpose calculations from the original plan.

`def-sf-semilinear-scalar-ordinary-interface`: attachment for the original public
definitions and comparison structure moved verbatim to the interface module.

The unit route and all original statement binders remain unchanged. Change record:
`coord/changes/G8-scalar-ordinary-interface.md`.

## Second reading by G8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
