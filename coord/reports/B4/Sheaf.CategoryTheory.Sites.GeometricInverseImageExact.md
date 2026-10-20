## What changed

Proved `CategoryTheory.GeometricMorphism.geometric_inverse_image_exact` in
`Sheaf.CategoryTheory.Sites.GeometricInverseImageExact`, with its existing signature,
public imports, independent site universes, and both existence and universal clauses
unchanged. No other Lean module is edited.

The proof constructs abelian presentations through internal commutative groups and
constructs the transported ring sectionwise from its internal ring object. It reuses
`Adjunction.transportedRing` and the proved `GeometricConstruction.imageFunctor`,
`imageFunctorUnderlying`, and `sectionGroup` through private proof imports. Ring and
module graph laws follow from the Cartesian lift and terminal comparison equations.
An explicit `ULift.down`/`ULift.up` conjugation produces the universe-explicit interface.
Sectionwise sheaf recognition is checked through an essentially small model, without
imposing an inequality between site universes and the coefficient universe.

For exactness, a private general lemma handles an abelian-valued functor with the
prescribed underlying inverse-image functor, including the composite with source
scalar forgetting. Forgetting abelian sheaves detects finite limits. Epimorphisms are
locally surjective, and the proved singleton case of
`Sheaf.map_jointly_locally_surjective` transports this property along the left adjoint.
Mathlib's kernel/epimorphism criterion gives homology and finite-colimit preservation.
Exactness of module inverse image is then reflected by target scalar forgetting.

The conservative command-change preflight requires the record
`coord/changes/B4-geometric-inverse-image-exact-proof-support.md`. It documents all
new local-instance, section-variable, namespace-open and elaboration commands, the
unchanged public signature, and every downstream consumer. No consumer needs an
adaptation.

Updated the existing node's proof, proof dependencies, proof origin and obsolete
`tool_uses` entry to match this route. The unit's realized route is preserved; its
`realized` statement and step lists are empty, and this node remains the exactness
input used by its parents. No target, public definition, statement or consumer changes.

Validation after the return: the repaired complete module compiled through `lcompile.py`
with no errors or warnings in 16.7 seconds. A temporary `#print axioms` check of the public theorem
reported exactly `propext`, `Classical.choice`, and `Quot.sound`; the probe was removed.
Import-direction checks found no cycle for the three new project proof imports.

The cross-unit tools `lem-weil-pbc-geometric-module-construction`,
`lem-weil-pbc-finite-product-ring-functor`, and
`lem-weil-pbc-inverse-image-local-families` are already fully proved generic tools:
respectively explicit module transport, internal ring transport, and local surjectivity
under a left adjoint. They supply categorical constructions independent of the
trace-formula unit and do not bypass any statement or step of that unit.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.GeometricMorphism.geometric_inverse_image_exact`
(`lem-trf-geometric-inverse-image-exact`). All conjunctions, both presentation existence
assertions, and both universal module exactness assertions are proved.

Holes closed: 1 of 1. Holes added: 0. Holes left: 0. Split-off statements: 0.
All new private definitions and helpers are fully proved; none contains `sorry`.
The theorem's axiom closure contains no `sorryAx`.

## No longer needed

Removed the direct proof import
`WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresObjects` and the corresponding dependency
`lem-weil-pbc-sheaf-algebraic-structures-objects`, including its obsolete top-level
`tool_uses` approval. Its statement fixes the value universe to `max u v w`; instead
this proof directly reconstructs sectionwise algebraic structures and recognizes
sheaves on an essentially small model, preserving the assigned independent universes.
Neither that module nor its equivalence theorem is needed by this proof.

Removed dependencies `lem-weil-pbc-left-adjoint-preserves-colimits` and
`lem-weil-pbc-right-adjoint-preserves-limits` from this node: the proof uses local
surjectivity and the abelian kernel/epimorphism criterion, rather than constructing a
lifted adjunction. The Mathlib leaf
`lem-weil-pbc-adjunction-lifts-abelian-group-objects` is retained because its
`Functor.mapCommGrp` and Cartesian braided structure are used; only its adjunction
clause is unnecessary.

Removed explicit imports `Mathlib.CategoryTheory.Sites.Limits`,
`Mathlib.CategoryTheory.Sites.Abelian`,
`Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`, and
`Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf`. The required sectionwise
limits and abelian-category instances remain available through the retained imports.
Enough injectives and the Grothendieck-category structure are unnecessary. The
`lem-weil-pbc-site-sheaves-enough-injectives` leaf remains as the record for its
abelian-category clause, which is used.

No source-library declaration or module is removed. The entries above describe
this node's dependency pruning; no assertion is made that a shared dependency is
unreachable from all other project targets.

## Where the brief, the DAG or earlier work was wrong

Repair of the return at head `360d38a6e`: compared the retained delivery with the
current module and the B2 algebraic-structure migration record. Reapplied the complete
proof to the current module, preserving its public imports, theorem signature and
original theorem docstring. The current private import is now the upstream
`WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresObjects`; it is unused by
this proof and is removed. No obsolete Sheaf import is restored. The node copy retains
only the delivery-owned route changes; current metadata stays authoritative.

The target statement is unchanged and correct. The original plan's full lifted
adjunction is unnecessary: finite-limit preservation and preservation of locally
surjective maps suffice. The algebraic-structure equivalence named in that plan has
more restrictive value universes than the assigned target; the private sectionwise
reconstruction and small-model sheaf check resolve this without changing its public
interface or any upstream statement. No disputed statement, forced adaptation,
source-library change, or new node is needed.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
