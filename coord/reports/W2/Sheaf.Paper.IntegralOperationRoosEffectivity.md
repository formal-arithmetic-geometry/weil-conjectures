## What changed

The proof of `WeilConjectures.integralOperationRoos_effectivity` now uses the
simultaneous coefficient-sequence reduction model, ordinary tensor adjunctions,
projection-preserving strict Roos comparisons and normalized DVR effectivity.
The tower comparison uses component maps with literal endpoints. Its evaluation
square is proved directly on underlying sections from the existing characterizations
of sequence restriction and quotient transitions. Naturality and the quotient unit
equation assemble the finite isomorphisms into the strict tower isomorphism.
The theorem statement and its three public constructions keep their signatures
and the three construction bodies. No source-library module is edited.
Four unclaimed dependencies share definitionally identical interfaces:
`IntegralReductionTowerUnrestricted` uses the scalar-reduction witness and functor;
`NormalizedDVRTower` uses the scalar-reduction category and retains its original
restriction construction as a reducible ordinary definition.
`DerivedScalarExtensionRestrictionAdjunction` retains its original category and
restriction bodies as reducible ordinary definitions. Both restriction interfaces
have explicit proved additivity instances. No object or map wrappers are introduced.
The four derived category, evaluation and restriction interfaces in
`CoefficientRingedSequenceSite`, the normalized DVR derived categories, legacy
restrictions and tower evaluations, and `unrestrictedIntegralFiniteComplex` retain
their exact bodies as reducible ordinary definitions. A proved private helper
matches the named transition functors before inspecting their constructions.
The transition proof checks transparency while instantiating this helper.
The integral source category and complex functor retain their original bodies,
including generated proof constants and literal finite-complex endpoints.
Change records are `coord/changes/W2-integral-roos-shared-reduction.md`,
`coord/changes/W2-normalized-module-category-alias.md`,
`coord/changes/W2-regular-scalar-restriction.md` and
`coord/changes/W2-regular-derived-sequence-interfaces.md`.
Five interface identity checks compile: the completed-module category, reduction
witness, ordinary functor, restricted complex functor and normalized module category
are equal to their previous presentations by `rfl` (19.3 seconds).
All five modules pass the normal compile check in dependency order, without
warnings or errors (result `a0f9fe0160f65967b9283a5c`). A redundant composite-iso
equality is replaced by direct definitional reduction.
Two private definitions cache the existing chosen ordinary and derived adjunctions
with their small adjunction types. Their bodies are exactly the original choices.
The public proof reduces the derived alias at its final boundary, so its stated
projection adjoints remain those of the original chosen adjunction. Three further
private definitions name the canonical finite, evaluation and sequence derived
comparison isomorphisms with their named functor endpoints. The repeated internal
effectivity assertion is a private predicate; the public statement is verbatim.

## Proved and sorry left

The assembled proof has zero `sorry` occurrences. It replaces the one original
hole in `WeilConjectures.integralOperationRoos_effectivity`
(node `lem-pur-integral-operation-roos-effectivity`). No holes are split off or added.
No `sorry` remains in any of the five changed modules. Every added helper and
instance is proved; there is no split-off theorem or new mathematical node.

## No longer needed

The proof uses the simultaneous reduction model instead of constructing K-flat
finite pullback and tensor normalization from scratch. It removes the direct proof
imports of `KFlatRingedToposPullback`, `ModulePullbackTensorIso`, and `ChangeOfRingsKFlat`.
It removes the unused direct `CoefficientExtensionRestrictedTower` proof import
while explicitly retaining direct proof imports of `IntegralReductionTowerUnrestricted`
`NormalizedDVRTower` and `CoefficientRingedSequenceSite`, whose interfaces the proof uses.
It also replaces the private `strictRoosTriangle` argument and its direct imports of
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products` and
`WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts` by the existing
projection-preserving constant-tower Roos comparison.

Accordingly the item does not directly need nodes
`lem-pur-kflat-change-of-rings`,
`lem-weil-pbc-ringed-pullback-preserves-kflat`,
`lem-weil-pbc-ringed-topoi-module-pullback-tensor`,
`prop-weil-pbc-proetale-constant-exact`, or
`lem-weil-derived-limit-products-core`. These modules remain available to their
other consumers and to the comparison lemmas that still import them. The normalized
DVR tower and reduction-tower interfaces remain transitively needed. No module is
withdrawn, and the unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The original plan constructed a normalized finite-operation tower directly. The
existing simultaneous reduction model and ambient operation tower isomorphisms
supply that construction with fewer independent tensor calculations. Fullness of
restriction along the locally surjective completion projection identifies the
ordinary quotient transition by its value on the tensor unit.

The legacy finite-field datum is unnecessary for the unrestricted operation towers;
a prime different from l is chosen only to instantiate the existing legacy effectivity
interface. The duplicate ordinary scalar-extension witnesses are definitionally equal. Sharing
their interface avoids expansion of sheafification and tensor instances during checking.

The quotient formula is proved for arbitrary indices before specializing to a
successor. Quotient functors and successor arrows carry explicit upper indices,
avoiding conversion between large chosen adjunctions indexed by `Nat.succ n` and
`n + 1`. The direct sectionwise square and the complete lower tower argument compile
with no holes (31.0 seconds). The ordinary
tower first uses the existing `unrestrictedTowerComplex` and
`unrestrictedTowerTransition` interface, so the tensor-unit equation has its literal
scalar-extension/restriction endpoints. A separate functor-presentation comparison
then identifies it with the operation tower.

The integral tower category keeps its original body and generated proof constants.
The scalar categories and ordinary and derived restriction and evaluation
functors keep their original bodies as reducible ordinary definitions to avoid
eager expansion of concrete coefficient actions. The adjunction module protects its
large witness while extracting the same derived specification, with transparency
checking enabled. The four change records request the required definition-sensitive
review for reached targets. No consumer source adaptations are needed.

The packet explicitly imports its adapted proof dependencies. The compiler helper
orders sandbox files by direct imports, so relying on transitive imports had attempted
the main module before compiling the adapted interfaces. The retained imports state
the actual proof dependencies and ensure their compiled versions are used.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
