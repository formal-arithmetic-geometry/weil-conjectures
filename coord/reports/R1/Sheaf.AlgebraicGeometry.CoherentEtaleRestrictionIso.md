## What changed

Proved `AlgebraicGeometry.Scheme.Modules.existsUnique_coherentEtaleRestrictionIso`
without changing its statement or the definition `coherentEtaleRestrictionIso`.
The proof constructs the natural isomorphism from the global-section components of
`tensorSectionsComp`, applies the additive ULift functor, lifts to sheaves, and
composes with `upperStarIsoLocalizationRestriction`. The prescribed component
formula and uniqueness follow by cancellation and extensionality.

Added one private proof import, `Mathlib.CategoryTheory.Adjunction.CompositionIso`.
Private helpers prove the adjunction-composition coherence, its section-unit
naturality consequence, and the resulting restriction square. They specialize the
same Mathlib argument already used privately in the upstream tensor-section
presheaf module; no public declaration is copied or added. Removed the unused
public import
`Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`; the other public imports,
signatures and definitions remain unchanged. The item node now records this proof.
The main module compiled in 22.9 seconds
after pruning the unused import. The consumer check also compiled the item (28.5 seconds), unchanged
`CoherentHigherImageClasses` (20.3 seconds), and unchanged
`AffineCohomologyEtaleModuleRealization` (17.1 seconds) in dependency order against
the delivered module, with no errors or warnings.

The landed declarations used are `tensorSectionsComp`, `tensorSectionsUnit`,
`etaleTensorSectionsRestriction`, `etaleTensorSectionsSheaf`,
`exists_tensorPullbackAdjunction`, `liftedCoherentEtaleSheaf`, and
`Etale.upperStarIsoLocalizationRestriction`, together with Mathlib's
`Adjunction.leftAdjointCompIso_assoc` and sheaf/presheaf isomorphism constructors.
This delivery contains no copy of a landed public theorem and no statement or
definition correction.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.Scheme.Modules.existsUnique_coherentEtaleRestrictionIso`
(node `def-weil-pbc-coherent-etale-restriction`). Added zero holes and split off zero
statements. No `sorry` remains in the delivered module. Its private helpers are
all proved. The selected isomorphism's definition remains unchanged.

## No longer needed

Removed `public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
the statement and proof instead use the already available upstream pinned tensor
adjunction and `tensorSectionsComp`. That imported module is not needed by this
proof. Its node `def-pc-module-pullback` remains needed for the tensor construction
and is not withdrawn. No existing node, declaration, module, or unit-route step
is withdrawn. The change record is
`coord/changes/coherent-etale-restriction-unused-adjunction-import.md`.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The item node had an empty proof because
it was recorded as a definition, while the Lean module postpones its unique
normalized existence theorem. Its original docstring gives the correct argument,
now formalized and recorded in the node. The construction works equally for empty
schemes and zero modules: it uses only functorial isomorphisms and extensionality,
with no nonemptiness assumptions.

Delivery tool capacity: the first submission returned exit 75, stating that all
24 delivery slots were busy; no packet check failed and nothing was pushed.
The same completed packet is retried as instructed by the tool.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
