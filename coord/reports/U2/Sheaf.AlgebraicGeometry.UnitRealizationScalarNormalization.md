## What changed

Replaced the proof of
`AlgebraicGeometry.Scheme.Modules.exists_unitRealizationScalar_of_coherentAction`.
The witness is the fixed higher-image functor applied to the inverse of an explicit
unit coefficient isomorphism, composed with the supplied realization. Its class formula
reduces the desired equation to the existing hypotheses `ha` and `hl`.

Added six modules recording the actual argument:
`UnitStructureCoefficientIso`, `SheafHDerivedNaturality`,
`UnitLocalizedScalarConjugation`, `UnitScalarRawData`,
`UnitCoherentRawEvaluationFormula`, and `UnitScalarRawEvaluation`, all in
`Sheaf.AlgebraicGeometry`. The coefficient isomorphism uses the actual adjoint
structure-module maps on top sections. The local scalar proof evaluates the normalized
coherent restriction, uses linearity of tensor composition and the structure maps,
and cancels the localization and coefficient isomorphisms. The raw evaluation proof uses
coefficient naturality of `rawRestrictedClassNormalization` and bijectivity and naturality
of `sheafHToDerived`. The existing theorem imports only the final raw-evaluation module
privately. No existing signature, definition, public import or attribute changes.

The change record is `coord/changes/unit-realization-scalar-proof-api.md`.

## Proved and sorry left

Replaced the one original hole by a complete assembly proof from the lower steps:
`AlgebraicGeometry.Scheme.Modules.exists_unitRealizationScalar_of_coherentAction`
(node `new-unit-realization-scalar-normalization`). The remaining raw-evaluation compatibility is isolated below; the packet is a
decomposition, not a net hole closure.

The new public proof declarations (pending the complete packet compile) are:

- `AlgebraicGeometry.Scheme.Modules.tensorPullback_map_smulHom`;
- `AlgebraicGeometry.Scheme.Modules.coherentEtaleMap_app`;
- `AlgebraicGeometry.Scheme.Modules.coherentEtaleMap_smulHom_app`;
- `AlgebraicGeometry.Scheme.Modules.unitStructureCoefficientIso_hom_app`;
- `AlgebraicGeometry.Etale.sheafHToDerived_map`;
- `AlgebraicGeometry.Scheme.Modules.unitLocalizedCoefficientIso_scalar`;
- `AlgebraicGeometry.Scheme.Modules.unitCoherentRawClass_class`;
- `AlgebraicGeometry.Scheme.Modules.unitCoherentRawClass_scalar`.

The raw-evaluation compatibility theorem
`AlgebraicGeometry.Scheme.Modules.unitCoherentRawClass_evaluation` remains `sorry`.
It concerns only the actual coefficient isomorphism and the fixed cohomology evaluation;
it does not repeat the realization theorem or assume its higher-image action.
All other new lemmas have complete proofs. The delivery tool checks compilation and axioms.

## No longer needed

No existing import or module is withdrawn. The direct invocation of
`lem-kun-commutative-exchange-chart`, `lem-pbc-canonical-additive-cohomology-square`, and
`lem-sbc-abelian-higher-direct-image-class-compatibility` in the old plan is unnecessary:
only coefficient naturality is needed, and `rawRestrictedClassNormalization` supplies
that square for the specified class construction. The associated modules are not newly
imported as proof dependencies of the item. They may remain needed elsewhere.

The old tensor-unit, coherent-restriction and Ext-evaluation dependencies are still used
through the new proof modules. They are not pruned. The item node now records the actual
two-step assembly, with these lower steps recorded on the four new nodes. No unit route
or source-library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The old proof plan's exchange-chart and additive
comparison detour is more general than this coefficient-only problem requires.

A concrete-category version of the Ext-naturality proof exceeded the file time limit.
The final argument formulates its natural-comparison calculation over an abstract
abelian category and keeps the evaluation construction locally irreducible. It changes
no shared definition or time limit. The raw-evaluation calculation uses the composite
functor map_comp law explicitly to avoid expanding the derived localization construction
during kernel checking. Local scalar conjugation and raw evaluation are
separate mathematical steps, not files split to evade a compile limit.

The mathematical edge cases checked are degree zero for Ext naturality, empty schemes
and charts, zero coefficient groups, and scalars zero and one. The formulas use only
isomorphism cancellation and module linearity and impose no nonemptiness or invertibility
of the scalar.

## New nodes

`new-unit-structure-coefficient-iso` records the explicit unit coefficient isomorphism
and its section and scalar API; it uses the existing adjoint structure-module isomorphism
and tensor-unit restriction equation.

`new-sheaf-h-derived-naturality` records naturality of the fixed Ext evaluation under
coefficient maps; the proof uses Ext postcomposition and the natural shift and single
comparisons.

`new-unit-localized-scalar-conjugation` records a statement about coefficient sheaves
alone, with no cohomology or higher-image realization. Its proof uses the exact section
normalization of coherent restriction and module linearity.

`new-unit-scalar-raw-evaluation` records the transfer of raw scalar equations to coherent
Ext equations and the canonical class formula. The proof combines the preceding steps
with the already proved raw class normalization theorem. The item node is updated to
refer to these actual proof steps. All four nodes carry complete Lean statements and
proofs, source references and the searches run in this session.

`new-unit-scalar-raw-data` records the explicit postcomposition construction of
transported raw classes, with no arbitrary chosen data.

`new-unit-coherent-raw-evaluation-formula` is the single remaining proof obligation:
compatibility of the fixed raw/Ext evaluation with this explicit coefficient map.
It has no realization, no higher-image action and no scalar hypothesis. Its formula
is needed by the proved scalar assembly and is strictly a cohomological step of the
original argument. The one upper hole closed and one lower hole added give net zero;
the delivery is a decomposition with proved structural and scalar steps.

The latest compile did not start Lean: exit 125, stdbuf could not create its
temporary directory because the device had no space left. The complete packet
has not passed compilation or delivery preflight; no successful delivery is claimed.

## Second reading by U2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
