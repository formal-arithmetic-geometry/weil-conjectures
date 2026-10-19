## What changed

Proved the ordinary restriction properties, both ordinary and derived mate naturality lemmas, both derived restriction
right-adjoint theorems, and the uniquely normalized ordinary restriction composition.

The ordinary and sheaf derived adjunctions first use existing common-universe theorems.
Canonical localization equivalences transport them to the independently selected source and
target localization sizes. Localization full faithfulness identifies the transported right
adjoints with the existing exact derived restriction definitions. All existing signatures, definitions, visibility and docstrings are unchanged.

Added the proof-only import Sheaf.RingTheory.DerivedModuleScalarAdjunction and recorded its
node lem-weil-pbc-derived-module-scalar-adjunction in the existing item's proof dependencies.
No new modules, declarations, nodes or change records.

## Proved and sorry left

Closed six of the original ten holes, with no holes added and no decomposition:

- CategoryTheory.ConstantScalarRealization.restriction_properties
- CategoryTheory.ConstantScalarRealization.moduleComparison_naturality
- CategoryTheory.ConstantScalarRealization.derivedRestriction_isRightAdjoint
- CategoryTheory.ConstantScalarRealization.moduleDerivedRestriction_isRightAdjoint
- CategoryTheory.ConstantScalarRealization.comparison_naturality
- CategoryTheory.ConstantScalarRealization.restrictionComposition_existsUnique

The four remaining original holes all have node
lem-sfb-constant-realization-derived-scalar-extension:

- CategoryTheory.ConstantScalarRealization.restrictionIso_existsUnique: construct the unique
  restriction comparison on constant generators using module sheafification.
- CategoryTheory.ConstantScalarRealization.moduleComparison_tensor: sheafified tensor comparison
  with its formula on constant generators.
- CategoryTheory.ConstantScalarRealization.constantRealizationDerivedScalarExtension: K-flat
  preservation, invertibility, representative comparison and scalar-unit compatibility.
- CategoryTheory.ConstantScalarRealization.constantRealizationDerivedScalarExtension_transitivity:
  tower compatibility of the normalized comparisons.

Validation: retained work was checked against the current source and dependency signatures.
The whole delivered module passed remote lcompile.py again (9.7 seconds, 2026-10-19).
The delivery preflight also compiles the axiom probe.
The proofs deliberately use existing named dependencies that remain unproved, as stage 3 requires.

## No longer needed

None. The remaining tensor and derived comparison holes retain the original DAG plan and its
proof-dependency imports. No unit statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The retained earlier attempt did not compile: its naturality rewrites did not account for
identity-functor maps and reassociation, and infer_instance could not supply an independent-size
module derived restriction adjunction. The existing module scalar-adjunction theorem uses one
localization universe; transporting through Localization.uniq preserves the original two-size
signature. No mathematical statement was changed.

The retained report overstated the seventh completed proof: restrictionIso_existsUnique
passed elaboration but its kernel check timed out. It remains an original named hole.
Profiling found expensive reduction through module sheafification and its adjunction;
private construction helpers did not yet bring the proof within the limit. No partial
proof or new hole is delivered for it.

## Second reading by Z9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
