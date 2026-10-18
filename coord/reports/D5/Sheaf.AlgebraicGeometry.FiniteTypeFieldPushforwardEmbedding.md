## What changed

Proved `AlgebraicGeometry.Etale.exists_mono_finite_pushforward_of_finiteType_field`
in the assigned module by specializing the existing
`AlgebraicGeometry.Etale.exists_mono_biproduct_lowerStar_of_isNoetherian`.
Local finite type over the field gives local Noetherianity; quasi-compactness
of the structure map gives compactness, hence Noetherianity of X. The existing
constructibility comparison provides precisely the required concrete ModuleCat
instance. Mathlib `Module.finite_of_finite` converts each finitely generated
module over the finite ring `ULift (ZMod N)` to a finite underlying set.
The original finite maps, modules, map and Mono proof are retained unchanged.

Added proof-only imports of Mathlib.RingTheory.Finiteness.Cardinality and
WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison.
The existing public imports and theorem signature are unchanged. Updated only
the item's proof, proof_deps, proof_origin and obsolete tool_uses in its DAG node.
No definitions, statements, consumers or other Lean modules changed.

Validation: the required lcompile.py single-file compile succeeded with no
warnings or errors (7.9 seconds). Import-direction checks and a DAG traversal
confirm that neither of the two reused theorem dependencies reaches this item.
The unit record sk-prop-sf-cbc has empty realized.statement and realized.steps;
this specialization preserves its higher-level route and the statement of the item.
N=1, the empty scheme, zero sheaf and empty finite family need no exclusions:
the reused theorem and the finite-module conversion apply in all these cases.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.exists_mono_finite_pushforward_of_finiteType_field`
(node lem-fin-finite-type-pushforward-embedding).
No sorry remains in the item. No holes or split-offs were added.
This is a proof from existing library declarations; no claim is made that all
transitive dependencies of those declarations are already sorry-free.

## No longer needed

Removed these proof-only imports from the item:

- `WeilConjectures.ConstructibleSheaf.Pullback`
- `Sheaf.AlgebraicGeometry.ConstructibleFieldFiniteSeparableConstant`
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`
- `Mathlib.AlgebraicGeometry.Properties`
- `WeilConjectures.AlgebraicGeometry.WeilPbcNormalizationInResidueFieldExtension`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`
- `Sheaf.AlgebraicGeometry.NormalGenericConstant`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModuleAdjunction`
- `WeilConjectures.ConstructibleSheaf.Defs`
- `WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm`
- `WeilConjectures.SixFunctors.Finite.Stalk`
- `Sheaf.AlgebraicGeometry.ConstructibleFiniteSelection`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction`
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`
- `Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme`

These are removed as direct imports of this module; some remain transitive
imports of the general theorem. No global module withdrawal is claimed.
The original public FinitePushforward import is used by the specialization and
provides the biproduct instance used in the existing signature.

The old direct proof dependencies no longer needed here are:

- `lem-weil-pbc-locally-noetherian-quasi-separated`
- `prop-constructible-pullback`
- `lem-weil-pbc-constructible-field-finite-separable-constant`
- `lem-weil-pbc-reduced-induced-closed-subscheme`
- `def-pc-integral-scheme`
- `lem-weil-pbc-normalization-in-residue-field-extension`
- `lem-fin-normalization-extension-finite`
- `def-weil-finite-integral-morphism`
- `lem-fin-normal-generic-constant`
- `lem-weil-pbc-inverse-image-composition-module-linear`
- `lem-weil-pbc-inverse-image-module-adjunction`
- `lemma-constructible-pullback-constant`
- `def-weil-pbc-inverse-image`
- `lem-weil-pbc-inverse-image-stalk-germ`
- `lem-weil-pbc-finite-stalk-formula-restriction`
- `def-weil-pbc-etale-constructible-sheaf`
- `lem-weil-pbc-constructible-noetherian-finite-selection`

The direct residue-field trivialization, normalization, module-adjunction,
stalk and finite-selection construction is subsumed by the existing, more general
Noetherian embedding. All eight old tool_uses entries were withdrawn, in their
original order: `prop-constructible-pullback`, `lem-weil-pbc-constructible-field-finite-separable-constant`, `lem-weil-pbc-reduced-induced-closed-subscheme`, `lem-weil-pbc-normalization-in-residue-field-extension`, `lem-weil-pbc-inverse-image-composition-module-linear`, `lem-weil-pbc-inverse-image-module-adjunction`, `lem-weil-pbc-inverse-image-stalk-germ`, `lem-weil-pbc-finite-stalk-formula-restriction`.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or statement repair was necessary. The original planned
construction was redundant because the general Noetherian module embedding is
already available in a public import of this file. The added constructibility
comparison is the already proved upstream declaration recorded in the comparison
node's lean_audit.slopmaster2 entry; that node's older primary lean record still
names the retired Sheaf wrapper.

The two existing nodes reused as tools of this specialization are
lem-weil-pbc-constructible-finite-pushforward-noetherian and
lem-weil-pbc-constructible-etale-module-sheaf-comparison (unit sk-thm-p1).
They give the general embedding and the predicate equivalence respectively;
the current unit has no existing declaration providing these generic interfaces.
No new tool_uses approval has been inserted by the worker.

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
