## What changed

The assigned theorem keeps exactly its existing signature. Its complete Lean proof
obtains coherent object comparisons, applies separate finite-stage and cocone Hom
interfaces to those same objects, and packages the resulting equations through a
constructor interface for the original explicit predicate.

The new coherent-object module gives real named tilde, localized tilde, scalar
reassociation and base-arrow constructions. It stores comparisons under Nonempty;
no definition chooses arbitrary data from unproved existence. It also proves the
generic categorical naturality cancellation, scalarExtensionHom reassociation,
and their combined natural-isomorphism form, affineModel_scalarConjugation_nat.
The concrete specializations and the conversion to the original predicate are
separate named obligations, with complete natural-language proofs and nodes.
All added imports in the assigned module are proof-only. No existing public
signature, target, or unheld module is changed.

## Proved and sorry left

Closed: AlgebraicGeometry.affineModelComparisonData_of_bottom_models.

The generic affineModel_scalarConjugation_nat is proved, together with its private
categorical cancellation and scalar-reassociation helpers. No hole occurs inside
a definition or an anonymous/private declaration.

Added and left, each exactly := by sorry:

- AlgebraicGeometry.exists_affineModelCoherentObjectComparisons,
  node lem-pc-affine-model-coherent-object-comparisons.
- AlgebraicGeometry.affineModelStageHomEquation_of_coherent_objects,
  node lem-pc-affine-model-stage-hom-equation-of-coherent-objects.
- AlgebraicGeometry.affineModelLimitHomEquation_of_coherent_objects,
  node lem-pc-affine-model-limit-hom-equation-of-coherent-objects.
- AlgebraicGeometry.affineModelComparisonData_of_hom_equations,
  node lem-pc-affine-model-comparison-data-from-hom-equations.

This is a decomposition: one original hole closed, four lower holes added,
net minus three holes. It is not an axiom-free proof of the original theorem.
The geometric obligation constructs object comparisons and iso-level triangles,
not arbitrary-map equations. Each Hom obligation is only one of the two kinds
of arrows. The constructor obligation assumes both Hom equations and only
introduces the witnesses into the existing predicate. None repeats the assigned
theorem's K-flat, coordinate-transition and bottom-model hypotheses and conclusion.

## No longer needed

No existing library module is claimed globally pruned. No original statement
import is removed. The earlier attempt's AffineModelFiniteDiagramPropagation
module and node are not delivered or imported. WithTerminal, adjoined-terminal
diagrams and terminalFamily are unnecessary: finite and cocone arrows are direct.
Unused proof imports AffineDerivedPullbackTensorTilde and KFlatModuleBaseChange
are removed from the new coherent-object module; their declarations remain in
the geometric node's intended proof plan for its next worker.

## Where the brief, the DAG or earlier work was wrong

The earlier timeout was not a tool failure. Controlled partial-proof checks,
timing markers and fully explicit expression comparisons locate expensive
conversion of categorical maps and object types, including generated preorder
and HasPullback proof constants in affineModelComparisonData versus direct
instances. The generic cancellation compiles; its concrete specializations and
the predicate constructor remain representation glue. A duplicate large formula
and a more elaborate square structure were tested and removed. No compiler
wall-clock limit was increased, no kernel check was bypassed, and no unsafe
reducibility option or diagnostic code remains in the delivered files.

The reduction covers identity arrows, zero rings and empty spectra, zero and
coincident models, and chain maps which do not descend to the bottom. No
hypothesis of directedness, colimit, flatness or boundedness is introduced.
The unit's realized route is unchanged.

## New nodes

lem-pc-affine-model-coherent-object-comparisons records the geometric construction
and four iso-level triangles. Its real definitions and proved generic scalar
conjugation API are listed in its Lean record.

lem-pc-affine-model-stage-hom-equation-of-coherent-objects records specialization
of that generic calculation to finite-stage arrows.

lem-pc-affine-model-limit-hom-equation-of-coherent-objects records specialization
to arrows from a finite stage to the cocone point.

lem-pc-affine-model-comparison-data-from-hom-equations records the constructor
interface for the original explicit predicate, given both Hom-equation families.
All four lie in dag/nodes/sec-picard-framework and retain the item's unit.
No change record or forced adaptation is required.

## Second reading by P4

1. I compared the delivered item module with the repository version. The
   theorem signature is unchanged byte for byte; only proof-only imports and
   the proof body changed. The added modules are new declarations and do not
   alter an existing interface.
2. I compiled all five sandbox modules with `lcompile.py --all`. Compilation
   succeeds with no errors. The only remaining `sorry`s are the four named
   split-off theorems listed above; no definition contains `sorry`, and no
   forbidden axiom, unsafe declaration, or implementation escape appears.
3. I checked each split-off statement and its node. The coherent-comparison
   existence statement, the two separate Hom equations, and the constructor
   interface are true, strictly smaller obligations, have source and proof
   descriptions, and are not duplicates of existing library declarations.
4. The proof follows the shortest available route below the unit: coherent
   comparisons, finite and limit Hom interfaces, then the constructor. The
   item retains the unit route and its revised proof dependencies; no
   unnecessary public proof import was introduced.
5. Node proof steps, dependencies, origins, and Lean declaration records match
   the delivered code. The unit's `realized` route is unchanged.

I changed only this second-reading report section after the first dry run,
recording the checks above. No Lean source or node content required repair.
