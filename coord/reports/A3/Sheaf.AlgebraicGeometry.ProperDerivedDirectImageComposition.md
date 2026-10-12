## What changed

Replaced the sorry in AlgebraicGeometry.exists_properDerivedDirectImageComposition with
an explicit Lean reduction, preserving its complete statement. Properness supplies the
qcqs instances, so schemeDerivedDirectImage_preserves_QCoh supplies preservation directly.
Choose the ambient canonical comparison and its derived-unit characterization from
RingedSpace.exists_derivedModuleDirectImageComposition. Restrict by whiskering with the
full-subcategory inclusion. The original characterization is proved from choose_spec.
Obtain ambient identity comparisons from the new unit-laws theorem, whisker with the
inclusion and compose with its right unitor. The two restricted unit laws follow by simp;
the restricted associativity law is the ambient law evaluated at E.obj.

Added DerivedDirectImageCompositionUnitLaws and
DerivedDirectImageCompositionAssociativity. Each isolates strictly one part of step 2,
without preservation, properness, Noetherian assumptions or existential composition data.
Their hypotheses are the ambient comparison family and its canonical unit equation;
the item constructs these hypotheses from an existing theorem.

Updated the item's node to this actual route. The new nodes record the complete
uniqueness argument, including the necessary naturality and reassociation calculations.
The blueprint unit route is preserved: its realized fields are empty for this auxiliary
node, and no unit-level statement or step is bypassed.

Validation: the original target signature is unchanged; all three delivered modules
compile using lcompile.py, and the item has no sorry. Checked identity morphisms, the zero
object and arbitrary derived-category choices: the new conclusions are universal-property
coherence statements and introduce no geometric or nonzero-object hypotheses. In a direct
associativity experiment, the two inverse transformations were reduced with rightDerived_ext
to equality of their pasted units; the remaining transport/naturality calculations were
not completed within the per-file elaboration budget. This experiment is not delivered.

## Proved and sorry left

Proved (from the named dependencies):
AlgebraicGeometry.exists_properDerivedDirectImageComposition
(lem-pc-proper-derived-direct-image-composition), the item's only original sorry.

The delivery leaves exactly two sorries, each with proof exactly `by sorry`:

- AlgebraicGeometry.derivedDirectImageComposition_unit_laws,
  node lem-pc-derived-direct-image-composition-unit-laws.
- AlgebraicGeometry.derivedDirectImageComposition_associativity,
  node lem-pc-derived-direct-image-composition-associativity.

The imported existing composition and preservation declarations remain their own work
items. They were not modified or proved in this delivery.

## No longer needed

Removed direct proof imports:

- Sheaf.AlgebraicGeometry.DerivedAdjoint:
  lem-pc-ringed-spaces-derived-adjoint is delegated to the existing ambient comparison.
- Sheaf.AlgebraicGeometry.DerivedPullbackComposition:
  lem-pc-ringed-spaces-derived-pullback-composition is likewise below that comparison,
  rather than needed directly by this module.
- Sheaf.AlgebraicGeometry.NoetherianDerivedDirectImageRightAdjoint:
  lem-pc-noetherian-derived-direct-image-right-adjoint is unnecessary here: only its
  preservation clause was needed, and the qcqs preservation theorem supplies that.
  Its Brown-representability, compact-generation and coproduct arguments are unnecessary
  for this proof.
- Sheaf.AlgebraicGeometry.DerivedCategory: its definitions are already available through
  the unchanged public import of SchemeDerivedDirectImage.

def-pc-derived-direct-image and def-pc-derived-category are also removed from direct
proof_deps: their definitions remain statement dependencies and are supplied through
SchemeDerivedDirectImage; they are not separately invoked proof steps.

lem-cat-right-adjoint-composition is no longer a direct dependency of this node: the
ambient comparison encapsulates that construction. These are local pruning decisions,
not claims that the named modules are unreachable from all other targets. All three
original public imports remain because the statement uses their definitions and instances.
The preliminary search of the similarly named DerivedDirectImageComposition module
found an etale bounded-below comparison, not the required unbounded module-sheaf result;
neither that module nor DerivedDirectImageCompositionUnbounded is imported.

## Where the brief, the DAG or earlier work was wrong

The DAG plan is mathematically appropriate, but does not directly expose the Lean glue
between coherent derived pullbacks, their mates, and the right-derived-unit equation.
An existing ringed-space comparison already packages the composition and unit
characterization, so rebuilding it is unnecessary. Its statement does not include the
identity and associativity laws; these are the precise two gaps isolated here.

The local literature directory has no cohomology.tex payload. Verified Stacks Tags 0D5T
and 079V on the official Stacks site. Tag 0D5T states composition by adjunction uniqueness;
the new proof texts explicitly expand the implicit coherence by derived uniqueness,
and their proof_origin is marked as an agent expansion rather than a verbatim source proof.

## New nodes

lem-pc-derived-direct-image-composition-unit-laws, in
lean/Sheaf/AlgebraicGeometry/DerivedDirectImageCompositionUnitLaws.lean, states existence of
ambient identity comparisons and the two unit equations for any canonically characterized
comparison family. It is strictly the unit part of the original coherence clause.

lem-pc-derived-direct-image-composition-associativity, in
lean/Sheaf/AlgebraicGeometry/DerivedDirectImageCompositionAssociativity.lean, states only
the triple-composition equation for a canonically characterized ambient comparison family.
It is strictly the associativity part of the original coherence clause.

Both node files are in dag/nodes/sec-picard-framework/. No definition or statement was
changed. coord/changes/proper-derived-composition-elaboration.md documents the scoped
heartbeat command because the static preflight classifies added commands as interface
changes. A proof-local option did not cover the declaration elaboration.

LeanSearch was also attempted and returned Internal Server Error; its unavailability is
recorded without treating it as evidence of no match. The other three searches succeeded.

## Second reading by A3

1. Compared the delivered item with the repository version. The theorem signature and all
existing declaration statements are byte-for-byte unchanged; only proof imports, a scoped
heartbeat option, and proof text changed. Verdict: pass.

2. Compiled all three delivered Lean modules with lcompile.py --all. The item has no
`sorry`; the only remaining sorries are the two explicitly named split-off theorems, each
with a matching node and proof docstring. No forbidden declarations occur. Explicit #print axioms probes for all three declarations
show exactly propext, Classical.choice, Quot.sound and sorryAx (the named open dependencies).
Verdict: pass.

3. Checked both split-off statements against the existing derived-category and
right-derived APIs, including identity morphisms and zero/arbitrary objects. Each is a
strict coherence component of the original argument and introduces no extra geometric
hypothesis. Searches found no existing declaration duplicating either statement. Verdict:
pass.

4. Read the proof top-down. It uses the existing ambient comparison and QCoh-preservation
theorem first, then the two strictly smaller coherence statements. Removed proof-only
imports are recorded above; no unused public import remains. The unit route is preserved
and no unit-level statement or step is bypassed. Verdict: pass.

5. Compared the item's node proof, proof dependencies, and proof origin with the Lean
proof, and checked both new node records and their lean declarations. The realized unit
route remains unchanged; node dependencies match the actual calls. Verdict: pass.

Changed after this reading: appended this review and completed the pruning report with
def-pc-derived-direct-image and def-pc-derived-category, which are no longer direct proof
dependencies. No Lean statements or proofs required repair.
