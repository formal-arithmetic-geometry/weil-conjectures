## What changed

Repaired reviewer X-86e5d, head 86e5dfb20, review point 4 together as one set.

AffineSpectrumCanonicalStalkComplexIso adds the explicit constructions
`isoPullbackModuleStalkComplexIso` and `canonicalSpectrumStalkComplexIso`.
The first composes the extension/restriction unit with the inverse canonical
pullback-stalk comparison and lifts it to complexes. The second transports the
source point and specializes to X.isoSpec.inv. The pullback-stalk comparison is
pinned by its germ formula; no arbitrary chain-isomorphism existence witness is chosen.
Both definitions have complete bodies and no sorry.

AffineSpectrumCanonicalTensorGeneratorFormulaOfQ replaces arbitrary-q quantification
with a typed let-binding to canonicalSpectrumStalkComplexIso. Its generator equation
is proved using scalar compatibility and the coefficient-one equation. The former
is proved in AffineSpectrumCanonicalTensorComparisonScalar using the existing inverse
restriction-stalk scalar theorem and linearity of the remaining three factors.
The coefficient-one germ calculation is a named obligation in its own new module.
This is a decomposition with a real scalar-extension argument, not a renaming of the
whole formula: the remaining theorem has no arbitrary coefficient d and does not
assert semilinearity on arbitrary vectors.

The existential caller AffineSpectrumCanonicalTensorGeneratorFormula now chooses the
same constructed q. Only its proof and now-unused proof import change. Its signature,
visibility, hypotheses, and conclusion are identical. The corrected node statement,
Lean signature, proof docstring, and metadata all describe the constructed map.
The parent node proof metadata is updated to the new choice. The unit route is kept.

Change record: coord/changes/canonicalSpectrum_tensor_generator_formula_of_q.md.

## Proved and sorry left

Holes closed: 1 (the repaired
`AlgebraicGeometry.SingleComplexBaseChange.canonicalSpectrum_tensor_generator_formula_of_q`,
node lem-pc-affine-spectrum-canonical-tensor-generator-formula-of-q).
Holes added: 1. This is a decomposition, with zero net change in the number of holes
before pruning; it is not a claim to have proved the original false statement.

The sole sorry in the delivered files is
`AlgebraicGeometry.SingleComplexBaseChange.canonicalSpectrum_tensor_comparison_one`
(node lem-pc-affine-spectrum-canonical-tensor-comparison-one), in
AffineSpectrumCanonicalTensorComparisonOne.lean. It is exactly `:= by sorry`, with
source and a complete section-germ/adjunction-unit proof in its docstring and node.
It is strictly the coefficient-one part of the generator argument.

The explicit chain coordinate definitions have no holes. Also proved without a new
sorry are `canonicalSpectrum_tensor_comparison_smul` and its private helper
`isoPullbackAdditiveStalkIso_smul`. The caller
`exists_canonicalSpectrum_tensor_generator_formula` retains a complete proof.
The old private counterexample helper is removed: it diagnosed the rejected universal
statement and is not part of the repaired proof.

Edge cases: the zero complex, zero modules, and zero stalk rings obey the same
unit and scalar equations; there is no z0 for an empty spectrum. For the identity
square over Spec(Q), only the specified q occurs. The counterexample using its
negative no longer applies. No flatness, nonzero, or boundedness hypothesis is added.

## No longer needed

Removed the proof-only import
Sheaf.AlgebraicGeometry.AffineSpectrumCanonicalTensorGeneratorFormulaQ from its sole
caller. Thus that module and node
lem-pc-affine-spectrum-canonical-tensor-generator-formula-q are no longer needed by
this route: an uncharacterized existence witness is replaced by an actual construction.
The parent node proof_deps drops the existence-only node. No other source module
imports it (checked with rg over lean/).

For completeness, the parent also drops the old direct proof dependencies
`def-pc-single-complex-base-change-stalk-condition`,
`def-pc-tensor-pullback-composition-iso`,
`lem-pc-affine-spectrum-canonical-stalk-ring-coordinates`, and
`lem-pc-iso-pullback-stalk-cohomology`: its proof now only constructs q and applies
the constructed-q formula. These four remain needed transitively by the new
construction/comparison modules and in the displayed signatures; their modules
are not pruned. Likewise, the OfQ node's old direct ring-coordinate dependency
is now used through the two comparison nodes and remains a statement dependency.
Only the existence-only FormulaQ module is claimed as pruned by this route.

Removed Mathlib.LinearAlgebra.TensorProduct.Associator and the diagnostic private
integer-tensor helper from the returned sandbox version. Neither contributes to the
corrected formula. The original statement-level imports remain needed; all newly
imported proof modules contribute to the compiled proof.

## Where the brief, the DAG or earlier work was wrong

The rejected universal statement confused canonical coordinates with arbitrary
isomorphisms. On the identity square over Spec(Q), q and -q give opposite nonzero
values on the same tensor generator. The former dispute-only delivery retained that
false universal statement and did not repair its caller. Both issues are now repaired.

The new theorem states only the formula for the explicit extension/restriction-unit
and germ-characterized pullback-stalk construction. It is not merely an existential
restatement of the parent. The parent retains exactly its original existential type.
The source Tags 0098, 0096, and 0DJ8 were read online; their canonical stalk and
adjunction maps motivate the explicit construction and germ calculation.

The blueprint ancestor utility reports None for this node's created.item chain,
which uses module names; the new nodes record that fact in blueprint.from.place.
Searching the imported blueprint for tensor generators found no duplicate.

## New nodes

`def-pc-affine-spectrum-canonical-stalk-complex-iso` records the explicit unit,
inverse pullback-stalk comparison, lifting to complexes, and point transport. Its
module contains two actual definitions and no sorry.

`lem-pc-affine-spectrum-canonical-tensor-comparison-scalar` records semilinearity of
the fixed comparison on all vectors. It is proved using
lem-pc-restrict-stalk-inv-smul and module-linearity of the remaining factors.

`lem-pc-affine-spectrum-canonical-tensor-comparison-one` is the sole new sorry:
the coefficient-one section-germ/composite-adjunction-unit calculation for the
constructed coordinates. Its docstring and node give the full mathematical proof.
All three inherit the item's chapter and unit and record the actual Mathlib searches.
The LeanSearch service returned Internal Server Error, recorded as unavailable;
Loogle, LeanFinder, and source grep were available.

Change record: coord/changes/canonicalSpectrum_tensor_generator_formula_of_q.md.

## Forced adaptations

Sheaf.AlgebraicGeometry.AffineSpectrumCanonicalTensorGeneratorFormula is unclaimed.
The original was compiled against the corrected OfQ module and failed at line 143:

```text
error: Application type mismatch: The argument q has type
stalkComplex ... ≅ ((ModuleCat.restrictScalars ...).mapHomologicalComplex ...).obj ...
but is expected to have type ℤ in the application
canonicalSpectrum_tensor_generator_formula_of_q f f' g g' sq sq0 z0 P q
```

The corrected formula's first ordinary argument after P is now k, because q is
let-bound in its conclusion. Consequently the original arbitrary witness cannot be
passed. Original lines 139–143 are replaced by the isoSpec point equality, the explicit
canonicalSpectrumStalkComplexIso witness, and application of the formula without q.
The now-unused existence-only proof import on line 6 is removed. No signature,
visibility, statement docstring, or unrelated proof line is changed.


## Second reading by N4

1. Compared all five delivered Lean modules with the repository. Three are new.
The existing existential caller has byte-identical declaration signature and
visibility; its only changes are the forced witness/application and removal of
the unused proof import. OfQ intentionally corrects the false arbitrary-q
statement, with the full old/new signature and sole caller in
coord/changes/canonicalSpectrum_tensor_generator_formula_of_q.md and a matching
statement_change record. No target or existing definition is changed. Verdict: pass
as a recorded intermediate-statement repair, not a proof of the old false statement.

2. Compiled the five modules in import order using lcompile.py --all: all pass
without warnings (5.9, 22.5, 11.7, 24.3, and 12.2 seconds). Source inspection finds
exactly the reported named coefficient-one sorry and no forbidden declarations,
no sorry in data, and no extra proof holes. Checked the chosen comparison against
Modules/TensorPullbackStalk.lean: its formula specifies every section germ;
linearity and scalar-extension generators determine its inverse, hence its map.
The construction does not choose an arbitrary complex-isomorphism witness.
Explicit #print axioms gives only propext, Classical.choice and Quot.sound for
both new definitions and the scalar theorem; the coefficient-one theorem and
OfQ additionally use sorryAx. The delivery's exhaustive probe checks every
delivered declaration, including the caller. The sole scratch warning was a
long #print command, absent from delivered files.
Verdict: pass with upstream/remaining sorryAx recorded, not axiom-free completion.

3. Read the coefficient-one theorem, its node and complete germ/adjunction proof,
and checked the directions of alpha and the two stalk comparisons. The mate of
pushforward composition identifies successive units; the restriction comparison
is the left-adjoint uniqueness map, which preserves those units. On the zero
complex/modules and the identity square this gives the asserted equation; an
empty spectrum has no z0. Scalar compatibility is proved on arbitrary vectors
and supplies the actual general-coefficient reduction. Independently searched
LeanFinder for successive-pullback unit germs, Loogle for conjugateIsoEquiv,
and grep for leftAdjointUniq unit and comp_unit_app, as well as lean/ for stalk
comparisons. These supply component lemmas, not the remaining composite formula.
AffineSpectrumStalkCoordinateData has a private Nonempty construction of the
same kind; its existential conclusion does not specify the required q and is
not a replacement for an explicit definition. ModulePinnedTensorStalkSquare
concerns a monoidal tensorator; the open-restriction generator lemmas concern
different pinned restriction comparisons. No direct duplicate was found.
Read Stacks Tags 0098, 0096, and 0DJ8 online. Verdict: the new hole is true, needed,
and strictly the coefficient-one portion; closing it requires a further formal
germ/mate calculation rather than a short direct application.

4. The main proof uses the shortest scalar extension argument once the
coefficient-one comparison is supplied. All public imports support signatures
or construction data; the scalar, coefficient-one, inverse-scalar and fully
faithful proof imports are ordinary imports. Checked the old proof_deps of both
existing nodes. Expanded No longer needed to distinguish removed direct edges
from the one actually pruned module. The unit sk-thm-picard-semicon has empty
realized statement/step lists; none is bypassed or edited, and its semicontinuity
route is preserved. Verdict: pass; one module pruned by this route.

5. Read all five node records against the declarations, construction bodies and
proof steps. Their proof_deps equal the unions of step uses; the existing parent
now names the explicit construction and OfQ application. New nodes have source,
full signatures, searches, provenance, chapter/unit, and blueprint references.
The OfQ lean signature includes exactly the recorded constructed-q let-binding.
Verdict: pass.

Second reading changed only this report: completed the direct-dependency pruning
account and added the independent review. No Lean proof, statement, definition,
import, or DAG record needed further repair. This delivery remains a recorded
statement repair plus a decomposition (one repaired upper hole closed, one
strictly smaller hole added), not a net proof claim.

## Forced adaptations

### Sheaf.AlgebraicGeometry.AffineSpectrumCanonicalTensorGeneratorFormula
Original against changed dependencies failed:
```
/tmp/forced-adaptation-62zt6uf6/lean/Sheaf/AlgebraicGeometry/AffineSpectrumCanonicalTensorGeneratorFormula.lean:143:78: error: Application type mismatch: The argument
  q
has type
  stalkComplex g' (X'.isoSpec.inv z0) P ≅
    ((ModuleCat.restrictScalars
              (canonicalSpectrumStalkEquiv X (g' (X'.isoSpec.inv z0)) ((Spec.map (Scheme.Hom.appTop g')) z0)
                  ⋯).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
      (stalkComplex (Spec.map (Scheme.Hom.appTop g')) z0
        (((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
of sort `Type u` but is expected to have type
  ℤ
of sort `Type` in the application
  canonicalSpectrum_tensor_generator_formula_of_q f f' g g' sq sq0 z0 P q

(with the modules compiled into /tmp/forced-adaptation-62zt6uf6/.lbuild) [14.0 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
