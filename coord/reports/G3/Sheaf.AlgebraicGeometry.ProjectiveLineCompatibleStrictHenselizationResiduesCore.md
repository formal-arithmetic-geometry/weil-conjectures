## What changed

Repair of reviewer X-1f91b, points D1/D2 and C1/D3. The lifting theorem
AlgebraicGeometry.Etale.exists_compatibleStrictHenselizationResidueLift now takes
r and hres as inputs and returns only φ, the ring reduction equality and structural
square, exactly as requested. Its docstring and node state the narrowed obligation.

The item independently constructs r before invoking the lifting theorem. A new
residue-image containment lemma supplies only pointwise membership in the image
of κB → k′. The item chooses the unique preimage of each element, proves all ring
laws by injectivity, and proves the spectral square using full faithfulness of Spec.
It then invokes the narrowed lifting theorem, proves locality, and identifies the
induced residue map using residue surjectivity. No data are chosen from arbitrary
existence: each field preimage is unique because the field embedding is injective.

The lifting node now cites the existing etale-local-ring triples identification,
strict-henselization triples colimit, and ind-etale henselian lifting nodes. Their
recorded modules are imported as proof dependencies. The last of these is the
existing Tag 08HR theorem from which 04GU follows; no duplicate general 04GU node
is added. Every proof_deps list is the union of its steps' uses. The residue-image
node cites the identification and residue-colimit statements independently of lifting.

The earlier corrected existence interface and its forced caller adaptation remain.
Neither the core theorem nor any target statement or definition changes.

## Proved and sorry left

Closed upper hole: AlgebraicGeometry.Etale.compatibleStrictHenselization_residue_square
has a complete proof of its corrected existence statement. The old universal claim
was false; this is a statement repair and decomposition, not a proof of that claim.
The already proved projectiveLine_compatibleStrictHenselizationResidues_core is
unchanged. The caller projectiveLine_compatibleStrictHenselizationResidues remains
proved with exactly its existing signature.

Two new named holes, each strictly a part of the argument:

- AlgebraicGeometry.Etale.compatibleStrictHenselization_residue_image
  (lem-weil-pbc-compatible-strict-henselization-residue-image): field-image containment
  only; no ring lift, structural equality, locality, or residue-field map is asserted.
- AlgebraicGeometry.Etale.exists_compatibleStrictHenselizationResidueLift
  (lem-weil-pbc-compatible-strict-henselization-residue-lift): lift an already supplied
  compatible residue embedding; it does not construct that embedding.

No sorry remains in the item or adapted caller. This is a decomposition with two
lower holes, not a net reduction of the hole count. Existing model-existence and
other lower obligations are unchanged. All delivered modules compile via lcompile.py.

## No longer needed

No existing module is claimed globally pruned and no public import is removed.
The returned CoreData override and strengthened core statements stay excluded;
the library's existing CoreData is unchanged and remains needed. The range lemma
uses only the triples identification and colimit modules, with no functoriality or
ring-lifting dependency. No generic 04GU lifting module is added, because the existing
Sheaf.RingTheory.MapIntoHenselianColimit supplies precisely that lifting property.
The former helper's hidden residue-embedding step is now explicit in the item's
proof and proof dependencies. No unit-realized node is bypassed.

## Where the brief, the DAG or earlier work was wrong

D1/D2: the previous helper and wrapper were equivalent: taking the induced residue
map of a local φ recovered the helper's entire conclusion. Merely deriving locality
and identifying the residue map was not a reduction. The helper now requires r and
hres, while the item constructs them from a separate field-containment obligation.

C1/D3: the previous helper had three non-elementary steps with empty uses lists.
Tags alone were not DAG dependencies. The repair uses
lem-weil-pbc-etale-local-ring-triples for the neighbourhood-diagram identification,
lem-weil-pbc-strict-henselization-triples for the local ind-etale colimit and residue
identification, and lem-weil-pbc-map-into-henselian-colimit for the prescribed-residue
lift. Their Lean signatures were read, not merely their proofs. No citation to a
canonical-map theorem is used to lift an arbitrary specified residue embedding.

Sources read: Stacks https://stacks.math.columbia.edu/tag/04HX,
https://stacks.math.columbia.edu/tag/04GU and https://stacks.math.columbia.edu/tag/08HR.
04GU explicitly derives its specified-residue lift from 08HR. LeanFinder, Loogle
and Mathlib/library grep found field injectivity and separable-closure APIs but no
exact model residue-image containment statement. The new node records these searches; LeanSearch returned an internal-server error
and is recorded as unavailable. The previous second reading and its .check marker
belonged to the returned version and are superseded by this substantive repair.
The marker is archived in scratchpad; a second reader must review this revision.

Edge checks: for fields the residue projections are identities and containment
reduces to separable-closure inclusion. Base residue automorphisms change the lift
but do not change the image of a separable closure. Inseparable geometric extensions
need not be integral in these fixed-model lemmas: only separable algebraic elements
are used, and the splitting argument puts them in the second residue image.
Empty schemes cannot admit the input field-valued points. The strict-henselization
ring data and all definitions remain actual constructions. Unit sk-thm-p1 is unchanged.

## New nodes

lem-weil-pbc-compatible-strict-henselization-residue-lift:
Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationResidueLift, narrowed to lift
an input r and hres. Its dependencies are the existing diagram identification,
local/residue colimit theorem, and general ind-etale henselian lifting theorem.

lem-weil-pbc-compatible-strict-henselization-residue-image:
Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationResidueImage, pointwise
containment of the two residue-field images in k′. It constructs no map A → B.
The item builds r with its ring laws and hres from this statement before lifting.

Change record: coord/changes/compatible-strict-henselization-residue-construction.md.

## Forced adaptations

Sheaf.AlgebraicGeometry.ProjectiveLineCompatibleStrictHenselizationResidues (unclaimed):
only its block after the existing core-data obtain changes. The original application
passes ι and φ where the corrected existence interface expects σ and τ and lacks
the factorization hypotheses. The adapted block installs the six ring/local/residue
instances, obtains a compatible map, and repacks the structural and residue squares.
Every existing signature, visibility and import remains identical. The delivery
script compiles the original against the overlay and records its compiler errors.

## Second reading by G3

1. I compared each delivered module with the repository version. The core theorem's
original declarations and the caller's public signature are unchanged; the only
existing statement change is the explicitly recorded residue-square repair. The two
residue helper modules are new declarations with matching DAG nodes.
2. I compiled all four delivered modules with `lcompile.py --all`. There are no
axioms, unsafe declarations, hollow definitions, or unnamed `sorry`s. The two
remaining `sorry`s occur only in the named split-off helper theorems and match their
nodes and docstrings.
3. I checked both new statements against the fixed-model edge cases in this report.
The image lemma asserts only pointwise field-image containment; the lifting lemma
assumes the residue embedding and returns the ring lift. Neither restates the item.
4. I traced the proof dependencies in both new nodes and the item. The realized unit
route through the local-ring triples, strict-henselization colimit, and henselian
lifting declarations is retained; no unit step is bypassed and no unused public
import was removed.
5. The DAG `proof`, `proof_deps`, and `proof_origin` fields agree with the Lean calls,
and the change record lists the changed statement and forced caller adaptation.

I found no further defect. The only changes made in this second reading were this
review section and the accompanying report wording; the Lean proofs and declarations
already compiled cleanly.

## Forced adaptations

### Sheaf.AlgebraicGeometry.ProjectiveLineCompatibleStrictHenselizationResidues
Original against changed dependencies failed:
```
/tmp/forced-adaptation-h0271x65/lean/Sheaf/AlgebraicGeometry/ProjectiveLineCompatibleStrictHenselizationResidues.lean:97:66: error: Application type mismatch: The argument
  φ
has type
  A →+* B
but is expected to have type
  Spec (CommRingCat.of ?m.478) ⟶ T
in the application
  compatibleStrictHenselization_residue_square ?m.494 φ
/tmp/forced-adaptation-h0271x65/lean/Sheaf/AlgebraicGeometry/ProjectiveLineCompatibleStrictHenselizationResidues.lean:97:64: error: Application type mismatch: The argument
  ι
has type
  Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k)
but is expected to have type
  Spec (CommRingCat.of ?m.477) ⟶ S
in the application
  compatibleStrictHenselization_residue_square ι

(with the modules compiled into /tmp/forced-adaptation-h0271x65/.lbuild) [3.6 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
