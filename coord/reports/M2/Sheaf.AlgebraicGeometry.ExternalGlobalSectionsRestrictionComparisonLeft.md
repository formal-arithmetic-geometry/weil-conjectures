## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_externalSectionsRestrictionComparisonLeft`
from an explicit presheaf morphism constructed using the field-linear pullback units,
restriction of the second-factor global section, and the sectionwise tensor coefficient.
The new module `Sheaf.AlgebraicGeometry.ExternalSectionsUnitMapLeft` supplies that construction,
its proved naturality and top-open normalization, and a separate local pure-tensor transport
statement. The original module imports it privately. Every existing signature and definition
is unchanged. The DAG records the construction followed by tensor extensionality.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.exists_externalSectionsRestrictionComparisonLeft` (one of one).
The item itself has no remaining sorry. Added one hole in
`AlgebraicGeometry.Scheme.Modules.exists_externalSectionsUnitOpenTransportLeft`, node
`lem-sc-external-sections-unit-open-transport-left`. This is a decomposition, not a net
reduction in holes: the natural transformation, its naturality, its top normalization,
and extension from pure tensors are proved; the remaining hole concerns the coefficient
and section isomorphisms for a single open subscheme and their action on pure tensors.

The helper `scalarSectionUnit_apply`, `externalSectionsUnitAppLeft_naturality`, and
`externalSectionsUnitLeft_top` are proved. Every new definition has explicit data.
The pullback coefficient is chosen from its existing characterization, which determines
all unit components on all opens, hence determines the coefficient by adjunction.

## No longer needed

No imports or modules are pruned. The original public import is required by the
unchanged signatures; the new private import is required only by the proof.
The following old proof dependencies are no longer direct dependencies of the item,
but remain required by the new local transport node:
`lem-weil-pbc-open-immersion-module-pullback-restriction`,
`def-weil-pbc-composite-adjunction`,
`lem-weil-pbc-conjugate-iso-unit-equation`, and
`lem-weil-pbc-module-pullback-tensor`.
The two scalar-operation dependencies remain used by the explicit construction.
Thus all six original planned dependencies remain in the argument. No blueprint
unit or step is bypassed; the unit record is unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The scalar pullback coefficient API already
provides a field-linear section unit as a natural transformation, so constructing
linearity again is unnecessary. The second-factor analogue remains sorry and does
not supply a proved shortcut. LeanFinder, Loogle and Mathlib grep found generic
restriction/unit/tensor tools rather than an assembled external-section transport.
LeanSearch returned HTTP 500, recorded as unavailable. The repository lacks the
Stacks source file, so Tag 0BED was read at its official web page; its degree-zero
canonical-cup verification is explicitly omitted and the transport proof is given
in full in the new theorem docstring.

## New nodes

`lem-sc-external-sections-unit-open-transport-left` records transport on pure tensors
for one open V, using the cartesian open immersion, restriction section identification,
uniqueness of left adjoints with its unit equation, composition comparisons, and the
pure-tensor pullback comparison. It carries no existence of a natural transformation
and no top-open normalization. Its module is
`lean/Sheaf/AlgebraicGeometry/ExternalSectionsUnitMapLeft.lean`.
Empty opens, empty X or Y, and zero coefficients require no extra assumption:
restriction and the adjunction comparisons remain isomorphisms and the unit equations
remain valid. No bijectivity or sheaf gluing is assumed.

## Second reading by M2

1. Compared both delivered modules with the repository. The item's only changes
   are a private proof import and the body of
   `exists_externalSectionsRestrictionComparisonLeft`. Its entire signature is
   byte-for-byte unchanged; `externalSectionsPushforwardLeft` and
   `externalSectionsTopIsoLeft`, including their bodies, are unchanged. The helper
   module is new. No existing definition, visibility, hypothesis or conclusion
   changes, and no change record is required. Verdict: pass.

2. Read every definition and proof. The first component is the pullback unit;
   the second is the global unit followed by restriction; their tensor followed
   by `scalarTensorCoefficientApp` gives the component. Naturality uses unit
   naturality and `tmulSection_map`. The top proof identifies both sections with
   `tensorPullbackTopSection`. Tensor extensionality then proves the parent from
   the local transport clause. There is exactly one `sorry`, the named public
   theorem `exists_externalSectionsUnitOpenTransportLeft`; none occurs in a
   definition, and there are no forbidden declarations or attributes.
   `exists_scalarPullbackCoefficient` prescribes every section of the adjoint
   natural transformation, so the adjunction bijection determines the chosen
   coefficient, rather than providing an arbitrary witness. Compilation and
   axiom results are recorded below.

3. Read the new transport statement against its docstring and node, and read
   [Stacks Tag 0BED](https://stacks.math.columbia.edu/tag/0BED), the pullback
   adjunction of [Tag 0096](https://stacks.math.columbia.edu/tag/0096), and tensor
   pullback in [Tag 01CD](https://stacks.math.columbia.edu/tag/01CD). This is the
   degree-zero canonical-map verification, not the Kunneth isomorphism assertion:
   it requires no quasi-coherence or finiteness. The remaining theorem fixes one
   open and the explicit component, and compares it on pure tensors. It omits
   the original existence of a natural transformation, naturality and top
   normalization; those have real proofs. Thus it is strictly a part of the
   argument, not a restatement. The isomorphisms are obtained by the cartesian
   open-immersion square, restriction sections, the normalized left-adjoint
   comparison, composition comparisons, and `module_pullback_tensor` with its
   unit-section formula. Tested the empty open (both section targets are zero),
   empty factors (the product is empty), zero coefficients (the comparison
   equation is zero), and the top open (the already proved normalization).
   These cases need no extra assumption. Independently searched LeanFinder for
   global sections and open pullback units, Loogle for `restrictAppIso`, and
   Mathlib grep for unit/restriction relations; also read the second-factor
   `ExternalSectionsComponents`, `ExternalSectionsOpenComparison`, the upstream
   `Modules/PullbackUnit`, and searched the library for external section and
   restriction tensor tools. None gives an assembled proved first-factor
   transport. The second-factor open comparison is itself still `sorry`.
   No split-off theorem could be closed in a few minutes. Verdict: pass.

4. The explicit section construction takes the direct unit-and-tensor route;
   its naturality and top normalization use no new hole. Both imports of the
   item are needed with the stated public/private visibility; the helper's
   public import is needed by its signatures and definitions. The four old
   comparison dependencies have moved to the local transport node, as now
   listed individually under `No longer needed`; none is pruned from the
   argument. Read `dag/units/sk-prop-av-cube.json`, including its embedded blueprint
   statement and proof step (the referenced literature file is absent here):
   the unit route and its `realized` record are unchanged. This remains a
   decomposition (one hole closed, one added), with zero net hole reduction.
   Verdict: pass.

5. Checked both node records against the Lean text. Each recorded theorem
   statement matches verbatim. The parent proof records the explicit unit
   construction and tensor extensionality; the new node records precisely the
   remaining local coefficient and section transport. Its `proof_deps` is the
   union of its step's `uses`, with the restriction, composite-adjunction,
   conjugate-unit and tensor comparisons retained. Source, searches, status,
   creation, blueprint ancestry, chapter, unit and Lean records are present.
   Existing-node edits are confined to stage-3-owned fields. Verdict: pass.

Second reading changed the report's dependency-transfer explanation and added
three independently executed searches to the new node. No Lean proof or
signature was changed.

Validation: `lcompile.py --all` compiled both delivered modules with no errors
or warnings. A scratch module printing the axioms of all eight new declarations
and the parent theorem also compiled. All new definitions and the three proved
helper theorems use only `propext`, `Classical.choice`, and `Quot.sound`; the
transport theorem and the parent additionally use `sorryAx`, exactly as expected
from the one reported open transport hole. Point 2 verdict: pass as a decomposition.
