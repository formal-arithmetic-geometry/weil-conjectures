## What changed

Replaced the sole sorry in Sheaf.AlgebraicGeometry.FlatClosedFibreInterior with a
compiling reduction following Stacks Tag 054X, second proof paragraph. The original
signature, public imports and docstring are unchanged. Added proof-only imports of
ClosedFibreInteriorComponent, FlatFibreComponentDimensionSpecialization,
NowhereDenseClosedFibreDimension, and Mathlib's UniversallyOpen module.

The main proof selects an ambient fibre component generic point using
Mathlib genericPoints.closure, lifts its underlying point through the closed immersion,
and identifies its fibre point using fiberι's embedding. The common-component
comparison is fully proved. Flat.generalizingMap for the restricted closed family
then gives a generalization over eta. Both local dimensions specialize to the common
special-fibre dimension. Their resulting equality contradicts the strict dimension
drop in the generic fibre.

ClosedFibreInteriorComponent contains proved private topology helpers: local dimension
cannot increase under an embedding; it is equal at a point in the interior of the
range; and a point mapping to a component generic point under a closed embedding is
itself component generic. Its public theorem is proved by constructing the map of
ordinary fibres, checking the pullback square, and applying these helpers. No data
are chosen from an unproved existence theorem.

The two remaining theorems are strictly separate parts of the argument. The flat
specialization theorem does not involve any closed immersion, integral base, generic
point of the base, or nowhere-density hypothesis. The strict dimension theorem does
not involve flatness, finite presentation, an open base restriction, or specialization.
They cannot individually imply the original theorem.

## Proved and sorry left

Closed the original hole:
AlgebraicGeometry.interior_fibre_closed_eq_empty_of_flat_restrict
(node lem-sbc-flat-closed-fibre-interior).

Also proved the new theorem:
AlgebraicGeometry.common_fibre_component_dimension_of_mem_interior
(node lem-sbc-closed-fibre-interior-component), with all three private helpers proved.

Two new holes remain, each the entire proof of a named public theorem in its own module:

- AlgebraicGeometry.fibre_dimension_eq_of_specializes_component_restrict
  (lem-sbc-flat-fibre-component-dimension-specialization).
- AlgebraicGeometry.fibre_dimension_lt_of_closed_interior_eq_empty
  (lem-sbc-nowhere-dense-closed-fibre-dimension).

The item's module has no sorry. This is a decomposition: one original hole closed,
two lower holes added, net minus one before further workers close them. It is not
claimed to be an axiom-free completion of the original theorem. All four modules
compile with the required lcompile.py wrapper.

## No longer needed

None of the original imports or DAG dependencies were removed; the original node
had no proof_deps and no proof-dependency imports. No existing node or module is
pruned by this delivery. Exploratory imports of Flat and FinitePresentation in the
new ClosedFibreInteriorComponent and NowhereDenseClosedFibreDimension modules, and
ClosedImmersion in FlatFibreComponentDimensionSpecialization, were removed as unused.

The new strict-dimension node points its planned worker to the existing affine
component formula lem-weil-pbc-dimension-at-point-components rather than duplicating it.
That formula alone does not provide the strict inequality for a closed fibre. It is
not imported by our completed proof since the remaining strict-dimension theorem is
still the next item.

## Where the brief, the DAG or earlier work was wrong

The original node had a single non-elementary step with uses=[] and proof_deps=[].
Its dimension arguments therefore had no stated declarations to import. This
delivery exposes them as two independent source-backed statements, and proves the
component and open-neighbourhood topology rather than leaving it as another hole.

The Stacks sources were checked online: 054X, 054U, 054T, 00OT and 00OS. The repository
literature checkout on this machine contains citation lists but not the source tex.
LeanFinder found Flat.generalizingMap and sober-space generic-point APIs, not the
dimension assertions; LeanSearch returned Internal Server Error and is recorded as
unavailable. Loogle did not know the upstream local-dimension definition. Repository
search found the affine component formula and the shared local-dimension definition.
Blueprint searches for fibre dimension, local dimension and generic point found no
existing blueprint statement duplicating any new lemma. The original item's stored
blueprint.from points to sbc-lem-slicing; we retained this ancestry on the new nodes.
The unit has empty realized arrays, so no recorded unit step was bypassed.

Edge cases: empty special fibres are handled without selecting a point (selection is
only under nonempty interior); an empty closed generic fibre supplies no z over eta;
zero-dimensional ambient fibres cannot contain a nonempty nowhere dense closed fibre;
identity closed immersions satisfy the comparison theorem but cannot satisfy the
strict-dimension premise in a nonempty fibre. Nonreduced source and closed subfamily
are allowed because all comparisons use the underlying topology. U may be the whole
base, and the dimension specialization theorem does not require an integral base.

## New nodes

lem-sbc-closed-fibre-interior-component is a fully proved topology comparison for a
closed fibre immersion at a component point in its interior. Module:
Sheaf.AlgebraicGeometry.ClosedFibreInteriorComponent.

lem-sbc-flat-fibre-component-dimension-specialization states the restricted form of
Stacks 054U, with fibre transport made explicit. Module:
Sheaf.AlgebraicGeometry.FlatFibreComponentDimensionSpecialization. This is one of the
two new holes.

lem-sbc-nowhere-dense-closed-fibre-dimension isolates the final strict dimension drop
of Stacks 054X, supported by the finite-type field component formula 00OT and domain
dimension theorem 00OS. Module: Sheaf.AlgebraicGeometry.NowhereDenseClosedFibreDimension.
This is the second new hole. No definition or existing statement was changed, and
no change record or forced adaptation is necessary.

## Second reading by M1

1. **Interface comparison.** Compared `FlatClosedFibreInterior.lean` with the repository version. The target declaration and its existing public imports are byte-for-byte unchanged; only proof-only imports and the proof body changed. The three added modules and DAG nodes correspond to the declarations they contain.

2. **Proof and axioms.** Compiled all four delivered modules with `lcompile.py --all`; compilation succeeds. The target proof has no `sorry`, and the two split declarations each contain only the documented named `sorry`. No `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or hollow definition was introduced. The helper theorem and private topology lemmas are fully proved.

3. **Statements and split holes.** Checked the two split statements against their docstrings and source tags. Fibre-dimension specialization and strict dimension drop are independent, strictly smaller reductions needed by the target proof; neither restates the target. Their DAG nodes, Lean signatures, source, and proof plans agree.

4. **Route and pruning.** The target follows the recorded Tag 054X route through component selection, flat generalization, specialization, and strict dimension drop. No original proof dependency or import became unused; exploratory imports were removed from the new modules as reported. The unit record has no realized steps to preserve.

5. **Edge cases and visibility.** Empty interiors avoid any point selection; all fibre maps use the canonical pullback comparison. Public imports are limited to statement dependencies, while proof-only imports are plain `import`. No statement or definition used by other modules was changed.

**Changes made during second reading:** appended this section only; no Lean or DAG repairs were necessary.
