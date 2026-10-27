## What changed

Partial stage-3 reduction of `Sheaf.AlgebraicGeometry.FormalCoefficientTransformCriterion`.
The signature of `AlgebraicGeometry.HilbertCoefficient.coefficient_field_extension` is
unchanged. Its proof now decomposes the five formal conditions and reassembles their
coefficientwise extensions in Lean. Four proved private helpers establish preservation
of order, commutation of partial derivatives, commutation of iterated partial derivatives,
and containment of mapped transverse ideals. The block Jacobian follows by mapping its
unit determinant and comparing entries. These arguments use coefficient injectivity,
`MvPowerSeries.coeff_pderiv`, `Ideal.mem_map_of_mem`, and `RingHom.map_det`.

The supported-division and finite-jet-length steps are isolated in two new modules,
`Sheaf.AlgebraicGeometry.FormalDivisionScalarExtension` and
`Sheaf.AlgebraicGeometry.FormalJetLengthScalarExtension`. Their hypotheses omit the
Jacobian and later-generator conditions; the length statement applies to every ideal.
Neither statement repackages the original theorem: the actual order, derivative,
transverse-ideal and determinant arguments remain proved in the item module. Each new
module has one named theorem with a source, complete proof in words, and matching node.
The item's step 14 and proof dependencies record this reduction; its other eight plans stay.
No existing signature, definition, public import, attribute, or consumer was changed.

Read BM 1997, Remark 3.8 (printed p.234), (7.2), Lemmas 7.3 and 7.5 and Corollary 7.4
(p.263), and Theorem 9.4 and proof (pp.277--278), from the published journal PDF obtained
at the URL recorded in the earlier NL report. The copy and extracted text are in this
sandbox's scratchpad. Read ILO VIII 2.3.11--2.3.13 (pp.93--94) and the current blueprint
ancestor `lem-trf-local-term-locality`. The scalar-extension detail is an agent-written
expansion of the source argument, recorded as such. The historical branch and unit are
unchanged; no unit statement or realized step is bypassed.

Searches used the prescribed msearch LeanFinder, Loogle, LeanSearch, and grep services,
plus rg in Mathlib and both project roots. The Loogle hit `MvPowerSeries.le_order_map`
is used. The remaining hits concern coefficient maps, univariate division, fractional
ideals and homogeneous ideals, rather than these scalar-extension statements. Read the
signatures of all six original dependency modules, including the coordinate-blowup and
continuous-division interfaces. The latter uses an injective vertex family over `Fin n`;
the item's field-extension clause has arbitrary vertices over `Fin m ⊕ Fin n`, and no
coordinate-center hypothesis. The new statements expose precisely its missing general
scalar-extension steps, without adding those hypotheses to the item.

Checked empty generator families (supported generation then forces the zero ideal),
zero variables, repeated or redundant vertices under the supplied uniqueness hypothesis,
zero and unit ideals, degree zero, empty Jacobian blocks, arbitrary extensions in separate
universes, and target coefficients outside the image of the source field. The new proofs
in words use inverse matrices on all target vectors and multiplier truncation, so they
do not assume coefficient-map surjectivity or that infinite formal series are tensor
products. For jet length, the finite nilpotent filtration compares ring-module length
with dimension, including the zero quotient.

Validation: all three modules compiled cleanly through `lcompile.py --all`; the item
compiled in 19.1 seconds before final import cleanup. The delivery tool performs the
final compilation and axiom probes after that cleanup. The sandbox contains only these
three Lean modules, their three node records, and this report, besides scratch/search
and launcher bookkeeping that the delivery tool excludes.

## Proved and sorry left

Original holes: 9. Closed body: `AlgebraicGeometry.HilbertCoefficient.coefficient_field_extension`.
New intermediate holes: 2. This is a decomposition, not a completed independent proof:
the net hole count of this packet is 1 closed minus 2 added = -1. The item itself has
8 remaining holes, and the three delivered modules have 10 holes in total.

The four private helpers `coefficient_order_map`, `coefficient_pderiv_map`,
`coefficient_iteratedPartial_map`, and `coefficient_transverseIdeal_map` are fully proved.

The following original named theorems remain unchanged with `sorry`, all attached to
`lem-trf-formal-coefficient-transform-criterion` (names have namespace
`AlgebraicGeometry.HilbertCoefficient`):

- `coefficient_equality_germ`
- `coefficient_permissible_chart`
- `coefficient_boundary_chart`
- `coefficient_free_variable`
- `coefficient_regular_permissible`
- `coefficient_regular_boundary`
- `coefficient_regular_line`
- `coefficient_regular_etale`

The delivery adds exactly these two named holes:

- `AlgebraicGeometry.HilbertCoefficient.formal_division_scalar_extension`, node
  `lem-trf-formal-division-scalar-extension`.
- `AlgebraicGeometry.HilbertCoefficient.formal_jet_length_scalar_extension`, node
  `lem-trf-formal-jet-length-scalar-extension`.

Every remaining hole is the entire proof of a public named theorem. There are no new
axioms, data holes, private holes, or arbitrary choices from unproved existence assertions.

## No longer needed

Removed the item's unused private imports of
`Sheaf.AlgebraicGeometry.FormalHilbertStratumMinors` and
`Sheaf.AlgebraicGeometry.JetDiagramHilbertControl`. Neither supplies a declaration used
by the completed field-extension assembly. The two new imports are private proof imports.
The original six dependency nodes remain in the DAG because the other eight theorem
plans still need them; no module or node is withdrawn or claimed globally pruned.
All existing public imports are retained to preserve the interface.

## Where the brief, the DAG or earlier work was wrong

No false original statement was established. Step 14's prose about finite matrix
identities did not have an existing theorem matching supported scalar extension in the
item's full generality, and its finite jet assertion was not yet available as a
ring-module-length equality. Those two gaps are now explicit statements. BM Remark 3.8,
rather than Remark 3.7 alone, explicitly discusses changing residue fields.
There is no current return or quarantine entry for this item. V2's return for
`CompletionThickeningCokernelReflection` concerns a different module and was not edited.

## New nodes

`lem-trf-formal-division-scalar-extension`, in
`dag/nodes/sec-trace-formula/lem-trf-formal-division-scalar-extension.json`, realizes the
supported-division scalar-extension portion of step 14. It states persistence of
homogeneous division for every prefix and supported expansions for the extended ideal,
using only the generator membership, orders, homogeneous division and source expansions.
The finite inverse-matrix argument and the continuous division/truncated multiplier
argument are recorded in full. Its new module is `FormalDivisionScalarExtension`.

`lem-trf-formal-jet-length-scalar-extension`, in
`dag/nodes/sec-trace-formula/lem-trf-formal-jet-length-scalar-extension.json`, realizes
the finite-jet dimension portion of step 14, with the exact `extendedHilbert` length
convention. It applies to arbitrary ideals and finite variable sets in any characteristic.
The proof identifies the extended relation subspace, compares quotient dimensions, and
then compares lengths with dimensions using the variable-power filtration. Its new module
is `FormalJetLengthScalarExtension`.

Both nodes inherit the item's chapter and unit and point to its blueprint ancestor.
Blueprint searches for `jet length` and `homogeneous division` found no imported node;
project searches found no duplicate of either statement. Each node records the three
actual Mathlib search kinds. No change record is needed: all existing interfaces and
consumer signatures are unchanged.

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
