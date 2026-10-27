## What changed

Replaced the sole `sorry` in `AlgebraicGeometry.ProEtale.adicModuleSliceCompatibility`
with a complete Lean assembly of its unchanged twelve-field conclusion. The item retains
its original structure and theorem signatures and its existing public import. Its proof
privately imports the new coefficient, tensor and closed-comparison modules.

The coefficient ring iso is constructed objectwise from the two supplied coefficient
identifications; naturality and the heterogeneous identity condition are proved.
The native balanced tensor pullback iso and its quotient equation are proved using the
existing native coequalizer API. The module restriction iso is explicitly assembled from
additive section equivalences, a scalar-linearity lemma, and the two naturality equations.
The sectionwise tensor iso is an explicit composite of existing isomorphisms; its entire
compatibility square is proved by cancelling inverse isomorphisms. Its data are not chosen
from an existence theorem. Finally the evaluation equation is proved from the Hom equation
at the identity further slice, the base evaluation formulas and injectivity of sections.

Six new modules and their six nodes record these constructions and the three remaining
normalization obligations. Only the item and its own existing node are modified among
existing files. No shared interface, target signature, source-library declaration or unit
route changes, so no consumer adaptation or change record is required.

## Proved and sorry left

Original hole closed: `AlgebraicGeometry.ProEtale.adicModuleSliceCompatibility`
(`lem-sf-adic-module-slice-compatibility`). The item itself now has zero textual holes.
This is a decomposition, not a complete proof of the original obligation without new holes:
one original hole is closed and three strictly smaller holes are added, for net -2.

Additional proved declarations are `adicSliceCoefficientComparison`,
`adicSliceNativeTensorIso_quotient`, and `adicSliceRestrictionComparison` (all in namespace
`AlgebraicGeometry.ProEtale`). The native, additive and transported tensor isomorphisms are
actual constructions. All private helpers, the tensor square and the evaluation equation
have complete Lean proofs.

Every remaining hole in this delivery, all in namespace `AlgebraicGeometry.ProEtale`:

- `adicSliceSectionEquiv_smul`, node `lem-sf-adic-slice-restriction-linear`, module
  `Sheaf.SixFunctors.AdicSliceRestrictionSections`: only scalar linearity of the fixed,
  explicitly constructed additive section equivalence. Both kinds of naturality, its
  inverse and the assembled natural module iso are already proved elsewhere in the packet.
- `adicSliceTensorIso_sections`, node `lem-sf-adic-slice-tensor`, module
  `Sheaf.SixFunctors.AdicSliceTensorCompatibility`: only the pure-tensor normalization of
  the fixed, explicitly constructed sectionwise tensor iso. Its existence, inverse and
  complete compatibility square are already proved.
- `adicSliceClosedCompatibility`, node `lem-sf-adic-slice-closed`, module
  `Sheaf.SixFunctors.AdicSliceClosedCompatibility`: the Hom equation on further slices and
  bidual equation through the actual native dual maps. This is a proposition containing
  those two equations, not a new choice of comparisons. It does not assert or assume the
  evaluation equation, which the item derives.

Each hole is a whole named public theorem with its source, proof in words and matching node.
No definition or private theorem contains a textual hole. The statements cover arbitrary
modules, including zero modules and zero sections, and arbitrary site objects, including
empty ones. Neither the tensor assertion nor the bidual equation asserts finite rank or
invertibility of a bidual map.

Verification: all seven sandbox files compiled in import order with `lcompile.py --all`,
without warnings or errors. The last complete run took 4.8 to 20.0 seconds per file. The final
server preflight and its axiom probes are run by `deliver3.py`, including the final private
proof-import cleanup. No local Lean or Lake invocation was used.

## No longer needed

No original public import was removed and no existing module is withdrawn. The original
module had no private proof imports to remove. The original six planned dependencies are
no longer direct proof dependencies of the item, but remain needed as plans for the smaller
obligations, so no global pruning of these nodes or modules is claimed:

- `lem-weil-proetale-weakly-etale-localization`,
  `lem-sfb-proetale-object-inverse-image-restriction`, and
  `def-pur-localized-ringed-site` remain below the scalar-linearity obligation.
- `lem-sfb-localized-site-tensor-restriction` remains below the pure-tensor obligation.
- `def-pur-sheaf-hom` and `det-sp-unique-right-adjoint` remain below the closed equations.

A new obligation constructing native tensor pullback is unnecessary: its iso and quotient
normalization follow from the existing proved native API. A new obligation proving the
module restriction naturalities is unnecessary: those follow from the supplied base section
formulas. A new obligation proving the tensor square is unnecessary: the explicit transported
iso makes that square an isomorphism-cancellation calculation. A new obligation for evaluation
restriction is unnecessary: it follows from Hom compatibility at the identity further slice.

## Where the brief, the DAG or earlier work was wrong

There is no disputed statement and no mathematical change to the assigned conclusion.
The old node grouped coefficient, action, tensor, Hom, evaluation and bidual normalization
into two large proof steps. The coefficient, native tensor, naturality, tensor-square and
evaluation substeps can be carried out directly. Only scalar action, pure tensors and the two
closed equations remain; these are recorded separately rather than moving the original
obligation under another name. No unit-level route is bypassed.

The native presentation of adic pullback needs its colimit-preservation instance provided
through the actual `adicUpperStar` functor when applying `Mod.mapModComap` tensor lemmas.
Site-object and module naturality are proved as separate helpers to keep elaboration small.
No timeout setting, transparency option or shared definition was changed to compile them.

## New nodes

`lem-sf-adic-slice-coefficients` owns the proved coefficient iso and identity theorem in
`Sheaf.SixFunctors.AdicSliceCoefficientComparison`.

`lem-sf-adic-slice-native-tensor` owns the explicit native balanced tensor iso and its proved
quotient normalization in `Sheaf.SixFunctors.AdicSliceNativeTensorComparison`.

`lem-sf-adic-slice-restriction-linear` owns the explicit additive section equivalence and its
remaining scalar-linearity theorem in `Sheaf.SixFunctors.AdicSliceRestrictionSections`.

`lem-sf-adic-slice-restriction` owns the two-field restriction record and its proved natural
iso assembly in `Sheaf.SixFunctors.AdicSliceRestrictionComparison`.

`lem-sf-adic-slice-tensor` owns the explicit transported tensor iso and its remaining
pure-tensor normalization in `Sheaf.SixFunctors.AdicSliceTensorCompatibility`.

`lem-sf-adic-slice-closed` owns the proposition comprising the further-slice Hom and native
bidual equations and its remaining theorem in `Sheaf.SixFunctors.AdicSliceClosedCompatibility`.

All inherit the assigned node's chapter and unit. No change records are needed.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
