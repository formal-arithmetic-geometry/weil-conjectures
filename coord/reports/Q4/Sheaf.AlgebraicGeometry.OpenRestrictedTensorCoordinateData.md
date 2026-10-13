## What changed

Preserved the signature and visibility of
`AlgebraicGeometry.SingleComplexBaseChange.exists_openRestricted_tensor_coordinate_data`.
Its proof now obtains normalized stalk coordinates, constructs the tensor-complex
isomorphism, proves its pure tensor formula, and applies the remaining homology transport
statement. Two proof-only imports name the two new modules. The original public import
is retained because the statement uses its constructed restriction and derived maps.

`Sheaf.AlgebraicGeometry.OpenRestrictedStalkCoordinates` proves
`exists_openRestricted_stalk_coordinates`. The four ring isomorphisms are actual open
stalk maps or point-congruence maps. A private linear natural isomorphism, proved directly
from the same-germ formulas, supplies the input-chain isomorphism with a degreewise
normalization. The proof verifies both base-algebra equations and the tensor-ring equation.
The semilinearity argument follows the proved private argument in
`Sheaf.AlgebraicGeometry.Modules.RestrictionStalkExtensionIso`; its public extension-of-scalars
statement is not used. No arbitrary witness is chosen for a definition.

Private tensor helpers in the parent follow the already proved construction in
`Sheaf.AlgebraicGeometry.AffineSpectrumTensorCoordinateData`: `TensorProduct.congr`, scalar
linearity by tensor induction, and `HomologicalComplex.Hom.isoOfComponents` with differential
compatibility. Specializing the tensor-ring equation at `(a, 1)` supplies the scalar
compatibility needed by those helpers. Thus tensor existence and the pure tensor formula
are proved in this delivery, rather than postponed in a new theorem.

`Sheaf.AlgebraicGeometry.OpenRestrictedTensorHomologyTransport` isolates the final homology
square for GIVEN ring and chain isomorphisms. It assumes the actual projection stalk map,
the same-germ input normalization, and the pure tensor formula. It asserts no existential
coordinate construction or base-algebra compatibility. Its docstring gives the full germ,
homology, and exact-localization argument. Both new statements were checked on the empty
open (there is no z0), top opens, zero rings and zero complexes; no extra nonzero,
boundedness, flatness or finite-dimensional hypothesis was introduced.

The coordinate module publicly imports only the stalk-condition interface;
`OpenDerivedStalkIso` and
`WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk` are proof-only imports.
The latter supplies the scheme module-stalk scalar-action instances used by the germ proof.

The three delivered modules compile together using `lcompile.py --all`. The parent's node
now records the actual reduction. The unit `sk-thm-picard-semicon` has no realized nodes
in its statement or proof steps, and its route is unchanged.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.SingleComplexBaseChange.exists_openRestricted_tensor_coordinate_data`
(node `lem-pc-open-restricted-tensor-coordinate-data`). Its proof is complete Lean FROM
the new homology lemma; this is a decomposition, not an axiom-free proof of the whole
original statement.

Also proved, without any local hole:
`AlgebraicGeometry.SingleComplexBaseChange.exists_openRestricted_stalk_coordinates`
(node `lem-pc-open-restricted-stalk-coordinates`), including the normalized input-chain
isomorphism and the three ring compatibility equations. Every private helper is proved.

The delivery adds exactly one hole, whose proof is exactly `:= by sorry`:
`AlgebraicGeometry.SingleComplexBaseChange.openRestricted_tensor_homology_transport`
(node `lem-pc-open-restricted-tensor-homology-transport`). No sorry remains in the parent
or the stalk-coordinate module. Net local holes closed minus holes added is zero; the
maintainer's pinned closure ledger determines the global figures.

## No longer needed

No original import was removed: the one original public import is needed by the public
statement. No affine-coordinate module is imported; its generic tensor construction was
read and reused as proved private helpers, without its affine geometric hypotheses or
its unproved coordinate theorem.

The original proof dependency `lem-pc-open-restriction-stalk-extension-iso`, module
`Sheaf.AlgebraicGeometry.Modules.RestrictionStalkExtensionIso`, is no longer needed on this
route. The proof constructs the normalized linear restriction comparison directly and
uses its inverse, so extension-of-scalars and the extension/restriction adjunction counit
are unnecessary. This does not assert that the module is unreachable from other targets.

The original direct proof dependencies `def-pc-single-complex-base-change-stalk-condition`,
`lem-weil-pbc-module-stalk-pullback`, `def-pc-open-derived-stalk-iso`, and
`def-pc-open-restricted-tensor-complex-iso` are retained through the two new nodes. They
remain necessary for the statements and the remaining homology argument.

## Where the brief, the DAG or earlier work was wrong

The planned extension-of-scalars isomorphism does not itself provide the normalization
needed by the homology square: an arbitrary input-chain isomorphism can change that
square. The new coordinate theorem therefore fixes q degreewise to the inverse same-germ
map after the pullback point congruence, and fixes eD to the actual projection stalk map.
The remaining theorem uses both normalizations explicitly. This is a clarification of
the proof route, with no change to any existing statement or definition.

The source pages Stacks Tags 0098 and 0D5U were read. LeanSearch returned an internal
server error; LeanFinder, Loogle, and recorded local Mathlib searches were used instead.
No forced adaptations or change records are needed.

## New nodes

`lem-pc-open-restricted-stalk-coordinates`, in
`dag/nodes/sec-picard-framework/lem-pc-open-restricted-stalk-coordinates.json`, records the
proved normalized ring/input-chain construction, source, germ proof, and exact Lean
signature. Its module is `Sheaf.AlgebraicGeometry.OpenRestrictedStalkCoordinates`.

`lem-pc-open-restricted-tensor-homology-transport`, in
`dag/nodes/sec-picard-framework/lem-pc-open-restricted-tensor-homology-transport.json`, records
the remaining homology square with GIVEN normalized coordinates, the germ and exact
restriction proof, source, and exact Lean signature. Its module is
`Sheaf.AlgebraicGeometry.OpenRestrictedTensorHomologyTransport`.

## Second reading by Q4

1. I compared the delivered parent module with the repository version. The existing
   theorem signature and visibility are unchanged byte for byte; only proof-only imports,
   private helpers, and the proof body changed. Verdict: pass.
2. I compiled all three delivered modules with `lcompile.py --all` and checked that the
   only remaining `sorry` is the named public homology-transport theorem. No forbidden
   declarations or hollow definitions occur. Verdict: pass.
3. I checked both split-off statements against their docstrings, nodes, and small edge
   cases (empty opens, top opens, zero rings, and zero complexes). They are strict
   reductions of the parent target and introduce no extra hypotheses. Verdict: pass.
4. I checked the proof route and imports. The parent uses the normalized coordinate node,
   the tensor-complex construction, and the homology transport node; the old extension
   isomorphism dependency is no longer used. The unit route and realized fields are
   preserved. Verdict: pass.
5. I checked that node `proof`, `proof_deps`, and `proof_origin` match the Lean proof,
   and that both new nodes contain the required source, statement, and declaration data.
   Verdict: pass.

I changed only this report section; no Lean statements or definitions were changed during
the second reading.
