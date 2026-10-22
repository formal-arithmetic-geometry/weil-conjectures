## What changed

Filled `AlgebraicGeometry.Etale.exceptional_tensor_and_base_change` by tensor
projection and Cartesian exchange calculations. Taking counit transposes reduces
the tensor square to a generic component calculation using the compact-scalar
projection square, projection naturality, evaluation compatibility and the proved
scalar right-unit law. A private component accessor keeps the site monoidal parameters
shared when applying that unit law.
The base-change calculation pastes the proper scalar/exchange square with the
proved open scalar square, transfers it to the chosen compactification, and applies
the existing coefficient-exchange mate theorem. Finite Tor amplitude gives a lower bound after tensoring with the scalar
coefficient sheaf. The existing scalar tensor comparison transports this bound to
scalar restriction; exactness and faithfulness of restriction reflect the bound
needed by the existing compactification-refinement coherence statement.

Moved the unchanged normalized map definitions, normalization predicates and their
construction proofs to `ExceptionalCoefficientMaps`. Its private K-flat
preservation wrapper reuses the identical proved result from
`EtaleHomComparisonModels` instead of rechecking the duplicate construction. A
private generic normalization lemma also keeps the reverse flat-model implication
at the abstract category level. The unit-existence proof
passes through a site-level specialization of the existing generic construction,
with unit-representative invertibility proved separately. These proof changes
avoid repeated expansion of sheaf monoidal data; the extracted public definition
bodies stay unchanged. The private compact-support isomorphism uses its components and is
sealed behind component equations used by the mate calculations. The item publicly
reexports this module. `EtaleCompactScalarCoherence` changes only its corresponding
public import. This breaks the original import cycle without changing any existing
public signature or mathematical object. The coherence node carries a
`statement_change` record explicitly citing those lower definition owners; its six
existing citers retain the same normalized arrows and coherence equations.
No adopted source-library file changes.
The change record is `coord/changes/exceptional-coefficient-lower-maps.md`.

Refactored `tensorDomainMap` to compose the existing
`compactScalarProjectionTarget` with the same tensor image of the unit mate.
The new `dualizingScalarMap` names that actual unit-mate composite; its defining
equation proves that this is precisely the arrow used before. The new name is a
construction, with no arbitrary witness or postponed proof.
This associates the same three arrows as `(δ ≫ κ) ≫ v` instead of `δ ≫ (κ ≫ v)`;
`Category.assoc` identifies them. The coefficient unit is written literally as the tensor unit, definitionally
equal to `constantComplex`, throughout this construction and its private proofs.
Its signature and `TensorCompatibility` statement
are unchanged. The definition now has a definitional component API, which avoids
repeated normalization of the expanded formula. Its defining dependency is a
public import. No external module refers directly to `tensorDomainMap`, so no
consumer proof changes are needed. The corresponding definition node and change
record explicitly describe the reassociation and the named unit-mate composite. Its
`statement_change` record archives the previous text, dependencies and proof, and
audits the unchanged use by `lem-pur-finite-adjoint-mate-compatibility`.
Private projection isomorphisms and a private compact-support isomorphism for the
chosen compactification give the native adjunction functors a shared component API.
The generic tensor calculation takes the projection isomorphisms themselves and
uses their inverse fields. The ordered tensor normalization is proved first with
the coefficient category variable and then specialized to modules. The tensor
proof locally restores normal transparency checks, so these private interfaces
remain opaque during elaboration and the constructed maps stay shared.


Validation: the final nine-file sandbox compiles in import order through the
project compile service, with the complete item taking 49.8 seconds under the
unchanged 60-second limit. All 24 existing public declaration headers remain
unchanged; `dualizingScalarMap` is an added definition. The twelve node records
parse successfully, and no delivery source contains a diagnostic probe. The only remaining `sorry` occurrences in the packet are
the four unchanged coherence theorems listed below. The seven new nodes now also record individual LeanSearch queries alongside
the original LeanFinder/Loogle and grep searches. The consumer audit includes the
fifteen lexical matches whose tensorIso/unitIso/TensorCompatibility names refer
to other constructions.
The delivery command repeats compilation and performs the required static and
consumer checks before pushing.


## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.exceptional_tensor_and_base_change`
(node `b3-exceptional-tensor-base-change`), the item's only original hole.
Added holes: none. All seven new modules have complete proofs or unchanged actual
definitions. This is a proof from the existing stated dependencies, not a new
unfinished decomposition.

The adapted `EtaleCompactScalarCoherence` retains its four original holes without
changing their statements or proof bodies:
`AlgebraicGeometry.Etale.etaleCompactScalarCoherence`,
`AlgebraicGeometry.Etale.etaleCompactScalarComposition`,
`AlgebraicGeometry.Etale.etaleCompactScalarOpenRestriction`, and
`AlgebraicGeometry.Etale.etaleCompactScalarUnit`
(node `lem-pur-etale-compact-scalar-coherence`). The new proof uses the first of
these, specifically its projection and bounded-below refinement conclusions.
Other preexisting dependency holes are not claimed as closed.

## No longer needed

No module is withdrawn. No adopted source declaration is removed.
The main module retains its existing public imports so consumers see the same API.
The old direct dependency edges from `b3-exceptional-tensor-base-change` to
`lem-amb-proper-coproducts-projection` and
`lem-amb-unbounded-compact-support-comparisons` are replaced by the precise ordered
projection and compact-scalar exchange route. Both old nodes are still needed
indirectly; this is not a claim that their modules can be pruned.
The normalization construction dependencies formerly attached to
`def-pur-exceptional-coefficient-tensor-maps` move to the new lower normalization
node; no mathematics is discarded. The lower maps module does not need
`FiniteReductionConstructibility` or smooth exceptional base change, so those
imports stay only in the original module, where the remaining statements need them.
The main proof no longer imports the following construction-only modules directly:
`WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange`,
`WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit`,
`WeilConjectures.CategoryTheory.Sites.ReductionFlat`,
`Sheaf.SixFunctors.EtaleHomComparisonModels`, and
`Sheaf.CategoryTheory.DerivedTensorRightExact`. The lower normalization construction
still needs them; they are not globally pruned.
The main proof also no longer needs `import all` of the extracted maps module,
`ExactRightDerivedAdjointKFlatRepresentative`, or `KFlatAcyclic`: the existing
`scalarTensorIso` and exact faithful scalar restriction give the required lower
bound directly. The K-flat machinery remains needed by the normalization
construction and is not globally pruned.
The lower maps module also drops the unused private import
`Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtension`; the main proof retains
that import for compact-support invertibility.
The unit proof does not need private helpers from `PurEtaleScalarMateProjection`.
The already proved `derivedTensorSymmetry_involutive` supplies the exact canonical
signed symmetry identity; an experimental duplicate symmetry helper was discarded
before delivery.

## Where the brief, the DAG or earlier work was wrong

The compact-scalar coherence module imported the item itself only to obtain its
normalized maps. Using that stated dependency to prove the item's last hole would
therefore create an import cycle. The extraction preserves the lower maps verbatim
and makes the dependency usable. The generic mate argument also needs right-unit
coherence, whereas the existing compact-scalar unit theorem states a different
left-unit law; the right-unit equation is proved here from the actual tensor and
unit normalizations. The existing open-restriction theorem assumes an open base
map, so it cannot supply arbitrary Cartesian open exchange; the required arbitrary
square is proved from units and the existing scalar pullback composition theorem.

## New nodes

`def-pur-exceptional-coefficient-normalizations` records the unchanged lower tensor
and unit constructions in `ExceptionalCoefficientMaps`.

`lem-pur-scalar-right-unit-transport` records the generic representative right-unit
calculation, including its natural-transformation construction.

`lem-pur-scalar-right-unit` records the normalized scalar right-unit law, proved by
localization and K-flat representatives.

`lem-pur-ordered-tensor-coefficient-mate` records the component projection calculation
transporting the inverse-projection/evaluation composite across coefficients.
The main proof separately uses the adjunction Hom bijection to recover the mate square.

`lem-pur-open-scalar-exchange-unit-mates` records the generic open exchange square
proved by transposing and using its prescribed unit equations.

`lem-pur-open-scalar-exchange-square` records arbitrary Cartesian compatibility of
open scalar balancing with exact inverse-image open base change.

`lem-pur-compact-scalar-base-change` records the compact-support scalar/exchange
square on the bounded-below pair of inputs, with the chosen compactifications.

Change record: `coord/changes/exceptional-coefficient-lower-maps.md`.

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
