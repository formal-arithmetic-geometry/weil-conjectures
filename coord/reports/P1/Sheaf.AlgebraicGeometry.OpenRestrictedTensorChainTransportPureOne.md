## What changed

Proved the only hole of
`Sheaf.AlgebraicGeometry.OpenRestrictedTensorChainTransportPureOne`, preserving the
signature and visibility of
`AlgebraicGeometry.SingleComplexBaseChange.openRestricted_tensor_chain_transport_pure_one`.
The proof-only import is `Sheaf.AlgebraicGeometry.OpenTensorRestrictionSquareStalkUnit`.
Its fully proved private coordinate helpers invert the specified tensor-pullback
stalk unit-germ formula and handle the scalar-extension equality transport. They
reuse the proved argument in `OpenOrdinaryTensorPureGermCoordinatesCanonical`
without importing that development's unrelated pinned-open interface.

Added two fully proved modules, one public theorem each:
`Sheaf.AlgebraicGeometry.OpenTensorRestrictionSquareStalkUnit` calculates the sheaf
unit square from the specified adjunction mates, then applies the generic stalk
square theorem. Its categorical proof uses the two composition-unit identities,
the two open left-adjoint uniqueness identities, and naturality. The second module,
`Sheaf.AlgebraicGeometry.OpenRestrictionStalkSquare`, proves that a commuting square
of arbitrary module morphisms remains commuting under inverse open-stalk coordinates.
Its private germ calculations prove composition, postcomposition, equality transport,
and identification of the restriction adjunction unit with inverse restrictStalkNatIso.
The arbitrary-morphism lemma has no tensor or derived construction in its statement.

The original node and both new nodes record the actual Lean proof route. There are
no existing definition, statement, visibility, or public-import changes. The extra
open namespaces in the existing module are local to its private helpers; all of
its original global commands are preserved.

## Proved and sorry left

Closed the only original hole:
`AlgebraicGeometry.SingleComplexBaseChange.openRestricted_tensor_chain_transport_pure_one`
(node `lem-pc-open-restricted-tensor-chain-transport-pure-one`).

Also fully proved both new public theorems:
`AlgebraicGeometry.SingleComplexBaseChange.openTensorRestrictionSquare_stalk_unit`
(node `lem-pc-open-tensor-restriction-square-stalk-unit`) and
`AlgebraicGeometry.SingleComplexBaseChange.openRestriction_stalk_square`
(node `lem-pc-open-restriction-stalk-square`). All private helpers are proved, and
the private stalkOfHom definition is the actual composition of additive stalk map
and stalkPushforward. There is no sorry in any delivered module and no new axiom.

Holes closed: one. Holes added: zero. This is a proof, not a decomposition leaving
new proof obligations. The second reader's explicit `#print axioms` checks show that all three public
theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`; none
depends on `sorryAx`.

## No longer needed

No original imports or original proof dependencies were removed. All three original
node dependencies remain needed for the specified tensor coordinate calculations.
Both new proof imports are used. All private helpers in the final files are used.

The pinned-open modules examined during the shortcut search are not imported:
`OpenOrdinaryTensorPureGermCoordinatesCanonical` and
`OpenPinnedTensorRestrictionStalkUnit`. They use literal open subschemes and
slice-site equivalence factors, whereas this item uses the actual scheme pullback
and its specified square. The item's ancestors cannot be used as shortcuts because
they depend on it. No modules are claimed pruned by this delivery.

## Where the brief, the DAG or earlier work was wrong

The original node compressed the tensor coordinate calculation and the adjunction
unit square into one prose step. The route is sound, but formalization needs the
separate underived mate calculation and stalk-functoriality calculation now proved
in the two new modules. The existing pinned-open unit lemma is not directly the
statement for the actual pullback scheme and its specified comparison.

The Stacks statements and proofs of Tags 0096 and 0098 were read online, and the
labelled proofs in sheaves.tex were obtained in the sandbox scratchpad. Mathlib's
adjunction mate, pushforward component, restriction-unit and stalk germ formulas
were read locally and used directly. LeanSearch returned Internal Server Error;
Loogle, LeanFinder and grep ran and found the component identities.

The naturality rewrites initially spent heartbeats unfolding large chosen functors.
Local irreducibility in the private categorical calculation and explicit transport
of the final equality avoid that search; no definition was changed and the file
limit was not raised. Empty opens have no z0; identity opens and zero modules use
the same unit and germ formulas. No flatness or nonzero-scalar assumption was added.

## New nodes

`lem-pc-open-tensor-restriction-square-stalk-unit`, in
`dag/nodes/sec-picard-framework/lem-pc-open-tensor-restriction-square-stalk-unit.json`,
records the proved categorical unit square and its application to stalks. Its
module is `lean/Sheaf/AlgebraicGeometry/OpenTensorRestrictionSquareStalkUnit.lean`.

`lem-pc-open-restriction-stalk-square`, in
`dag/nodes/sec-picard-framework/lem-pc-open-restriction-stalk-square.json`, records
proved generic germ functoriality for arbitrary restricted module morphisms. Its
module is `lean/Sheaf/AlgebraicGeometry/OpenRestrictionStalkSquare.lean`.
Both keep the original chapter, unit, and open-local proof route.
There are no change records or forced adaptations.


## Second reading by P1

1. **Interface preservation — pass.** Read the full diff of the existing module
   against the repository. The original declaration's signature is byte for byte
   unchanged, including both pullback-square hypotheses, all scalar structures,
   arbitrary integer degree and the specified inverse restriction coordinates.
   The existing docstring, global commands and public import are preserved.
   Only proved private helpers, a plain proof import and the proof body are added.
   The other two modules are new; no existing definition or statement is altered.
   The parsed declaration comparison reports no statement changes and exactly
   one original sorry removed. There are no forced adaptations or change records.

2. **Kernel proof and data — pass.** Compiled all three modules in import order
   through lcompile.py: clean, in 6.7, 30.9 and 24.7 seconds respectively.
   Explicit `#print axioms` in temporary copies of each module reports precisely
   `propext`, `Classical.choice`, `Quot.sound` for each public theorem, without
   `sorryAx`. The delivered sources contain no sorry, axiom, unsafe, opaque,
   implemented_by, extern or skipped kernel check. The private stalkOfHom is an
   explicit composition of the stalk functor map and stalkPushforward, not a
   chosen existence witness. The chosen adjunction and stalk isomorphism are the
   original specified constructions; their unit/germ normalizations and all
   existence results used in this proof are proved. No new chosen data is added.

3. **Supporting statements and sources — pass.** There are zero split-off holes.
   Read both new theorem signatures, complete docstring arguments and node files,
   and the source text of Stacks Tags 0096 and 0098 in scratchpad/sheaves.tex
   (lemma-adjoint-pullback-pushforward-modules and lemma-stalk-pullback-modules).
   The stalk square assumes exactly a commuting square of arbitrary module
   morphisms a, b, c, and concludes the equality obtained by applying additive
   stalk maps, with point transport in the correct direction. Its h hypothesis
   is the precise sheaf equation proved by square_unit in the other module.
   The unit theorem concerns the actual pullback scheme and the four specified
   comparison factors; no affine, flat, finite, nonzero or derived hypothesis is
   inserted. Empty U has no z0; for the whole open and identity morphisms the
   formulas are the adjunction unit identities; zero modules give zero maps.
   Arbitrary positive or negative degrees are handled independently in the item.
   Independent Loogle search for stalkPushforward, LeanFinder search for unit
   naturality under composite-adjoint comparison, and grep for stalk naturality
   and composition returned component identities, not either full statement.
   Repository searches also found the private tensor_unit_stalk helpers already
   acknowledged in OpenOrdinaryTensorPureGermCoordinatesCanonical, and the open
   pinned theorem with different slice-site comparisons and literal open scheme.
   Neither is an available public direct replacement for this pullback square.

4. **Top-down route and pruning — pass.** Read the original tensorStalkIso
   component equation and exists_tensorMap restriction equation, the inverse
   tensor-pullback stalk germ formula, the four factors defining
   openTensorRestrictionSquareIso and the adjunction mate/uniqueness identities.
   The item first rewrites both coordinate maps, removes equality transport by
   substitution of the scalar map, then evaluates the proved unit-square equality
   on x. square_unit cancels cP, applies the two composition mate identities and
   moves the input open comparison through the q-unit by naturality; the generic
   stalk lemma then uses composition, postcomposition, equality transport and
   the restriction-unit germ identity. All helpers are used. Every import serves
   a public signature or an actual proof, and proof-only imports are plain.
   All three old proof dependencies remain used, so No longer needed correctly
   lists none removed. Read dag/units/sk-thm-picard-semicon.json: its realized
   fields are unchanged; this is the same open-local comparison argument below
   the unit level, without bypassing a unit statement or step.

5. **DAG agreement — pass.** All three node lean.statement strings occur verbatim
   in their modules, and each proof_deps is exactly the union of proof-step uses.
   The item cites the stalk coordinates, scalar-map definition and unit-square
   result actually used. The unit node cites adjunctions, the defined composition
   comparisons, the open square definition and the generic stalk theorem. The
   generic node records the explicit germ calculation and module stalk functor.
   The existing node changes only proof, proof_deps and proof_origin; both new
   nodes have source, creation, chapter/unit, blueprint, searches and complete
   Lean records. Their routes agree with the formal proofs, with no dependency
   cycle introduced by the new chain of proof imports.

Changes by the second reader: added this review and replaced the report's
unverified transitive-axiom disclaimer with the three explicit axiom-check results.
No Lean or node repair was needed. Removed all temporary axiom-check copies before
the delivery. One original hole closed; zero holes added; no modules pruned.
