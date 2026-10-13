## What changed

The unchanged theorem `AlgebraicGeometry.Scheme.root_normalization_generic_stalk_unramified`
is proved from two independent clauses of the original DVR argument:
maximal-ideal equality and separability of the induced residue-field extension.
They are stated in the new modules
`Sheaf.AlgebraicGeometry.Morphisms.RootNormalizationGenericStalkMaximalIdeal` and
`Sheaf.AlgebraicGeometry.Morphisms.RootNormalizationGenericStalkResidueSeparable`.
The item imports these modules privately, together with
`Mathlib.RingTheory.Unramified.LocalRing` for the concluding local criterion.
All original signatures, visibility and public imports are preserved.

The proved private helper
`formallyUnramified_stalkMap_of_maximalIdeal_and_residue` does the actual local-ring
assembly. Finiteness supplies essential finite type via `LocallyOfFiniteType.stalkMap`.
The stalk map supplies the local-hom instance. The helper transports separability
from the canonical scheme residueFieldMap to the residue algebra of the stalk map:
it checks equality of the algebra maps on representatives under the surjective
residue map, where it is definitional. It then applies
`Algebra.FormallyUnramified.of_map_maximalIdeal` (Mathlib's Tag 02FM criterion).
The item's complete proof applies each geometric clause at the same point and
passes both results to that helper. Neither new theorem alone gives the conclusion.

The source read was Stacks [09EB](https://stacks.math.columbia.edu/tag/09EB),
[0BRM](https://stacks.math.columbia.edu/tag/0BRM), and
[0EYG](https://stacks.math.columbia.edu/tag/0EYG), particularly the root-extension
paragraph and the two distinct conclusions of the DVR calculation.
Mathlib's `Unramified/LocalRing.lean`, `Morphisms/FiniteType.lean` and
`Morphisms/FormallyUnramified.lean` were read for the concluding API.
Existing strict-henselization etaleness statements depend on this item and have
stronger hypotheses, so they cannot be used as a shortcut. No cyclic imports
or reverse application of the claimed conclusion is used.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.root_normalization_generic_stalk_unramified`
(node `lem-sbc-root-normalization-generic-stalk-unramified`).
The item's module has no remaining sorry. The private local criterion is proved.

Added two holes, each exactly the whole proof of a public named theorem:

- `AlgebraicGeometry.Scheme.root_normalization_generic_stalk_maximalIdeal`, node
  `lem-sbc-root-normalization-generic-stalk-maximal-ideal`.
- `AlgebraicGeometry.Scheme.root_normalization_generic_stalk_residue_separable`, node
  `lem-sbc-root-normalization-generic-stalk-residue-separable`.

This is a decomposition: one upper hole closed, two strictly weaker independent
clauses added, net -1 holes closed. It is not a sorry-free proof of the geometric
Abhyankar calculation. Both modules have complete source and proof docstrings.
Neither assumes the upper unramified statement, supplies an etale neighbourhood,
or chooses any data from an unproved existence theorem.

Edge cases checked mathematically: a finite group has positive cardinality;
when its cardinality is one, the root equation has degree one and the original
cover is unramified. Empty normalization fibres are vacuous. The domain quotient
excludes a unit divisor equation. No perfectness of the base residue field is
assumed: the prime-to-characteristic degree argument supplies separability.
Without the root extension, tame ramification need not have maximal-ideal equality;
without invertibility of the group order, inseparable residues and wild ramification
are possible. These hypotheses remain in both new statements.

## No longer needed

No original import or geometric node is pruned. The direct dependency on
`lem-sbc-normalization-stalk-base-change` moves beneath the two new clauses;
it is still needed for their planned proofs and is not reported as pruned.
The new modules import only what their statements use; the local unramified
criterion is a proof import of the item, not a public import of either new module.

The nodes for flatness, source etale neighbourhoods, purity and strict
henselization are not needed in this proof and are not imported. They were
already absent from the item's original proof_deps, so no existing branch is
claimed as pruned. The unit's trait/tame-root route is preserved. Its realized fields are empty
in the repository, and this item is not its key statement; this delivery does
not fill or alter those fields.

## Where the brief, the DAG or earlier work was wrong

The existing node's first two steps use non-elementary DVR and tame Galois
arguments but cite no stated nodes. Its sole dependency, normalization under
stalk base change, cannot supply ramification-index one or residue separability.
The two new nodes expose precisely these two missing conclusions; the final
finite-type local-ring assembly is now complete Lean.

The source label for the concluding algebra criterion is Tag 02FM, matching
Mathlib's `Algebra.FormallyUnramified.of_map_maximalIdeal`; the original node
mentions 02GF. This delivery does not alter any statement.
The local clone has only the literature index files, so the cited Stacks pages
were read online. LeanSearch returned Internal Server Error; this is recorded
as unavailable, not as evidence of no match. Loogle, LeanFinder and grep
returned local criteria/degree formulas but no exact geometric root-normalization
clause. The existing tame-root-product residue theorem was also read: it needs an
explicit product-of-root-algebras model, which the present hypotheses do not
supply. The existing trait-section residue theorem additionally needs a smooth
family, section and trait-chart data, also absent here. Neither can replace the
new residue clause without another geometric chart-construction hole.
Blueprint searches for ramification and unramified gave no matching
imported statement; the spreading unit's tame-root calculation remains the source.

## New nodes

`lem-sbc-root-normalization-generic-stalk-maximal-ideal` states only the
ramification-index-one consequence as an equality of the actual stalk maximal
ideals. It preserves the geometric input and identifies the local root divisor
and the relevant normalized factors in its proof outline. It neither states nor
assumes residue separability of the resulting map.

`lem-sbc-root-normalization-generic-stalk-residue-separable` states only
separability for the canonical scheme residue-field map at the indicated point.
Its outline explains the stabilizer degrees, the exclusion of inseparable degree
and the residue-separability conclusion after tame root base change. It neither
states nor assumes maximal-ideal equality of the resulting map.

Both are in the original chapter and unit, record searches actually run in
searches.jsonl, and cite normalization-stalk-base-change for localization.
No definition, existing statement or external interface is changed, so no change
record or forced adaptation is needed.

## Second reading by J4

1. **Interfaces — pass.** Read all three delivered modules and diffed the item
   against the repository. The existing theorem signature is byte for byte
   unchanged; its docstring and public imports also remain unchanged. The only
   existing-module edits are three private proof imports, a proved private
   helper, and the replacement of the original sorry. No definitions or target
   statements change; no change record or forced adaptation is required.
2. **Proof and axioms — pass, with the reported decomposition.** Compiled all
   three files in import order using lcompile.py. The item contains no sorry;
   only the two listed public geometric theorems have sorry. No axiom, unsafe,
   opaque, implemented_by, extern, hollow definition, or choice of arbitrary
   data from an open existence theorem occurs. Inspected the residue algebra
   comparison: surjectivity of the residue quotient reduces equality to rfl on
   stalk representatives. The helper supplies localness and essential finite
   type and applies the actual Mathlib local criterion, not an assumed
   conclusion. A scratch-copy #print axioms check is recorded below.
3. **Split statements — pass.** Read Stacks 09EB, 0BRM, 0EYG, and 09E7,
   including the root-extension paragraph of 0EYG and the adic formal smoothness
   conclusion of 0BRM. The two new statements retain every geometric input and
   assert the two separate local consequences. Neither is a restatement of
   formal unramifiedness: the criterion needs their conjunction. The regular
   nonzerodivisor and domain quotient make the principal local maximal ideals
   into DVRs, without an unstated global domain or excellence assumption on H.
   The finite G-torsor's connected field factors have stabilizer groups, so
   their Galois degrees divide |G|. Invertibility excludes wild indices and
   inseparable residue degrees. Checked |G|=1, split/disconnected torsors,
   empty normalization fibres, and positive characteristic with imperfect
   residue fields. The degree-one case is the identity DVR extension; unit g
   and a zero base ring are excluded by the domain quotient instance.
   Repeated LeanFinder, Loogle and grep searches with new wording, recorded in
   searches.jsonl. Hits give degree formulas, the reverse implication from
   unramifiedness, or the already used local criterion, not these geometric
   clauses. Read tameRootProduct_residue_separable and the trait-section
   residue proof: their root-chart/trait-section inputs are not provided here.
   No split can be closed in a few minutes by those declarations.
4. **Route and pruning — pass.** The proof completes the local algebra assembly
   and leaves precisely its two geometric inputs open. The proof imports are
   private; the new modules' public imports support their unchanged-input
   signatures. The old sole proof dependency,
   lem-sbc-normalization-stalk-base-change, is no longer a direct dependency
   of the item but remains below both new clauses; it is explicitly accounted
   for under No longer needed. No module is claimed as pruned. Read
   dag/units/sk-prop-input-spreading.json: the tame trait/root step is retained,
   and this auxiliary item is not the unit's key statement. Its existing empty
   realized record is unchanged.
5. **DAG agreement — pass after repairs.** The existing node changes only proof,
   proof_deps, and proof_origin. Their two new dependencies exactly match the
   two geometric applications in Lean. Both new nodes have source, complete
   proof, matching verbatim Lean signatures, searches, created/blueprint
   records, chapter and unit, and the localization dependency. Their planned
   proofs remain explicitly non-elementary and open.

Second reading changed only documentation and node text: fixed doubled TeX
backslashes in both new node statements; explicitly cited Tag 09E7 in both
new theorem docstrings and node sources; made clear that 0BRM gives adic
formal smoothness and 09E7 supplies its index-one and separable-residue
consequences; synchronized the node proof text with each docstring; clarified
the unchanged unit realized record. The correct compiled proof was retained.
This remains one original hole closed and two holes added, not a net proof gain.

Scratch-copy axioms check: the private helper depends only on propext,
Classical.choice and Quot.sound. The original theorem and both new geometric
theorems depend on those three and sorryAx, exactly as expected while the two
reported geometric clauses remain open. The scratch copy was removed.
