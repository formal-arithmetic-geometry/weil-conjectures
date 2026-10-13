## What changed

Reduced `AlgebraicGeometry.exists_overlap_pair_map_at_stage`, without changing its signature,
to existing fixed-model local map descent and one canonical transport calculation.

The proof constructs the universal original overlap `H = U_a ×_{X_j} U_b` and its map
`g : H → Spec R_j`. It proves the required geometric hypotheses for `g`, restricts the two
finitely presented quasi-coherent chart modules to the identity base change of `H`, and
constructs their conjugated limit transition explicitly. It applies
`exists_finitePresentation_local_map_datum` with both original and starting index `j`.
Surjectivity of Zariski restriction on morphisms gives a global map with the supplied local
components. Injectivity on the pulled-back limit cover proves its global recovery equation.
The stage overlap map is then the explicit `overlapPairMapOfModel` of that global map.

Added `Sheaf.AlgebraicGeometry.OverlapPairModelTransport`, containing the universal model maps,
canonical comparison isomorphisms, conjugated limit map, explicit stage overlap map, and the
remaining fixed-stage transport theorem. All definitions have real construction bodies.
`overlapModelLimitToBase_comp` and all proof obligations in these definitions are proved.
The tensor/abstract comparison is left-adjoint uniqueness for the canonical adjunctions;
no arbitrary model or map is chosen from an unproved existence theorem.

Added proof imports of the model transport module, local map datum, `FiniteDescent`, and
`ZariskiDescent`. Removed the direct proof import of `FinitePresentationColimit`.
Updated the item's node proof, proof dependencies, and proof origin to match this route.
No existing definition, statement, public import, target signature, or downstream module changes.

Validation: both delivered Lean modules compile together with no errors or warnings through
`lcompile.py --all`. The target proof uses actual gluing and recovery equations, not one
application of a renamed lifting statement. The new transport statement has a fixed given
stage and a given recovered map; it requires no directedness, limit, affineness, Noetherianity,
finite presentation, quasi-coherence, or finite cover. It concludes the square for an explicit
map and does not assert that a later stage or lifted map exists.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.exists_overlap_pair_map_at_stage`
(node `lem-pc-fp-overlap-pair-single-stage`). There is no `sorry` left in the item's module.

Added one hole: `AlgebraicGeometry.overlap_pair_square_of_model_recovery`
(node `lem-pc-overlap-pair-model-transport`), in the new module
`Sheaf.AlgebraicGeometry.OverlapPairModelTransport`. Its proof is exactly `by sorry`.
Its docstring and node give the projection, adjunction, naturality, and associativity argument.

This is a decomposition: one original hole closed and one smaller transport hole added,
not a claim of a net reduction in holes or an axiom-free proof of the original theorem.
The existing local descent module and its lower affine lifting/overlap agreement declarations
remain dependencies, as intended in stage 3. No other holes are added or edited.

## No longer needed

Removed the direct import `Sheaf.Algebra.FinitePresentationColimit`, and the item's direct
proof dependency `lem-pc-fp-module-map-descent-affine`. The algebra theorem remains used
transitively by existing local map descent; this is not a claim that its module is globally
unreachable. The overlap transition and canonical-comparison definitions likewise remain
needed through the new model module and the unchanged target signature.

No existing module is claimed globally pruned. No persistence theorem is imported or used.
The original pairwise affine lifting and gluing work is reused through the already stated
local map datum instead of duplicated as new lifting statements. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No false statement or source error was found. The original plan had not exposed the canonical
comparison calculation required to apply ordinary fixed-model map descent to the universal
overlap. The new node isolates precisely that calculation, while the main module performs
the actual lifting and gluing from existing declarations.

The overlap need not be affine: the proof only uses quasi-separatedness of `X_j` and the
compact affine source of `U_b → X_j` to get quasi-compactness, then uses the local descent
lemma on `H`. Noetherianity is retained in the existing signature and in the invoked interface.
An empty overlap has the same universal constructions and unique maps; repeated charts and
zero modules impose no extra hypothesis. A preorder is passed unchanged to existing local
descent; no antisymmetry or extra nonemptiness assumption is added.

Read Stacks Tags 01ZR and 0096. Searched the library, Mathlib, and the whole imported blueprint
for overlap transport, 01ZR, and 0096. LeanFinder found pullback composition, scheme pullback
chart isomorphisms, and the adjunction mate comparison, but no exact theorem. LeanSearch was
unavailable and was recorded as unavailable. Grep and Loogle searches are in `searches.jsonl`.
The blueprint ancestor lookup returned no ancestor because the item's creation record names a
module; the new node inherits the existing item's recorded ancestor
`lem-pc-rf-perfect-base-change` and its chain. No blueprint reference is changed.

Zariski morphism gluing is used as a closed library tool, in the same way as the existing
proof of the map clause of `FinitePresentationModuleMapDescent`; that larger module is not
imported, which would create a cycle through its object clause.

## New nodes

`lem-pc-overlap-pair-model-transport`, in
`dag/nodes/sec-picard-framework/lem-pc-overlap-pair-model-transport.json`, states only that a
recovered map on the explicit original-overlap model gives the canonical square for the
explicit stage overlap map. It removes all analytic descent hypotheses and does not assert
stage existence. The real definitions construct both maps and all component comparisons;
the remaining proof compares them by universal pullback uniqueness and adjunction coherence.
This node has the item's chapter and unit, a complete proof in words, the three actual search
kinds, and the verbatim Lean signature. No change record or forced adaptation is needed.


## Second reading by R4

1. Compared the existing module against the repository with `diff` and the declaration
   parser: the existing theorem signature and docstring are byte-for-byte unchanged.
   All original public imports remain. No existing definition or target changed, and
   no forced adaptation or change record is needed. Verdict: pass.

2. Compiled both delivered files through `lcompile.py --all`: no errors or warnings.
   Audited every new definition: actual universal pullback maps and composition
   isomorphisms, with proved internal obligations. The only choice is the tensor
   adjunction whose unit is pinned sectionwise by `exists_tensorPullbackAdjunction`;
   this determines its Hom equivalence and hence the adjunction, and is the identical
   choice used by `tensorPullbackCompositionIso`. There is no arbitrary descent
   witness in a definition. Scanned both files for prohibited declarations and
   checked the axioms of every delivered declaration in a separate scratch module.
   The sole new direct hole is the reported transport theorem. Verdict: pass,
   conditional on that named hole and the existing descent dependencies.

3. Read the new transport theorem from its hypotheses through its explicit conclusion,
   and checked its docstring and node proof against the constructions. It is a
   strictly smaller fixed-map coherence calculation, not a renamed existential
   lifting theorem. Pulling back the recovery equation along the universal limit
   overlap gives the result: the two maps into the fixed model have equal projections,
   the tensor/abstract comparisons are mates of identity on pushforward, and both
   composition comparisons are mates of pushforward composition. The pseudofunctor
   associativity identities then cancel the source/target comparisons and the inverse
   component of e_b. This applies equally to empty overlaps, repeated charts,
   zero modules, k = j, and equivalent indices in a preorder. No limit or finiteness
   assumption is needed by this calculation. Independent LeanFinder, Loogle and grep
   searches using adjunction mates and composition coherence found component APIs
   (`leftAdjointCompIso_assoc`, `leftAdjointUniq_trans_app`, and
   `conjugateEquiv_pullbackComp_inv`), but no theorem closing the full chart calculation
   in a few minutes. Verdict: valid decomposition; one closed hole, one added hole.

4. Checked the top-level reduction: local fixed-model descent supplies compatible
   maps, Zariski full faithfulness glues them and detects the recovery equality, and
   only the final geometric transport remains split. Each proof import supplies
   used declarations or finite-presentation pullback instances; both new public
   imports supply types or constants in the new signatures. The only old proof
   dependency removed is `lem-pc-fp-module-map-descent-affine`; it remains transitive
   through local descent. The two old overlap definition nodes remain used directly
   and are retained in proof_deps. No module is claimed globally pruned. Read
   `dag/units/sk-thm-picard-semicon.json`: this item is not a realized unit statement
   or step, and neither the unit route nor its realized records change. Verdict: pass.

5. Checked both node records against the Lean, including the verbatim new signature,
   proof steps, dependency unions, provenance, source, searches, creation record,
   chapter and unit. Corrected the main node's dependency bookkeeping: its gluing
   step calls the closed Zariski theorem, whereas `lem-pc-fpqc-descent` records a
   different fpqc theorem. Recorded this elementary closed-library step explicitly
   and removed that spurious dependency. Restored both directly used overlap
   definition nodes to the final step and proof_deps. Verdict: pass after repair.

Second-reading changes: DAG dependency bookkeeping and this audit report only;
no Lean proof, definition, signature, import or hole was changed. Sources reread:
[Stacks 01ZR](https://stacks.math.columbia.edu/tag/01ZR) and
[Stacks 0096](https://stacks.math.columbia.edu/tag/0096).
