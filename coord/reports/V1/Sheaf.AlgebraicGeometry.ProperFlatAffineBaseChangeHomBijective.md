## What changed

Repair of return X-cd2b4 (landing import-prune rejection): the mixed Leray theorem
writes both instance binders explicitly, with independent `w` and `wA`. The existing
`exists_schemeGlobalSectionsDirectImageIso` binds both localizations at `w`, so it
cannot instantiate this conclusion. This uses the return's explicit-binder exception.
Removed the duplicate private `AlgebraicGeometry.lerayCore` declaration and now reuse
that existing private generic theorem through a proof-only `import all` of
GlobalHomAdjunctionIso. The statement-visible ordinary public import remains.

Full-set landing checks also found copied private tensor helpers. Removed
`mixedPullbackTensorModelMap_isIso` and `mixedPullbackCounit_isIso`; the comparison
now reuses the existing `pullbackTensorModelMap_isIso` and `pullbackCounit_isIso`
through a proof-only `import all` of GlobalHomAdjunctionIso. Removed the direct
proof-only FlatResolution import, which only the copied helper needed.
No duplicate generic helper remains. No new declaration, node or hole was added in
this repair; the target signature and all existing visible interfaces are unchanged.
Updated the Leray node signature and both construction nodes' proof provenance and
dependencies. Previous second-reading sections predate this repair and were removed;
the independent second reader must review the repaired delivery.

Validation: `lcompile.py --all` compiled all seven modules without warnings after
replacing the helper copies with imports. The Leray and tensor construction modules
take about 17 and 16 seconds respectively. No heartbeat-limit override is needed.
The delivery dry run uses the current fetched `sheaf-dag` base and enables the
requested server compilation for the modules that have no sandbox dependencies.

Replaced the target sorry by scalar-extension cancellation followed by degree n-m
cohomology and the natural shifted-Hom identification. The target signature is unchanged.
Constructed independent-universe evaluation-mate/Leray comparisons and the derived
extension/restriction adjunction in FlatAffineGlobalHomComparison. Their construction
proofs compile; no definition contains sorry or selects arbitrary existence data.

The model counit is existential and does not fix the raw model tensorator. The new
proved exists_mixedHomTensorPullbackIso instead packages the canonical comparison
normalized to SingleComplexBaseChange.counit, proves its invertibility using K-flat
representatives, and selects only this normalized isomorphism. The canonical comparison
uses exists_canonical_from_model to conjugate the model by the universal counit
comparison. The Leray comparison is fixed by its derived-unit equation. The extension functor is
chosen from a proved adjunction existence theorem, hence determined up to the adjunction
isomorphism used in the comparison.

## Proved and sorry left

Closed AlgebraicGeometry.proper_flat_rightAdjoint_affine_baseChange_hom_bijective.
This is a decomposition, not a complete mathematical proof: one upper hole closed,
three strictly lower obligations added.

Also proved AlgebraicGeometry.exists_mixedHomTensorPullbackIso using the existing private
K-flat invertibility helpers (the copied declarations were removed). Also proved
AlgebraicGeometry.exists_mixedGlobalSectionsDirectImageIso
(lem-sc-mixed-global-sections-direct-image-iso) and
AlgebraicGeometry.mixedGlobalExtension_adjunction
(lem-sc-mixed-global-extension-adjunction). These construction proofs were already
closed in the first worker's repair; the second reading adds their module/node records
and adds no holes.

Remaining new sorries:
- AlgebraicGeometry.mixedAffineGlobalHomBaseChangeMap_isIso
  (lem-sc-flat-affine-global-hom-comparison): the first comparison is invertible.
- AlgebraicGeometry.properFlatGlobalHomComposite_isIso
  (lem-sc-proper-flat-global-hom-composite-isIso): the composite comparison is invertible,
  before cancelling its first factor.
- AlgebraicGeometry.restrictedGlobalHom_shiftedHom_equiv
  (lem-sc-restricted-global-hom-shifted-equiv): the natural shifted-Hom identification,
  with no properness, flatness, perfectness, or quasi-coherence hypotheses.

No sorry remains in the item. The combining Lean proof cancels alpha, maps the resulting
isomorphism through cohomology, and conjugates the concrete bijection by additive
equivalences using their stated naturality equation.

## No longer needed

Removed duplicate private declarations `AlgebraicGeometry.lerayCore`,
`AlgebraicGeometry.mixedPullbackTensorModelMap_isIso`, and
`AlgebraicGeometry.mixedPullbackCounit_isIso`. Removed the direct FlatResolution import
from MixedHomTensorPullbackIso. These existing obligations are reused through
GlobalHomAdjunctionIso; no module is claimed pruned from the target closure.

The repair removes direct selection of def-pc-derived-pullback-monoidal-model from
the flat affine comparison proof; that node remains transitively needed by canonical
comparison model transport. The fresh second reading removes the redundant direct
AffineGlobalHomBaseChangeMap and LeftDerivedFunctor.Defs imports from
FlatAffineGlobalHomComparison, imports PerfectComplex for its statement, and makes
the proof-only FlatResolution import plain rather than public.

Removed the item's direct proof imports of BaseChangeRHomPerfect,
AffineMorphismHomOutOfPerfect, FlatPrecomposePus, GlobalHomAdjunctionIso, and
ProperSupportPerfectDirectImage. Their mathematical obligations remain below the new
comparison nodes and their modules remain transitively imported. No original mathematical
node or module is claimed pruned from the targets' import closure. The unit route is retained.

## Where the brief, the DAG or earlier work was wrong

The earlier report missed three duplicate private helpers and failed to expose
section binders to the statement-duplicate checker. The mixed public theorem is a
real universe generalization, but its implicit section variables made its statement
text identical to the shared-universe theorem. Both reported landing findings are
repaired, and the Lean record now includes the explicit binders.

Repair of H5/E4: the earlier raw monoidal-model choice was insufficiently normalized.
Simultaneously changing the model counit and tensorator signs preserves the model
equations. Its tensorator therefore need not equal the shared-counit canonical
comparison. The replacement explicitly uses canonical comparison model transport
and K-flat invertibility, preserving independent localization universes.

The original dependencies do not directly compose at their Lean interfaces:
AffineMorphismHomOutOfPerfect uses spectra, and GlobalHomAdjunctionIso and
FlatPrecomposePus require module derived-category morphisms in the same universe as the
sheaf localization. The target has only the sheaf instance, at an arbitrary universe.
The new comparisons keep module and sheaf localization universes independent; the item
uses standard module localizations without changing its signature. The source also requires
transport from arbitrary affine schemes to spectra and the full canonical-map compatibility.

The local literature/stacks-project directory is absent in this checkout. Read the sources
at https://stacks.math.columbia.edu/tag/0AA7, https://stacks.math.columbia.edu/tag/0AA8,
and https://stacks.math.columbia.edu/tag/08JA. The blueprint search found no exact duplicate
for global Hom base change or shifted Hom. The ancestor utility does not follow the
module-valued created.item of this stage-3 node; the existing blueprint.from.node is used.
LeanSearch was unavailable (HTTP 500), recorded as unavailable. LeanFinder, Loogle and
logged grep searches were run; no exact Mathlib match was found.

Edge checks: zero M and empty schemes yield zero comparisons; arbitrary nonflat g is
allowed because scalar extension is derived. Arbitrary unbounded K and all negative or
positive shifts remain allowed. No statement or definition in an existing module changed.

## New nodes

lem-sc-mixed-global-sections-direct-image-iso: the already-proved unit-normalized
Leray isomorphism, in MixedGlobalSectionsDirectImageIso. Its acyclicity input is the
existing direct-image/global-sections K-injective theorem; no new hole.

lem-sc-mixed-global-extension-adjunction: the already-proved derived scalar-extension
adjunction, in MixedGlobalExtension. It uses mixed tensor K-flat quasi-isomorphism
invariance and the existing derived-adjunction interface; no new hole.

lem-sc-mixed-hom-tensor-pullback-iso: proved canonical tensor isomorphism using the
shared derived counit; supports the flat affine comparison. Its model-transport
dependency remains the existing named lower obligation, not a new hole.

lem-sc-flat-affine-global-hom-comparison: the first, general flat affine comparison,
needed for arbitrary quasi-coherent N, not only a(K).

lem-sc-proper-flat-global-hom-composite-isIso: the proper direct-image/perfect RHom
comparison and mate compatibility, asserting invertibility before cancellation.

lem-sc-restricted-global-hom-shifted-equiv: a general natural shifted-Hom/cohomology
identification, independent of the geometric base-change hypotheses.

Change record: coord/changes/proper-flat-hom-proof-elaboration.md records the static
checker's classification of local elaboration options; no exported interface changes.

## Second reading by V1

1. **Interfaces.** Compared all seven delivered modules with the repository: the
   item is the only existing module; the other six are new. The item's declaration
   signature is byte-for-byte unchanged, with no declarations added or removed and
   no statement-visible import changed. The two elaboration options are covered by
   the existing change record. No target statement or existing definition changed.
   Verdict: passes.

2. **Compilation and axioms.** Independently ran `lcompile.py --all` on the seven
   modules, then compiled scratch copies with `#print axioms` for every delivered
   theorem and definition. All compile without warnings. The extension adjunction
   and normalized Leray construction use only `propext`, `Classical.choice`, and
   `Quot.sound`. The tensor construction, comparisons, and item also use `sorryAx`
   from the recorded open dependencies. Exactly the three listed public theorems
   contain `sorry`; no definition contains a hole and no forbidden declaration or
   attribute occurs. The Leray unit equation and canonical tensor coordinate
   equation determine the chosen comparisons, while the scalar-extension functor
   is selected from a proved derived-adjunction construction. These choices are
   not arbitrary data from unproved mere existence. Verdict: passes as a
   decomposition, not as an axiom-free proof of the item.

3. **New statements.** Read Stacks Tags [0AA7](https://stacks.math.columbia.edu/tag/0AA7),
   [0AA8](https://stacks.math.columbia.edu/tag/0AA8), and
   [08JA](https://stacks.math.columbia.edu/tag/08JA), and the existing declarations
   `affineMorphism_hom_out_of_perfect`, `properSupport_perfect_directImage`,
   `flat_precompose_pus`, and `rhom_global_sections`. Flatness supplies Tor
   independence in 0AA7; perfect M and quasi-coherent N are precisely its case (1).
   In the composite lemma, properness, flatness, and finite presentation give
   perfect Rf_*M, and the assumed base-change inverse is used at M. The compatibility
   obligation is retained, rather than replacing the canonical map by an arbitrary
   isomorphism. The shifted-Hom equivalence requires no geometric hypotheses:
   K-flat/K-injective computation and exact scalar restriction allow arbitrary
   unbounded complexes and both positive and negative shifts. Tested the argument
   on zero objects, empty schemes, identity squares, and nonflat g; no missing
   hypothesis emerged. The three holes are different pieces of the source
   argument; none merely renames the item's bijection. Each has a docstring proof
   and node. Independent LeanFinder searches using “Tor independent cartesian
   square” and “global sections of derived internal Hom cohomology”, Loogle's
   `"CohomologyClass", "homAddEquiv"`, and logged grep found only raw Hom-complex
   infrastructure. Repository and upstream searches found no exact closed
   replacement. The shared-universe public comparisons cannot directly instantiate
   the independent-universe statements. Verdict: passes; none of the three holes
   can be closed by a short application of the results found.

4. **Reduction and pruning.** Read the actual cancellation proof: alpha and
   alpha followed by h are isomorphisms; left cancellation makes h invertible;
   degree n-m cohomology preserves it; the stated naturality equation conjugates
   its underlying bijection to postcomposition with c[n]. Its direction and both
   shifts agree with the item. The five old direct proof dependencies are
   `lem-pc-affine-morphism-hom-out-of-perfect`,
   `lem-pc-proper-support-perfect-direct-image`, `lem-pc-global-hom-adjunction`,
   `lem-pc-base-change-rhom-perfect`, and `lem-sc-flat-precompose-pus`.
   All five leave the item's direct `proof_deps` and are retained below the new
   comparison nodes; none is claimed removed from the target import closure.
   The duplicate private helpers have been removed and their existing versions
   are reused with proof-only `import all`. Public imports in the new modules
   supply their signatures or public definition bodies; proof dependencies are
   plain imports. Read `dag/units/sk-thm-picard-duality.json`: its realized fields
   are unchanged, and this below-unit auxiliary proof keeps the original Hom
   comparison route. Verdict: passes; no module is pruned from the closure.

5. **DAG agreement.** Compared the item's node with the repository: only `proof`,
   `proof_deps`, and `proof_origin` change. Its three steps match the two IsIso
   applications, cancellation, and shifted-Hom transport in Lean. Read all six new
   nodes, including their Lean records, sources, searches, creation and blueprint
   records. The extension node records mixed-tensor derivability; Leray records
   the direct-image/global-sections K-injective input; tensor records canonical
   model transport and the reused K-flat helpers. The three open nodes record
   the affine comparison, proper-side comparison/compatibility, and shifted Hom
   arguments respectively. Verdict: passes.

Changes in this reading: added this independent review, recorded additional
searches, and explicitly enumerated the old direct dependency nodes. No Lean
proof, statement, definition, import, node, or change record needed further repair.
One original hole is closed by reduction and three lower holes remain newly added;
the net hole count is -2, not a claim of completed mathematical proof.
