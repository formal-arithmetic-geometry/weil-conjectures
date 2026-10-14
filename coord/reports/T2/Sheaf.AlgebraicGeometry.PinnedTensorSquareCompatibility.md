## What changed
Repaired D2 by proving the component theorem using extensionality against the scalar-extended total-tensor summand injections. The two routes are calculated separately on a summand and compared through an explicit common map. The right calculation uses the scalar-extension tensorator and tensor-map naturality. The deferred left calculation has a complete proof plan using the pinned injection equations, pullback-stalk naturality, the hypothesis on the pullback tensor comparison, and the module tensor/stalk square. The component theorem combines the two explicit summand normal forms and then applies scalar-extension coproduct extensionality. The module square is proved by scalar and pure-tensor induction followed by the germ formulas.

Repaired C4 by delivering the existing compatibility node with its component-extensionality proof and component dependency; its statement fields are unchanged. Repaired B2 by making the component node's statement self-contained: it introduces the schemes, square, complexes, chain map, comparison hypothesis, stalk functors, scalar extension and specified coordinates before stating the component equation for every integer degree.

## Proved and sorry left
Closed the original hole `AlgebraicGeometry.pinned_tensor_pullback_stalk_compatibility` (1 of 1) and the returned hole `AlgebraicGeometry.pinned_tensor_pullback_stalk_component`.

Proved new declarations `AlgebraicGeometry.pinned_tensor_square_right_summand` and `AlgebraicGeometry.Scheme.Modules.module_pinned_tensor_stalk_square`.

The sole remaining delivered `sorry` is `AlgebraicGeometry.pinned_tensor_square_left_summand` (node `lem-pc-pinned-tensor-square-left-summand`). This is a decomposition: one route on one specified tensor summand is identified with an explicit map through the scalar-extension tensorator and the two module pullback-stalk components. It does not compare the original two composites or assert their equality at every degree. The right route is already calculated, and the component proof supplies the coproduct-extensionality argument. One lower hole was added; no hole remains in the item or component theorem, and there is no `sorry` in a definition.

The full left proof attempt established the constituent equations but did not finish elaborating the final composition within the fixed compile limit. Diagnostics showed repeated reduction of chosen colimit objects. The attempt is saved locally in `left-proof-attempt.txt` for the next reader; it is not a delivered Lean module. Validation: `lcompile.py --all` compiled all six delivered modules without warnings. The required `deliver3.py --no-push` dry run gates readiness and repeats the delivery checks.

## No longer needed
No original module or node has been pruned. The item's old direct `proof_deps`
`def-pc-derived-pullback-tensor-comparison`,
`def-pc-single-complex-base-change-stalk-condition`,
`lem-pc-tensor-pullback-stalk-square`, and `lem-weil-pbc-module-pullback-tensor`
are replaced at the top node by `lem-pc-pinned-tensor-square-component`.
They remain statement dependencies or dependencies of the summand argument;
their modules are retained, not globally pruned. The deferred left summand retains plain imports of every recorded proof-dependency module, including ModulePinnedTensorStalkSquare, as its proof plan requires. Unused private proof-attempt helpers were removed. The proved module square is in the target's Lean import closure as a planned dependency of the remaining left-summand theorem; compatibility still depends on that named sorry. The discarded experimental generator module is not delivered.

## Where the brief, the DAG or earlier work was wrong
The returned component theorem was equivalent to the item by component extensionality, so leaving its entire proof deferred did not constitute a reduction. This repair calculates the routes on individual summands and supplies the coproduct-extensionality argument. The first repair dry run also required the LeanSearch search kind in the two new summand nodes and explicit filenames for all four change records. The LeanSearch query was attempted and the service returned Internal Server Error; that unavailability is recorded without a search verdict, alongside the completed other searches. The change records are named below. The old second-reading point 3 incorrectly described the degree projection as strictly smaller; that claim is withdrawn below.

## New nodes

- `lem-pc-pinned-tensor-square-component`: the component equality, now proved from the summand calculations.
- `lem-pc-pinned-tensor-square-left-summand`: normalization of the left route on one summand with one remaining hole and a complete proof plan using the module square and a categorical diagram chase.
- `lem-pc-pinned-tensor-square-right-summand`: proved normalization of the right route on one summand.
- `lem-pc-module-pinned-tensor-stalk-square`: proved module tensor/stalk square used in the left calculation.

## Earlier second reading (a previous round; superseded)

The following records the prior reading and the requested correction; this repair still requires a fresh independent reading.

1. The original compatibility theorem's signature is unchanged. The component theorem's delivered signature is also unchanged by the repair.
2. The prior compilation and sole-component-sorry claim are superseded by the repair's final compilation and hole inventory above.
3. Correction requested by D2: projecting the entire item to every degree was equivalent to the item and was not a strictly smaller deferred statement. The repaired component proof instead uses scalar-extension coproduct extensionality and compares explicit left and right summand normal forms. The right normalization and the module tensor/stalk generator calculation are proved. Only the left route on one tensor summand is deferred, as explicitly inventoried above; it is a single part of the generator argument, rather than the original component equality under a different name.
4. The compatibility theorem imports the component privately, and the component imports the two summand calculations privately. New module dependencies follow the actual proof and are recorded in their nodes.
5. The route continues to use the pinned stalk tensor construction and degreewise tensor generators, preserving the unit's route.

The prior local instance-name adjustments remain recorded in:

- `coord/changes/pinnedTensorSquareCompatibilityT2Instance1.md`
- `coord/changes/pinnedTensorSquareCompatibilityT2Instance2.md`
- `coord/changes/pinnedTensorSquareCompatibilityT2Instance3.md`
- `coord/changes/pinnedTensorSquareCompatibilityT2Instance4.md`


## Earlier second reading (a previous round; superseded)

Independent second reading of the six sandbox modules, their five node records,
the repository compatibility module and node, and
`dag/units/sk-thm-picard-semicon.json`.

1. **Interfaces: pass.** Compared each delivered module with its repository path.
   `PinnedStalkTensor.lean` is byte-identical; the component, two summand modules,
   and module-square module are new. The compatibility theorem's complete signature
   is byte-identical, including the derived-category instance, cartesian square,
   arbitrary complexes, chain map, specified comparison and every injection equation
   in hχ, actual stalk scalar map, and the fixed σ and ρ. The only existing
   declaration changes besides its proof are the four recorded local instance
   renamings; their types and bodies are identical. No definition, target statement,
   or hypothesis was altered. Expanded the four change records' Old/New sections
   from name fragments to complete declarations.

2. **Proof and axioms: pass as a partial delivery.** Fresh `lcompile.py --all`
   compiled all six files without errors or warnings (12.0–36.0 seconds per file).
   A separate scratch module imported the delivered modules and ran `#print axioms`
   on compatibility, component, left summand, right summand, module square, and
   `exists_pinned_stalk_tensor`. The last three have only propext, Classical.choice,
   and Quot.sound. The first three additionally have sorryAx, as expected from the
   single left-summand hole. The scratch source was removed before delivery.
   A source scan finds exactly `pinned_tensor_square_left_summand := by sorry`
   and no forbidden declarations or attributes. No data definition is added.
   The chosen comparisons are existing specified comparisons: their injection or
   germ formulas determine the maps on generating elements; the tensorMap has
   specified restrictions on both tensor factors. There is no arbitrary witness
   newly chosen from an unproved mere-existence theorem.

3. **Split and mathematical reading: pass.** Read Stacks
   [0DJA(1)](https://stacks.math.columbia.edu/tag/0DJA),
   [0BYJ](https://stacks.math.columbia.edu/tag/0BYJ),
   [01CD](https://stacks.math.columbia.edu/tag/01CD),
   [01CB](https://stacks.math.columbia.edu/tag/01CB), and
   [0098](https://stacks.math.columbia.edu/tag/0098).
   The chain-coordinate equation is the auxiliary generator calculation for the
   cited derived tensor argument, rather than the entire derived assertion of
   0DJA. Its additional χ and hχ specify the actual chain representative.
   For the only deferred theorem, source pinning inverts the source injection
   formula; pullback-stalk naturality moves that injection through κ; hχ supplies
   the pullback tensor comparison; bifunctor-map naturality moves a to degree q;
   target tensor-stalk naturality and target pinning give the final injection.
   The proved module square supplies exactly the intervening scalar tensorator
   equation after transporting its ring map by the restriction equation in
   exists_tensorMap. All six squares have the required objects and orientations.
   The explicit right-hand normal form is independently proved without χ or hχ.
   Thus the deferred result identifies one route on one summand; it does not
   assert equality of the original two composites. The component proof performs
   the remaining transitivity and scalar-extension coproduct extensionality.
   The module square's proof represents both germs on the intersection of their
   neighborhoods, applies the three recorded generator formulas, then uses scalar
   extension and tensor induction. It matches the intermediate computation in
   TensorPullbackTensorIsIso, whose public conclusion is only IsIso, not this
   equality. Fresh leanfinder, loogle and grep queries and local source searches
   found constituent APIs but no reusable square theorem; added the relevant
   fresh search records to the module-square and deferred-summand nodes.
   Checked zero factors (all summand maps zero), zero stalk rings (zero modules),
   identity pullback (the ordinary scalar tensorator), and complexes concentrated
   in single arbitrary degrees (the module square with no differential sign).
   Infinite total sums introduce no finiteness assumption; the argument is on a
   specified summand and the component proof uses coproduct extensionality.
   The saved left proof attempt was read, but its unresolved elaboration chase
   does not supply a short verified replacement. The hole remains explicitly named.

4. **Route and pruning: pass.** The top proof uses hom_ext, the component proof
   uses mapBifunctor.hom_ext_of_map, and the right calculation uses the existing
   total-comparison injection and whiskering formulas, then whisker_exchange.
   All proof-only imports of the new component/summand results are plain imports.
   The public imports provide objects, comparisons, tensor structures or instances
   appearing in the signatures. No original import is removed. Completed the
   No longer needed inventory with all four old direct proof dependencies and
   explained why their modules remain needed below or in signatures.
   The unit's realized.statement and its sole realized.steps entry are empty;
   this delivery changes neither the unit nor its semicontinuity/base-change route.
   The generator reduction stays below that level and retains pinned coordinates.

5. **DAG: pass.** The compatibility node records the actual component-extensionality
   proof and its component dependency; the component records the two summand
   dependencies and their common explicit normal form. The right node follows its
   proved comparison/whiskering calculation. The module-square node follows the
   germ induction proof and its three canonical comparison dependencies. The left
   node records the deferred six-square argument and the module-square dependency;
   these are planned dependencies of the named sorry, not a claim that the current
   Lean body already applies them. Each new node has its self-contained statement,
   source, full proof plan, search records, creation and blueprint provenance,
   chapter/unit and Lean record. No pre-existing statement field was changed.

Second-reading changes: completed the direct-dependency inventory, expanded all
four instance change records to full declarations, and recorded fresh alternative
searches. No Lean proof or signature needed repair. Against the repository base,
one original hole is closed and one new lower hole is added: a decomposition with
net zero closure-hole reduction, not a fully axiom-free proof of compatibility.
The returned component hole is also closed in this repair; it was not a second
original repository hole. No module is pruned. Final dry run and delivery use
`deliver3.py`, including its per-declaration axiom probe and preflight checks.

The instance-name adaptations are recorded in
`coord/changes/pinnedTensorSquareCompatibilityT2Instance1.md`,
`coord/changes/pinnedTensorSquareCompatibilityT2Instance2.md`,
`coord/changes/pinnedTensorSquareCompatibilityT2Instance3.md`, and
`coord/changes/pinnedTensorSquareCompatibilityT2Instance4.md`.

## Second reading by T2

1. Interfaces: compared the compatibility module with the repository byte for byte
   apart from its proof, private imports, and the four local instance names documented
   above; all delivered new declarations have the signatures recorded in their nodes.
   Verdict: pass.
2. Proof and axioms: compiled all six sandbox modules with `lcompile.py`; source scan
   found only the named left-summand `sorry`, with no forbidden declarations or hollow
   definitions. The proved declarations use only permitted axioms, while the dependent
   compatibility and component declarations inherit the named `sorryAx`. Verdict: pass.
3. Split statements: checked the component, left/right summand, and module-square
   statements against their node records and edge cases (zero modules, identity maps,
   single degrees, and arbitrary sums). The left summand is a strict one-summand
   reduction and its deferred proof is documented. Verdict: pass.
4. Route and pruning: the component proof uses summand extensionality, the compatibility
   proof uses degree extensionality, and pinned coordinates remain on the unit route.
   Imports retained are used by signatures or proof dependencies; no unjustified prune
   was made. Verdict: pass.
5. DAG: proof, proof dependencies, origins, Lean records, search records, and change
   records agree with the delivered files; the four instance adaptations are explicitly
   named. Verdict: pass.

Changed only the report inventory and second-reading record after the prior dry run;
no Lean source or node statement was altered.
