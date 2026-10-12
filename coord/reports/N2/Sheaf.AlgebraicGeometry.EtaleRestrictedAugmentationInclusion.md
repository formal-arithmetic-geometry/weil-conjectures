## What changed

Proved `AlgebraicGeometry.Etale.etaleRestrictedAugmentation_inclusion` in
`Sheaf.AlgebraicGeometry.EtaleRestrictedAugmentationInclusion`. The signatures,
visibility, definitions, existing docstrings, and imports are unchanged. Added a
local `backward.isDefEq.respectTransparency false` option for the theorem's elaboration.

The proof follows the existing node's degreewise calculation. After chain-map
extensionality, use `T.aug_formula` and Mathlib's
`HomologicalComplex₂.ιTotal_map`. Evaluate the extended map in resolution degree
zero with `HomologicalComplex.extendMap_f`, and cancel the extension isomorphisms.
For `q ≤ n`, write `n` as the image of `(n - q).toNat` under `embeddingUpIntGE q`;
the truncation projection and inclusion are inverse components of the same
isomorphism. For `n < q`, both composites have a zero source. This applies to
negative q, the zero complex, and empty total diagonals without additional hypotheses.

Searches through leanfinder, loogle, msearch grep, and local rg found the generic
total-map naturality and extension formulas, but no pre-existing copy of this
restricted augmentation equation. No new lemma or node was needed. The existing
DAG proof, dependencies, and unit route already describe the implemented proof,
so no node update is necessary.

Validation: the item's module compiles cleanly through `lcompile.py`.

## Proved and sorry left

Closed the only original hole:
`AlgebraicGeometry.Etale.etaleRestrictedAugmentation_inclusion`
(node `lem-weil-pbc-etale-restricted-augmentation-inclusion`).

Holes closed: 1. Holes added: 0. No `sorry` remains in the delivered module,
and no intermediate theorem was split off. This is a proof, not a decomposition.

## No longer needed

None. The sole public import,
`Sheaf.AlgebraicGeometry.EtaleRestrictedTotalResolution`, is required for
`etaleRestrictedAugmentation` in the theorem's statement. All three planned
proof dependencies remain used: the termwise presentation's augmentation formula,
the explicit restricted total construction, and the restricted augmentation.
No nodes or modules were pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface fault was found. The DAG's proposed degreewise
argument is sufficient and is now implemented in Lean. No forced adaptations,
statement changes, or change records are needed.

## Second reading by N2

1. Interface preservation: compared the entire sandbox module with the repository
   using `diff -u`. The only differences are the theorem-local elaboration option
   and replacement of its `by sorry` by a proof. Both existing declaration
   signatures, the inclusion definition, visibility, imports and docstrings are
   byte for byte unchanged. The equation retains arbitrary scheme X, bounded-below
   K, presentation T and integer q, with exactly the node's two composites. Pass.
2. Proof validity: independently compiled the delivered file with `lcompile.py`
   (30.9 seconds, no warnings or errors). Compiled a scratch copy with explicit
   `#print axioms` for both `etaleRestrictedTotalInclusion` and
   `etaleRestrictedAugmentation_inclusion` (30.3 seconds). Both list only
   `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`. Read the complete
   proof: total-map naturality and `extendMap_f` reduce the degree-zero summand;
   the retained-degree branch cancels inverse component isomorphisms, and the
   omitted-degree branch uses the zero source. No sorry, prohibited declaration,
   hollow definition, or arbitrary choice from an unproved existence was added.
   Pass.
3. Split statements: there are no new declarations, new nodes or split-off
   statements, and no remaining hole in this module. In particular the original
   equation is proved directly rather than renamed as a new assumption. The
   retained-degree argument includes n = q and negative q because
   `(n - q).toNat` is used only after proving nonnegativity. The omitted-degree
   argument covers every n < q; a zero complex needs no extra hypothesis. Pass.
4. Route and pruning: read the imported explicit augmentation and component
   definitions and T.aug_formula, and searched both Lean roots for related
   augmentation/inclusion, truncation projection/inclusion and total-map results.
   Read Mathlib's `ιTotal_map` and `extendMap_f` and the upstream truncation
   component formulas. These are precisely the reusable generic ingredients
   already used; no shorter complete augmentation equation was found. The
   unconditional upstream truncation retraction cancels inclusion then projection,
   whereas this proof needs the opposite order only in retained degrees, so it
   does not remove this case split. The sole public import is necessary for the
   augmentation in the signature. All three old proof dependencies are used;
   `## No longer needed` is complete. Read `dag/units/sk-prop-h2.json`: this
   helper is not a realized unit statement or step, and no unit route or realized
   record is changed. Pass.
5. DAG agreement: read
   `dag/nodes/sec-curve-estimates/lem-weil-pbc-etale-restricted-augmentation-inclusion.json`
   together with the Lean file. Its degreewise proof, three proof dependencies,
   and proof_origin describe exactly this cancellation calculation derived from
   the explicit Stacks 015J/0133 augmented-total construction. Its Lean statement
   matches the unchanged theorem signature. No node amendment is necessary. Pass.

Second reading changed only this report: added the independent review and explicit
axiom evidence. No Lean proof repair was needed. Holes closed: 1; holes added: 0;
intermediate statements split off: 0; imports or modules pruned: none.
