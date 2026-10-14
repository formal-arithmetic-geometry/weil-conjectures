## What changed

Proved `AlgebraicGeometry.Scheme.Modules.moduleCup_godement_fmap_models` with its entire
signature unchanged. All edits are in the item and its existing DAG node.

Constructed the cross-scheme Godement map explicitly using stalkPushforward, restriction
of scalars, the stalk-skyscraper adjunction, pushforwardSkyscraperIso, and pushforward's
product comparison. Proved its coordinate formula, unit and multiplication laws, and
compatibility with coefficient composition. Iterated it, proved insertion and collapse
compatibility, assembled the natural transformations, and proved their augmentation squares.

Used coordinate-characterized beta maps on both schemes. Reused the proved private
coordinate laws through a proof-only `import all Sheaf.Paper.ModuleCupGodementBetaExists`;
there is no change to that module. Existing recursive pairing and collapse theorems supply
the canonical pairings. A local proved assembly helper, adapted from the private
`pairingForModels` argument in ModuleCupGodementCoefficientModels, retains their component
formulas without importing the coefficient-model existence theorem. Proved the one-step
tensor square on common local representatives, its iterate induction, and the final
transport to the six models. Every private helper is proved.

Added proof-only imports for simplex generators, recursive pairings, canonical collapse,
and the coordinate beta laws. Coordinate existence and the product APIs are available
through those imports. Public
imports, public signatures, definitions used by targets, and other modules are unchanged.
Updated only proof, proof_deps and proof_origin in the item's DAG node.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Modules.moduleCup_godement_fmap_models`
(node `new-module-cup-godement-fmap-models`).

One hole closed, zero holes added. No `sorry` remains in the delivered module. No new
modules or nodes and no decomposition. The proof uses the existing coordinate existence
theorem and its existing dependencies; those imports have not been strengthened or altered.
The product constructions and all new cross-scheme maps are explicit, without choosing
arbitrary data from a holed existence theorem. Choices of pairings occur only inside the
existential theorem proof.

The proof checks empty products by extensionality and makes no nonempty-scheme or nonzero
coefficient assumption. Degree-zero iterate compatibility is exactly the original hχ;
the augmentation equations use the actual germ unit. Both cofaces and codegeneracies are
checked before invoking generation of the simplex category.

## No longer needed

No original direct import was removable: the two original public imports define the
statement's codegeneracy predicates and cosimplicial-complex identifications.

Removed the planned logical dependencies
`new-module-cup-godement-iterate-pairings-canonical-exists` and
`lem-sc-module-cup-godement-model-pairing-pairing` from the node's proof_deps. Their existential
pairing theorems are unnecessary: we use specified coordinate beta maps, recursive pairings
from those beta maps, and local model transport retaining the component formula. Their
modules still occur transitively through existing public imports; this delivery does not
claim to prune them globally. The canonical module's beta structure is still needed.

A temporary proof-only import of Sheaf.Paper.ModuleCupGodementCoefficientModels was removed;
no coefficient-model existence theorem or coefficient-model module is needed by the proof.
No other planned dependency is unused. The recursive theorem's node
`new-module-cup-godement-iterate-pairings-from-beta` replaces the canonical existence theorem
in the recorded route. No blueprint unit statement or step is bypassed.

The second reader removed three redundant proof-only imports added by the first worker:
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products`,
`Mathlib.CategoryTheory.Limits.Types.Products`, and
`Sheaf.Paper.ModuleCupGodementTensorCoordinatesExists`. Their declarations remain available
transitively; the coordinate-existence node remains a genuine logical dependency. Scratch
compilation and the axiom check both pass without these imports. This is direct-import
cleanup, not pruning a module from the targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The existing existential pairing-for-models theorem does not expose a degreewise formula
or a chosen coordinate beta, so it cannot by itself provide the cross-scheme tensor square.
Its already-proved transport argument can be used locally with specified recursive pairings;
this is now formalized. The DAG's coordinate construction plan is otherwise correct and
has been implemented without splitting off any new obligation.

## Second reading by M4

Independent second reader; read the complete 803-line submitted module, its repository
version, the changed node, its six proof dependencies, and
`dag/units/sk-prop-av-cube.json`. Read Stacks
[0FKR](https://stacks.math.columbia.edu/tag/0FKR) for the augmented Godement construction
and [0FKU](https://stacks.math.columbia.edu/tag/0FKU) for the cup-product context. The
cross-scheme coordinate argument is the explicit extension identified in the existing
docstring, not a claim that those sources state this Lean theorem verbatim.

1. **Interface: pass.** Extracted the existing theorem from its `theorem` keyword to
   `:= by` and compared it byte for byte: identical. The six models, both
   `MonoidalPreadditive` assumptions, the three coefficient maps and the sectionwise
   `hχ` are retained. The conclusion retains both pairing augmentation equations,
   all three cross-scheme augmentation squares, and the pairing square in every degree
   and on every open. Existing docstrings, public imports, and target definitions are
   unchanged. The new helpers are private; no change record or forced adaptation is needed.

2. **Proof and construction: pass.** The original and import-cleaned versions compile
   without errors or warnings. A scratch copy with
   `#print axioms AlgebraicGeometry.Scheme.Modules.moduleCup_godement_fmap_models`
   prints exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   The delivered source contains no `sorry` or forbidden axiom/implementation mechanism.
   Read every private definition: `stalk`, `proj`, `coord`, `lift`, `eval`, and `iterate`
   construct actual maps from stalk functoriality, scalar restriction, skyscraper
   evaluation, products, and recursion. In `coord`, the scalar tower is along the actual
   `f.stalkMap`; the `pushforwardSkyscraperIso` is used in the correct inverse direction.
   No definition chooses an arbitrary witness of an unproved existence statement.

3. **Split statements and edge cases: pass; none split off.** There are no new public
   statements, new nodes, or residual holes. Read the coordinate characterization and
   the three proved `coordinates_*` lemmas imported from `ModuleCupGodementBetaExists`:
   they apply to the particular maps chosen in this theorem. Germ representatives
   determine the stalk pairing, and pure tensor sections together with sheafification
   and product projections determine the tensor map. The existing recursive theorem
   fixes `p 0` and the recursion; it is not an unrelated existential pairing.
   Checked `iterate_insert` at zero against `lift_unit`, `iterate_collapse` at zero
   against `lift_multiply`, and `iterate_pairing` at zero against `hχ`. Successor
   indices use the preceding insertion/collapse. Empty schemes and opens missing the
   coordinate point are covered by product and `SkyscraperSections.ext`; zero modules
   require no extra assumption. The common-neighbourhood argument uses intersections,
   with no affineness or nonemptiness assumption.

4. **Route and imports: pass after cleanup.** Searched the upstream library for
   `Godement`/`godement` and this library for `godement_fmap`, `stalkPushforward`, and
   `pushforwardSkyscraperIso`. The upstream Čech Godement construction does not supply
   the module tensor square. A fresh LeanFinder query for a cross-scheme product of
   stalk skyscrapers returned scheme coproduct/projection results, not this theorem.
   The proof already uses the upstream stalk/skyscraper API and existing recursive
   pairings rather than reconstructing them. The two removed planned dependencies are
   both listed under `No longer needed`; they remain transitively imported, so no global
   pruning is claimed. The unit's existing `realized` entries are empty and unchanged;
   this proof replaces only the lower coordinate argument and bypasses no recorded
   unit statement or step. Scratch removal tests confirmed that simplex generation,
   pairings-from-beta, and canonical-collapse imports are needed. Removed the three
   redundant added imports listed above; compilation and the axiom check still pass.

5. **DAG correspondence: pass.** Compared the JSON objects: only `proof`, `proof_deps`,
   and `proof_origin` differ. `proof_deps` is exactly the union of the steps' `uses`.
   Step 1 is `stalk`/`coord`/`lift`; step 2 is projection formulas, unit and
   multiplication compatibility, insertion/collapse induction, `modelMap`, and its
   augmentation lemma. Step 3 uses coordinate existence and the proved coordinate
   laws, then `moduleCup_godement_iterate_pairings_from_beta`,
   `moduleCup_godement_iterate_pairings_collapse_of_canonical`, and the local
   `pairingForModels` retaining the component formula. Step 4 is `tensor_germs`,
   `lift_pairing`, `iterate_pairing`, and the final transport cancellation. All six
   recorded logical dependencies are used. No new-node fields require review.

Second-reading changes: removed three redundant proof-only imports and corrected the
import description and pruning accounting in this report; no proof body, existing
signature, definition, or DAG route needed repair. Net holes: one closed, zero added.
