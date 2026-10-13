## What changed

Replaced the sorry in `determinant_wedgeMorphism_local_data_at` by a proof through an
explicit pre-quotient wedge and its factorization. The existing signature is unchanged.
Added three proof-only imports and three new modules with matching nodes:
`ExteriorSheafMapExists`, `ExteriorSheafWedgeMapExists`, and `DeterminantWedgeQuotientFactor`.
The first constructs a sectionwise exterior morphism, verifies naturality on pure wedges,
and sheafifies it; its proof is complete. The original proof constructs q as identity tensor
this map, proves q's value formula, obtains the factorization, and evaluates it on the supplied
lift tuple. No data definition is introduced or chosen from an unproved existence theorem.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.Scheme.Modules.determinant_wedgeMorphism_local_data_at`
(node `new-local-wedge-at`). This is a decomposition, not a sorry-free determinant theorem:
two strictly smaller holes were added, and the net hole change is +1.

The new theorem `AlgebraicGeometry.Scheme.Modules.exteriorSheaf_map_exists`
(node `lem-sc-exterior-sheaf-map-exists`) is proved with no sorry.

Every sorry left in this delivery:

- `AlgebraicGeometry.Scheme.Modules.exteriorSheaf_wedgeMap_exists`
  (`lem-sc-exterior-sheaf-wedge-map`): canonical wedge before quotienting, for arbitrary f,
  with no short exactness or local-freeness assumptions.
- `AlgebraicGeometry.Scheme.Modules.determinant_wedge_quotient_factor`
  (`lem-sc-determinant-wedge-quotient-factor`): factorization of two already supplied maps,
  with no construction or final value formula in the conclusion.

No sorry remains in the item's module. All choices in its proof are existential elimination
inside a proposition, not data definitions. Edge cases checked mathematically: empty scheme
and empty open; either wedge degree zero; zero ring; arbitrary characteristic; quotient not
locally free. Alternation, not division or skew-symmetry alone, gives the repeated-factor zero.

## No longer needed

None. Every original public import is needed for the unchanged statement. Each new proof
import is used. The original node listed no proof dependencies to prune; its empty dependency
list is replaced by the three actual construction and descent nodes. No other node or module
is asserted globally unreachable. The finite-free exterior basis theorem remains needed
inside the quotient factorization.

## Where the brief, the DAG or earlier work was wrong

The item's node had one non-elementary fixed-open construction step with no dependencies.
The ancestor `lem-sc-determinant-wedge-morphism` supplies a detailed preserved proof, including
lift independence and the universal properties. These can be stated in Lean: the previous
attempt's assertion that no reduction could be stated was incorrect. The reduction here is
not a renamed copy: its canonical wedge map is defined before quotienting and independently
of exactness, and its factorization theorem takes both maps as input and concludes only a
composition equality. The item's proof constructs the quotient map and derives the original
value formula in Lean.

The referenced literature files are absent from this machine's literature directory. The
source text preserved in the ancestor DAG nodes and the Mathlib source were read; details in
the new nodes are marked as agent-written. The unit record's realized lists are empty; no
unit statement or prescribed step is bypassed or changed. Searches of the imported blueprint
for exterior, wedge and quotient found no duplicate sheaf-level construction. LeanSearch
returned Internal Server Error; the unavailable result is recorded accurately. LeanFinder,
Loogle and source grep found the ordinary-module universal properties used in the proved map,
but no matching sheaf-level determinant descent theorem.

## New nodes

`lem-sc-exterior-sheaf-map-exists`: the induced exterior morphism with its formula, proved by
an explicit natural presheaf map and sheafification. Module `ExteriorSheafMapExists`.

`lem-sc-exterior-sheaf-wedge-map`: wedge the image of the first block with the second block
before quotient descent. Its hypotheses require only an arbitrary sheaf morphism and the
sum of the degrees. Module `ExteriorSheafWedgeMapExists`.

`lem-sc-determinant-wedge-quotient-factor`: factor the supplied pre-quotient wedge through the
supplied quotient map using exactness and repeated-factor vanishing after trivializing the
kernel sheaf. Module `DeterminantWedgeQuotientFactor`.

No change records: no existing definition, signature, visibility or dependent module changed.

## Second reading by H2

1. Compared the delivered local module with the repository version. The theorem signature and all
   existing declarations are unchanged byte for byte; only proof-only imports, a local elaboration
   option, and the proof body were added. The three added declarations are in separate modules.
2. Compiled all four delivered modules with `lcompile.py --all`; compilation succeeds. The only
   remaining `sorry`s are the two named split theorems below, and no prohibited declaration or
   definition data is present. The original target therefore depends on `sorryAx` only through
   these explicitly split nodes.
3. Checked the three new statements against their hypotheses and edge cases (zero degrees, empty
   opens, and arbitrary characteristic). `exteriorSheaf_map_exists` is proved explicitly; the two
   remaining statements are strictly smaller factorization and wedge-construction obligations,
   each with a source, proof description, and matching DAG node. No duplicate library theorem was
   found by source search.
4. The local proof follows the node route: induced exterior map, pre-quotient wedge, quotient
   factorization, then evaluation on the supplied lift tuple. The unit record has no realized steps,
   so no prescribed unit route is bypassed. The proof dependencies and node records match the imports
   and declarations used.
5. Imports are minimal for the public signatures and proof. No old proof dependency or module can
   be pruned from this delivery.

Changed during second reading: appended this review record only; no Lean source or DAG repair was
needed.
