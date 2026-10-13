## What changed

Closed `CategoryTheory.normalizedRingHomExtension_exists` by constructing its degree maps
with `ringHomExtension_degrees_exists`, choosing them degreewise, and filling the chain-map
commutation field using `ringHomExtension_differential`. The pure-tensor clause follows
from the degree maps' normalization.

`RingHomExtensionDegrees` fully proves the degree-map existence step: an ordinary
Tensor-Hom comparison is transported to internal Homs on the unique-object site;
scalar extension of the source projections has its required pure-tensor formula by
naturality of the sheafification unit; the specified target limiting fan assembles the
coordinates. No finite-projective, boundedness, flatness or infinite-product-preservation
hypothesis is added. The internal-Hom map is constructed directly from linear equivalences. No duplicate
transport theorem or invertibility characterization is declared: its import would
create a cycle through `PerfectRHomBaseChangeMap` and this item.

The six shared definitions move unchanged to `RingHomExtensionDefs`, publicly re-exported
by the item. Names, signatures, universes, bodies, visibility and declaration docstrings
are unchanged. New proof dependencies are ordinary private imports of the item.
The change record is `coord/changes/ring-hom-extension-definitions-split.md`.
All four delivered modules compile locally; the supporting modules were compiled in
import order, and the final chain-map assembly compiled without warnings. All Lean
lines meet the 100-column limit.

## Proved and sorry left

Closed: `CategoryTheory.normalizedRingHomExtension_exists`
(node `lem-pc-normalized-ring-hom-extension`).

Fully proved: `CategoryTheory.ringHomExtension_degrees_exists`
(node `lem-pc-ring-hom-extension-degrees`), with no direct sorry.

Added one remaining sorry: `CategoryTheory.ringHomExtension_differential`
(node `lem-pc-ring-hom-extension-differential`). Its proof is exactly `:= by sorry`.
It asserts only differential compatibility for already supplied normalized degree maps,
not existence or the original theorem under a new name. This is a decomposition of one
upper hole into one strictly smaller hole, with a fully proved degree construction,
not a net reduction in the number of holes. The item's module contains no direct sorry.

## No longer needed

The direct imports of `HomComplex`, `TensorProduct`, and `KFlatTensorQuasiIso` move
to `RingHomExtensionDefs`; this is relocation, not removal from the import closure.
The old `proof_deps` nodes `def-pur-hom-complex`, `def-pur-sheaf-hom`, and
`def-pur-sheaf-tensor-product` remain used through the degree and differential nodes.
None of the original mathematical dependencies is pruned: `HomComplex`,
`TensorProduct`, and `KFlatTensorQuasiIso` remain public imports of the shared definitions
module, and are still reachable from the item. `KFlatTensorQuasiIso` supplies the actual
one-point ring sheaf constant, so removing it would change the public definitions.

No infinite-product preservation theorem, finite-support product comparison, boundedness,
finite-projective Hom theorem, K-flatness theorem or derived extension theorem is used by
this proof. The existing `RingHomExtensionTransport` and `RingExtensionInternalHomExt`
modules are not imported here because of their dependency on `PerfectRHomBaseChangeMap`.
The degree construction uses direct tensor-Hom conjugation, without the unused
invertibility characterization. The six duplicate helper theorems flagged on return
are removed: `point_eq`, `slice_eq`, `pointExtensionEquiv_tmul`,
`pointLift_isIso_iff`, `ringHomComplex_isLimit`, and `ringHomExtension_transport`.
Singleton elimination and the existing `homComplex_exists` witness are used inline;
the pure-tensor transport equality is definitional. No library module is pruned.
The original node's two construction/verification steps are retained as separate nodes.

## Where the brief, the DAG or earlier work was wrong

Repair of return X-53a9b: the earlier delivery redeclared six private theorem
statements already present in the library. All six declarations have been deleted,
rather than renamed. Importing the existing transport theorem is impossible because
its public import of `PerfectRHomBaseChangeMap` reaches this item. The replacement
constructs only the normalized map, a strictly smaller result than transport plus
invertibility; the unneeded invertibility argument and its helper are deleted.
The limiting fan is obtained directly from `homComplex_exists`.

No mathematical statement error was found. The DAG marked the entire construction and
chain verification elementary, but neither was supplied by an independent Lean theorem.
The construction is now proved; the chain verification is explicitly isolated with its
source and complete natural-language proof. The bottom-topology site has no sheafification
obstruction, and the ordinary tensor-Hom map exists even for zero rings and zero modules.
All degree maps are constructed, not chosen from a bare unproved existence statement.

The library transport lemma cannot be imported into this item: it publicly imports
`PerfectRHomBaseChangeMap`, which imports this item. No forced downstream adaptations are
needed for the unchanged relocation and public re-export of definitions. The unit record
has empty realization lists; the same two parent-node steps and unit are retained.

## New nodes

`def-pc-ring-hom-extension-shared-definitions` records the unchanged shared definitions
in `Sheaf.Algebra.Homology.RingHomExtensionDefs`. It contains no sorry.

`lem-pc-ring-hom-extension-degrees` records the fully proved degree-map construction in
`Sheaf.Algebra.Homology.RingHomExtensionDegrees`.

`lem-pc-ring-hom-extension-differential` records the strictly smaller remaining chain
verification in `Sheaf.Algebra.Homology.RingHomExtensionDifferential`; its named theorem
has the only new sorry. Every new node remains in the parent's chapter and unit.


## Second reading by Q3

1. PASS: compared the item with the repository by diff and checked the target
   theorem signature byte for byte. Each of the six relocated declaration texts,
   including its body, is unchanged. Their public re-export preserves existing
   users; the relocation and elaboration options have the declared change record.
   No target statement, hypothesis, conclusion, universe or definition was altered.
2. PASS: compiled all four modules through lcompile.py in import order, without
   warnings. A scratch copy printed axioms for all six shared definitions, both
   intermediate theorems and the item. The definitions and degree construction use
   only propext, Classical.choice and Quot.sound. Only the differential theorem and
   the item depending on it additionally use sorryAx. The only direct hole is the
   reported named differential theorem; no forbidden declarations or hollow data.
   The chosen degree maps come from a proved existence theorem, not an unproved
   arbitrary-witness theorem.
3. PASS: read the differential statement and its full docstring argument against
   homComplex_exists's chosen projections and differential formula. It asserts
   compatibility of supplied normalized maps, strictly one part of the parent
   construction. Pure tensors generate over the bottom-topology site, and slice
   evaluation and product projections detect equality, so normalization suffices.
   Zero rings, zero terms, identity scalar extension and nonadjacent degrees do
   not require extra assumptions. Independent leanfinder search for tensor extension
   commuting with the cochain Hom differential found Mathlib HomComplex differential
   identities, not this sheaf-valued scalar-extension assertion. Loogle search for
   LinearMap.liftBaseChange confirmed the ordinary tensor infrastructure already
   used. Repository rg searches found no independent replacement. Existing
   RingHomExtensionTransport and RingExtensionInternalHomExt depend on the item
   via PerfectRHomBaseChangeMap, so importing them would create a cycle. Closing the
   remaining verification requires the coordinate/tensor extensionality argument;
   it is not a missing one-line Mathlib application.
4. PASS: the item assembles proved degree maps and their normalization before
   applying the separate compatibility lemma. The sole Mathlib proof import is
   private; shared definitions needed in public signatures are publicly imported.
   No unused direct proof import was found. All three original proof dependencies
   remain used transitively and are accounted for under No longer needed; no
   module is claimed pruned. The unit's realized lists are empty, and no recorded
   unit realization or route is removed. The parent's construction and verification
   steps remain represented separately in the same unit. This closes one upper
   hole and adds one strictly smaller hole: decomposition, with net zero holes.
5. PASS: checked all four node records against their Lean declarations. The parent
   uses exactly the degree and differential nodes. The degree node records direct
   tensor-Hom conjugation, unit naturality and Fan.IsLimit.lift/fac. The remaining
   node records the coordinate differential argument and matches its named hole.
   The shared-definition node records unchanged relocated data. Existing-node edits
   are restricted to lean, proof, proof_deps and proof_origin; new-node source,
   searches, creation, chapter/unit, blueprint and Lean fields are present.

Second reading changed only this report by adding the independent checks and axiom
results. No Lean proof or statement repair was needed. The scratch axiom copy was
removed before delivery.
