## What changed

Replaced the sole hole in `Module.flat_of_flat_closedFiber` by a complete Lean proof
from a common Noetherian model, the existing Noetherian fibre criterion, base change,
and the existing theorem that localization of an algebra module preserves flatness
over the base. Its signature and public imports are unchanged.

Added `Sheaf.RingTheory.NoetherianFlatClosedFiberModel`, with the public theorem
`Module.exists_noetherian_flat_closedFiber_model`. It groups the original argument's
steps 1--8 and the two limit localization comparisons. The model asserts base and
closed-fibre flatness of the stage module; it asserts neither flatness of the middle
stage ring over the base nor flatness of the stage module over the middle ring.
The parent obtains those two facts by actually applying
`Module.flat_and_flat_of_flat_fibre_noetherian` and then transports them.

The model allows `M = 0`, so the parent proves `Nontrivial N₀` itself: zero `N₀`
would give zero tensor product and zero localization, contradicting the comparison
with nonzero `M`. No data definition is chosen from an unproved existence statement;
the existential witnesses are eliminated only inside the proof of the parent theorem.

Updated both DAG proof routes to match the Lean. Compiled both files as a set through
`lcompile.py --all`; their declarations elaborate with no warnings.

## Proved and sorry left

Closed the original hole in `Module.flat_of_flat_closedFiber`
(node `lem-weil-pbc-criterion-flatness-fibre`): 1 of 1 original holes closed.

Added exactly one hole, `Module.exists_noetherian_flat_closedFiber_model`
(node `lem-weil-pbc-noetherian-flat-closed-fiber-model`), in its separate module.
Its proof is exactly `by sorry`; its docstring and node give the full argument and
sources. This delivery is a **decomposition**, with one upper hole closed and one
lower hole added, not a claim of a complete axiom-free proof or positive net progress.
There are no holes left in the item's module and no other holes added.

Existing imported statements remain work for their own items, including
`Module.flat_and_flat_of_flat_fibre_noetherian` and
`Module.Flat.localizedModule_of_algebra`; this delivery does not edit them.

## No longer needed

Removed the direct proof imports `Sheaf.Paper.LimitTowerEssentiallyFinitePresentation`
and `Sheaf.RingTheory.ColimitEventuallyFlat` from the item. Both remain needed in the
new model's proof plan, and are imported by that module. They are relocated, not pruned
from the target import closure. The Noetherian criterion import is retained.

Added only proof imports of `Sheaf.RingTheory.NoetherianFlatClosedFiberModel` and
`Sheaf.RingTheory.Flat.LocalizationPreservesFlatness` to the item.
The latter is the existing general tool matching Claim L of the original proof.
Its node is in another unit (`lem-pc-affine-flat-module-localization-preserves-flatness`);
it is used as that general localization tool, with no change of the unit's route.

No original mathematical dependency or module can be declared globally pruned:
the first eight steps are still required by the model. The new node retains their
proof dependencies; the parent records only the four dependencies it now directly uses.
The unit `sk-thm-p1` and its realized statements and steps are untouched.


For completeness, the following old direct `proof_deps` are now carried by the
model node rather than used directly by the parent (none is globally pruned):

- `def-weil-directed-colimit-abelian-groups`
- `def-weil-finitely-generated-module`
- `def-weil-pbc-essentially-finite-type-algebra`
- `def-weil-pbc-finitely-presented-algebra`
- `def-weil-pbc-flat-ring-map`
- `def-weil-pbc-module-localization`
- `def-weil-pbc-noetherian-ring`
- `lem-weil-pbc-colimit-eventually-flat`
- `lem-weil-pbc-commutative-algebras-colimits-exist`
- `lem-weil-pbc-filtered-colimit-algebras-elementwise`
- `lem-weil-pbc-filtered-colimit-modules-elementwise`
- `lem-weil-pbc-filtered-colimit-rings-zero`
- `lem-weil-pbc-finite-type-algebra-noetherian`
- `lem-weil-pbc-limit-tower-essentially-finite-presentation`
- `lem-weil-pbc-localization-base-change`
- `lem-weil-pbc-localization-module-exact`
- `lem-weil-pbc-localization-noetherian`
- `lem-weil-pbc-localization-of-localization`
- `lem-weil-pbc-localization-tensor-over-base`
- `lem-weil-pbc-surjective-image-noetherian`
- `lem-weil-pbc-tensor-over-quotient-ring`

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or marked disputed. The limit-tower statement
uses one common universe for its three limit rings, unlike this item's three independent
universes; the new model makes the common stage universe explicit as `max u v w` and
keeps the stage module in `Type t`, so that lift transport is part of its stated proof.
This is interface bookkeeping, not a restriction on the parent theorem.

The source's concluding equalities require the localization corrections already
recorded by the original DAG. The Lean proof uses module-localization comparisons,
not equality with unlocalized base changes. Read the original DAG proof and the
Stacks pages https://stacks.math.columbia.edu/tag/00R7 and
https://stacks.math.columbia.edu/tag/00R6 (the literature checkout is not present here).
The source and existing Noetherian criterion need nonzero `M`, while the intermediate
model does not: the parent derives its necessary nonzero stage condition from the
comparison, as checked by the compiler.

## New nodes

`lem-weil-pbc-noetherian-flat-closed-fiber-model`, in
`dag/nodes/sec-proper-base-change/`, records the common-stage approximation before
applying Tag 00MP. Source: Algebra, proof of Tag 00R7, first two paragraphs; the
existing node's localization corrections and limit comparison clauses give the two
module localization equivalences. It is a genuine intermediate stage construction,
not either conclusion of the parent's theorem under a new name.

Edge cases checked against the statement and proof: the zero module is permitted
in the model, and gives a zero model; all local rings are nontrivial by `IsLocalRing`;
locality keeps the extended maximal ideals proper, so the fibre stage rings are local;
no domain, reducedness, positive rank, or nonzero tensor assumption is added.
The parent derives nonzero of its model from the module comparison, rather than
assuming localization reflects nonzero (it need not do so).

Searches ran through `msearch.py`: LeanSearch for a Noetherian model with simultaneous
base and fibre flatness returned HTTP 500 (recorded as unavailable); LeanFinder found
Noetherian smooth flatness, finite/finite-presentation equivalences, and flatness of
adic completion, but no such approximation theorem; Mathlib grep for
`noetherian.*flat.*(model|approx)|flat.*(fiber|fibre).*stage` found no matches.
Also searched Loogle for `Module.Flat`, the source and statement libraries for fibre
flatness/model declarations, and the imported blueprint with `blueprint_refs.py`;
no existing declaration gives this common-stage conclusion.

No definition or statement changes, change records, or forced adaptations are included.

## Second reading by K3

1. **Interfaces: PASS.** Compared the item against the repository with `diff` and
   compared its full theorem signature as raw text: byte-for-byte identical.
   All existing public imports and visibility remain identical; only proof imports
   and the proof body differ. There are no definition or statement changes and no
   forced adaptations. Restored the original theorem docstring verbatim.
2. **Proof and axioms: PASS as a decomposition.** Both modules compile through
   `lcompile.py --all` without errors or warnings. Scratch copies with `#print axioms`
   for `Module.flat_of_flat_closedFiber` and
   `Module.exists_noetherian_flat_closedFiber_model` report exactly `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. The latter is expected from the
   one new model hole and the existing imported open theorems. The only literal
   `sorry` delivered is the named model theorem, with a complete source-based
   docstring; no data definition, forbidden declaration, or arbitrary witness
   construction is added. The existential witnesses are eliminated within a proof
   of a proposition. Checked the nonzero argument in particular: it uses that a
   zero module's tensor product and localization are zero, not reflection of
   nonzero by localization.
3. **Split statement: PASS.** Read the common-stage statement against the first
   two paragraphs of [Stacks 00R7](https://stacks.math.columbia.edu/tag/00R7) and the
   existing limit-tower and eventual-flatness interfaces. Its conclusion is the
   approximation data before the Noetherian criterion; neither desired flatness
   conclusion is included. Zero modules are allowed; the parent supplies nonzero
   of the stage module. Locality makes the fibre ideals proper even for rings
   with nilpotents, and quotient rings remain Noetherian local. Independent
   LeanFinder search for descent to Noetherian subrings with simultaneous flatness,
   Mathlib grep for eventual/descent flatness and Noetherian models, and repository
   searches found no equivalent declaration. Inspected Mathlib's smooth Noetherian
   descent and the upstream `exists_noetherian_model` and local flatness-descent
   tools: they give useful pieces, but do not provide the simultaneous local tower,
   module, and closed-fibre approximation. Closing this model is substantial work,
   not a short application of a known theorem.
4. **Route and pruning: PASS.** The compiled reduction actually invokes the existing
   Noetherian criterion, flat base-change instances, the general module-localization
   tool, and transport along linear equivalences. The model retains the limit and
   fibre-system route of the old proof. Its public imports support its signature;
   Sheaf imports are proof-only. The localization theorem is a general tool from
   another unit, implementing Claim L of the original argument. The unit
   `sk-thm-p1` and every `realized` entry are unchanged. Expanded `No longer needed`
   to enumerate all 21 old direct dependencies relocated to the model; no claim of
   pruning from the target closure or positive net hole reduction is made.
5. **DAG: PASS.** Checked the existing node's only changed fields are `proof`,
   `proof_deps`, and `proof_origin`. Both nodes' `proof_deps` equal exactly the union
   of their proof steps' `uses`. The new node has the required source, creation,
   blueprint, searches, chapter/unit, and Lean records; its Lean signature is
   verbatim. The parent route matches the compiled proof and the model route
   describes precisely the remaining approximation argument.

Second-reading changes: restored the existing theorem docstring, completed the list
of relocated direct dependencies in the report, and added this independent review.
No mathematical proof or statement repair was needed. The accounting remains one
original hole closed, one model hole added: a decomposition with net zero holes.
