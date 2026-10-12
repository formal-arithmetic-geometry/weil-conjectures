## What changed

Replaced the sole sorry in
`AlgebraicGeometry.Scheme.GaloisCover.exists_larger_open_finiteEtale_model`
with a complete Lean proof combining a local neighbourhood extension with the existing
finite étale gluing theorem. All existing signatures, public imports, and docstrings are
unchanged. The two added imports are proof-only.

Added `Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap`, whose one theorem
isolates the local extension near a missing point and its comparison on the overlap.
The neighbourhood W need not contain U; this theorem neither constructs a cover on
U union W nor asserts the original conclusion under a different name.

The item constructs V = U union W and proves strict enlargement using the missing point.
It checks that the two inverse-image opens cover c inverse V, invokes the source library's
`FiniteEtale.exists_pullback_iso_of_isPullback`, extracts the resulting cartesian restriction
square, and pastes it with the original generic restriction square. The generic-fibre
factorization is the original factorization followed by the open inclusion.

Both modules compile cleanly through lcompile.py. An explicit #print axioms check of
the gluing theorem shows only propext, Classical.choice, and Quot.sound. The module-system import-direction check
allows the gluing import. No definitions, target signatures, other modules, or unit records
were changed. The route remains the local claim and spreading of Stacks 0EYJ followed by
gluing, as required by the unit's Noetherian-base argument.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.GaloisCover.exists_larger_open_finiteEtale_model`
(node `lem-sbc-enlarge-open-finite-etale-model`). The item's module has no sorry left.

Added one hole in
`AlgebraicGeometry.Scheme.GaloisCover.exists_local_finiteEtale_model_overlap`
(node `lem-sbc-local-finite-etale-model-overlap`) in its own new module.
Its proof is exactly `by sorry`, with the local trait/depth-two argument and neighbourhood
spreading written in its docstring. This delivery is a decomposition: one upper hole closed,
one strictly local hole added; net hole reduction zero.

`AlgebraicGeometry.Scheme.FiniteEtale.exists_pullback_iso_of_isPullback`
(node `lem-sbc-finite-etale-two-open-gluing`) already has a proof in the source library;
this delivery registers that tool and introduces no corresponding hole or duplicate module.

The remaining local input includes the difficult tame-normalization/depth-two extension and
spreading with comparison. It is not claimed proved. In particular, the displayed overlap
isomorphism is part of that input, not obtained by assuming arbitrary covers glue without a
comparison.

## No longer needed

No existing import, node, or module is pruned. The original node had no proof dependencies
and the item had no proof-only imports to remove. The new local module uses the existing
finite étale category and pullback functor; no alternative construction is introduced.

## Where the brief, the DAG or earlier work was wrong

The brief says each proof step names its input nodes, but this item's original node had
one long non-elementary step and an empty proof_deps list. There was no supplied local
extension statement to apply. This delivery makes its local neighbourhood input explicit
and uses the already proved two-open gluing theorem for the assembly.

The blueprint-ancestor utility reports no ancestor for this module-created node; its
existing blueprint.from field explicitly names sbc-thm-spreading-finite-etale-galois.
The new nodes preserve that recorded ancestor and the parent chain.

Mathlib searches were run via msearch.py and are recorded in searches.jsonl and the new
nodes. LeanSearch returned HTTP 500; the local-extension LeanFinder query was unavailable.
Loogle and source grep found no local extension theorem. The gluing search found generic
Mathlib scheme-gluing machinery, while a direct library search found the exact finite
étale gluing theorem used here. Existing normal-generic fullness inputs were inspected;
they do not supply the local étale extension.

Edge cases of the new local statement were checked mathematically: U cannot be empty
because it contains the generic point; U cannot be all of S; a field base admits no such
proper U, so the assertion there is vacuous. Nonempty W meets the dense open U of the
integral base, so overlap comparison has the expected generic content. Disconnected
torsors are retained and addressed componentwise with stabilizers in the proof sketch.
The gluing tool permits empty/disconnected finite étale schemes and needs no normality,
Noetherian, section, or group assumptions; the item's proof uses only its cartesian
intersection, covering, and overlap-isomorphism hypotheses.

## New nodes

`lem-sbc-local-finite-etale-model-overlap`: the local claim and neighbourhood spreading
part of Stacks 0EYJ, with the exact new Lean signature and complete proof in words.
One sorry in `LocalFiniteEtaleModelOverlap.lean`.

`lem-sbc-finite-etale-two-open-gluing`: records the already proved source-library theorem
`FiniteEtale.exists_pullback_iso_of_isPullback` without adding a module or a sorry.
Its full statement includes the two open immersions, cartesian intersection square,
covering condition, two finite étale schemes, and isomorphism on the intersection.

No change record is needed: no existing statement, definition, or public interface changed.

## Second reading by C1

1. Interface: PASS. Diffed the delivered item against the repository version and
   compared its theorem signature byte for byte. Only two plain proof imports and
   the proof body were added. No existing declaration, definition, public import,
   target, or other existing module changed. The existing node changes only in
   proof, proof_deps, and proof_origin. No change record is required.
2. Proof: PASS as a decomposition. Recompiled both modules in import order with
   lcompile.py, with no errors or warnings. Inspected every proof step: the union
   gives strict enlargement, the inverse-image inclusions cover it, the overlap
   square is cartesian, gluing gives the restriction isomorphism, and pasting gives
   the specified generic restriction. Explicit #print axioms in a removed scratch
   copy gives propext, Classical.choice, Quot.sound, and sorryAx for the item and
   local input; the gluing theorem has only the three permitted axioms. There are
   no forbidden declarations or hollow definitions. Existential witnesses are
   eliminated inside a proposition proof; no definition chooses arbitrary data
   from an unproved existence theorem.
3. Split statement: PASS. Read the local theorem and its source proof at
   https://stacks.math.columbia.edu/tag/0EYJ. Its conclusion is the neighbourhood
   extension and overlap comparison before gluing, not a renamed strict-enlargement
   conclusion. Normality plus smooth geometrically connected fibres supplies the
   normal integral family needed for generic faithfulness. The split section fibre
   and stabilizer reduction cover disconnected torsors. Checked empty U (excluded
   by the generic point), U=top (excluded), a field base (vacuous), trivial G, and
   empty or disconnected covers (empty torsors are excluded by hZ; gluing itself
   permits them). The source-backed docstring contains the trait, depth-two,
   completion, and spreading argument. The difficult local input remains open.
   Independent LeanFinder search used "punctured spectrum of normal local base"
   and "split section"; it found only etale-locus and smooth-chart lemmas.
   Loogle query "IsPullback", "Etale" found no match. Library grep for depth,
   punctured, extension, and generic full faithfulness found no local extension
   already stated. Generic hom fullness does not construct the missing cover.
4. Route and pruning: PASS. The real gluing assembly is already short and uses
   the proved library tool rather than a new gluing hole. The original node had
   empty proof_deps, so there are no old dependency nodes to prune. Both added
   imports of the item are proof-only. The new module's public Functoriality
   import is necessary for FiniteEtale.pullback in its signature. Read
   dag/units/sk-prop-input-spreading.json: the Noetherian local claim, trait case,
   depth-two calculation, and spreading route are retained. Its realized record
   is unchanged; this item does not replace the unit statement or its steps.
5. DAG: PASS. Read all three delivered node records against the Lean declarations.
   The item names exactly its local overlap and proved gluing dependencies, and
   its three proof steps follow the Lean assembly. Both new nodes have source,
   origin, searches, creation, ancestor, chapter, unit, and Lean records. The local
   node records the one new named sorry; the gluing node records an existing
   proved declaration and introduces no duplicate Lean theorem or hole.

Second reading changed only this report by adding the independent review and
explicit axiom results. No Lean repair was necessary. One original hole closed,
one local hole added: decomposition, net hole reduction zero, no pruning.
