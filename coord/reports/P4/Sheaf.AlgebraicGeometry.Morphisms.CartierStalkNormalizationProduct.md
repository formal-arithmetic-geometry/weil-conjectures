## What changed

Replaced the whole proof of `AlgebraicGeometry.Scheme.cartier_stalk_normalization_product`
without changing its signature or docstring. This is a decomposition into two geometric
comparison statements, followed by a complete Lean assembly.

`CartierStalkPuncturedComplement` states only the Cartier-complement pullback square.
The original torsor is base-changed using the existing proved
`GaloisCover.exists_baseChange`; pullback cancellation and pasting identify its source.
The existing field torsor component theorems supply the fields and subgroup equivalences.
The proof explicitly transports the automorphism actions using
`MulSemiringAction.compHom` and `IsGaloisGroup.of_mulEquiv`.

`NormalizationStalkFieldCoproduct` states the normalization comparison for a supplied
field coproduct over a stalk. It has no group, Cartier, DVR, finite-normalization, or
module-finiteness assumptions or conclusions. Factor finiteness is proved in the main
module: finite coproduct inclusions of spectra are finite, and composition with the
inverse normalization isomorphism and the finite pullback projection gives each finite
algebra map. The inclusion proof uses surjectivity of product evaluation, with `ULift`
reindexing to meet `sigmaSpec`'s equal-universe instance.

Updated the parent node's proof, proof dependencies and origin. Added two new modules
and their nodes. No existing definitions, statements, visibility or public imports changed.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Scheme.cartier_stalk_normalization_product`
(lem-sbc-cartier-stalk-normalization-product). Its proof has no `sorry`.

Added two holes, each the entire proof of a named public theorem:

- `AlgebraicGeometry.Scheme.cartier_stalk_punctured_complement`
  (lem-sbc-cartier-stalk-punctured-complement).
- `AlgebraicGeometry.Scheme.normalization_stalk_field_coproduct`
  (lem-sbc-normalization-stalk-field-coproduct).

This is a decomposition, not a completed proof of the dependency closure: one hole
closed, two added. Torsor base change, field decomposition, subgroup-action transport,
the structural-map assembly, and factor module finiteness are proved from the named
statements. All three delivered modules compile cleanly through `lcompile.py --all`.

The new complement statement was checked on the trivial cover-independent case
Spec Z localized at a nonzero prime with its reduced closed Cartier centre: its
complement is Spec Q over the actual DVR. A field cannot meet the DVR hypotheses.
The normalization comparison includes n = 0 (the zero ring, empty spectrum) and n = 1,
and permits arbitrary R-algebra maps and fields of arbitrary degree. It asserts no
finiteness of their integral closures. For a trivial group the action transport is
trivial, and the finiteness argument uses the original normalization hypothesis.
No arbitrary witness of an unproved existence theorem is stored in a definition.

## No longer needed

Removed the direct proof import
`Sheaf.AlgebraicGeometry.Morphisms.NormalizationStalkBaseChange`
from the main module. It remains needed by the new normalization comparison module;
its DAG dependency moved there. It is not globally pruned.

No other original import, node, or module is pruned. Both field-torsor modules are
used directly. The new base-change dependency is an existing proved theorem of the
same blueprint unit. The unit and chapter routes remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The original plan treated two substantial comparison steps as glue: the Cartier
complement at the stalk and the entire normalization field-product comparison.
Neither is supplied by the signatures of the three original proof dependencies.
They are now independent items; neither restates the target. The first has no cover
or normalization; the second starts with specified fields and an actual source
isomorphism and constructs no Galois data or finiteness proof.

The existing normalization-stalk-base-change theorem uses the projection from the
pullback of an arbitrary base morphism, rather than directly `N.fromSpecStalk`.
The new normalization node's proof records the identity-pullback comparison needed
when applying it. No change to that existing interface was necessary.

The local literature checkout contains citation tables but no blueprint or Stacks
texts. Source pages for Stacks Tags 01WQ, 0307, 035I, 03SF and 03QR were read online.
The new proof plans are marked written by an agent. The ancestor tool returns None
for this module-created parent; the new nodes record the trait paragraph of
sbc-thm-spreading-finite-etale-galois and the explicit parent chain.

LeanSearch returned Internal Server Error for both new statements, recorded without
a mathematical verdict. LeanFinder and source/DAG searches found the generic affine
normalization and DVR APIs but no duplicate of either statement.

## New nodes

`lem-sbc-cartier-stalk-punctured-complement`, in
`dag/nodes/sec-smooth-base-change/lem-sbc-cartier-stalk-punctured-complement.json`,
is stated by `Sheaf.AlgebraicGeometry.Morphisms.CartierStalkPuncturedComplement`.
It isolates exactly the Cartier-complement comparison of parent step 1. Its docstring
and node give the stalk quotient, uniformizer localization and pullback argument.

`lem-sbc-normalization-stalk-field-coproduct`, in
`dag/nodes/sec-smooth-base-change/lem-sbc-normalization-stalk-field-coproduct.json`,
is stated by `Sheaf.AlgebraicGeometry.Morphisms.NormalizationStalkFieldCoproduct`.
It isolates parent step 2, using the existing normalization-stalk-base-change node
and the finite coordinatewise integral-closure calculation. No change records were
needed, since every existing signature and definition is unchanged.

## Second reading by P4

Independent second reader, 2026-10-14. Read the three delivered modules, their
nodes, the original module and node, the three original proof-dependency modules,
the added base-change dependency, and the unit record.

1. **Interface preservation: pass.** `diff -u` shows only the proof body and plain
   proof imports changed in the existing module. A byte comparison confirms that
   the existing theorem signature and docstring are identical. There are no
   delivered definitions, adaptations, or existing visibility/public-import changes;
   no change record is required.
2. **Proof and axioms: pass as a decomposition.** Compiled all three modules in
   import order using `lcompile.py --all`, with no errors or warnings. Independently
   compiled a scratch copy with `#print axioms` for all three delivered declarations:
   only `propext`, `Classical.choice`, `Quot.sound`, and the permitted `sorryAx` occur.
   The only two explicit holes are the reported entire public theorem proofs; no
   forbidden declaration or hollow definition occurs. Witness selection stays
   inside the parent theorem proof. Read the pullback cancellation/pasting, the
   component inclusion, inverse-equivalence action transport, and the finite-factor
   proof; each proves the stated clause for the actual structural maps.
3. **Split statements: pass.** Both are strictly smaller parts of the original
   geometric argument. The complement lemma contains no cover or normalization;
   the normalization lemma requires supplied fields and an actual source
   presentation and concludes no Galois or module-finiteness result. Checked the
   Cartier quotient at the integral generic point and the nonzero uniformizer
   argument; a field stalk cannot satisfy these centre hypotheses. Checked the
   normalization comparison for zero and one components, noninjective R-algebra
   maps, and extensions of arbitrary degree; coordinatewise integrality requires
   only finitely many components, not finite field degrees. The empty product is
   the zero ring and the normalization is empty. Sources independently read:
   [Cartier local equations](https://stacks.math.columbia.edu/tag/01WQ),
   [localization of integral closure](https://stacks.math.columbia.edu/tag/0307),
   and [relative normalization](https://stacks.math.columbia.edu/tag/035I).
   Both docstrings and nodes give complete mathematical proof plans. Fresh
   LeanFinder searches used “punctured spectrum discrete valuation ring fraction
   field open immersion” and “normalization of an affine morphism spectrum algebra
   integral closure ring algebra equivalence finite product”; source searches
   checked `normalizationCoprodIso`, `normalizationObjIso`, and punctured-spectrum
   APIs. No duplicate or direct specialization was found. A Loogle query involving
   `Pi` was rejected as an unknown identifier and supplies no mathematical evidence.
   Neither full geometric comparison could be closed by a few-minute application
   of the APIs found.
4. **Route and pruning: pass.** The parent proof uses all its remaining proof imports.
   The sole removed original proof dependency is normalization stalk base change,
   now used by the new comparison module and explicitly recorded above; it is not
   globally pruned. All public imports concern signature vocabulary. The trait
   normalization and field-factor route of `sk-prop-input-spreading` is retained.
   Its pre-existing `realized` arrays are empty; this delivery neither changes that
   record nor bypasses a realized node. No assertion of whole-closure progress is
   made: one original hole is closed and two strictly smaller holes are added.
5. **DAG agreement: pass.** Checked the parent proof steps against the Lean body,
   including the proved base-change node and finite-factor argument. Programmatic
   checks confirm that each node's recorded Lean statement matches its module and
   that `proof_deps` is exactly the union of its proof steps' `uses`. The new nodes
   carry sources, origins, searches, creation and blueprint provenance, chapter,
   unit, and complete Lean records. Existing non-stage-3 fields were not edited.

Second reading changed only this report, adding the independent review and its
verification evidence. The Lean proofs and node records required no repair.
