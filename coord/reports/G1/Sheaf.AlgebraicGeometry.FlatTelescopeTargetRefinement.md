## What changed

`Sheaf.AlgebraicGeometry.FlatTelescopeTargetRefinement` now proves its existing
statement unchanged from two separate parts of the original argument. First resolve
an arbitrary bounded-above source tower by a strict quasi-isomorphic split tower
whose terms are coproducts of compact flat generators. Then apply finite-piece bar
enlargement to that structured source. The latter statement stops at the enlarged
bar complex B, its geometric homotopy equivalence into T, and a degreewise-split
1-shift presentation of B. It does not assert the original cone augmentation.

The private, fully proved helper `isIso_split_cone_augmentation` performs that
remaining algebraic calculation. It constructs the boundary homotopy from the
retractions in the degreewise splittings, forms a morphism of distinguished
triangles with identity first two components, and applies Mathlib's triangle
five lemma to the canonical cone augmentation. The homotopy calculation follows
the proved code in `Sheaf.CategoryTheory.Abelian.SplitSESBoundaryComparison`;
that module's derived-category result is not imported or assumed here. The
original theorem composes this augmentation with B -> T, composes the two
level quasi-isomorphisms, and proves strict naturality, the zero shifted
restriction, and the sum identity in Lean.

All three modules compile cleanly with the launcher. The original public imports
and theorem signature are unchanged. Only proof imports were changed. No existing
definition or statement was changed, and no other held module needs adaptation.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.exists_flat_telescope_target_refinement`
(node `lem-sc-flat-telescope-target-refinement`). This is a decomposition from
1 upper hole into 2 genuinely distinct lower holes, not a hole-free geometric proof.

The only new and remaining sorries are:

- `AlgebraicGeometry.exists_compact_flat_generator_tower_resolution`
  (`lem-sc-compact-flat-generator-tower-resolution`), in
  `Sheaf.AlgebraicGeometry.CompactFlatGeneratorTowerResolution`.
- `AlgebraicGeometry.exists_compact_flat_telescope_bar_enlargement`
  (`lem-sc-compact-flat-telescope-bar-enlargement`), in
  `Sheaf.AlgebraicGeometry.CompactFlatTelescopeBarEnlargement`.

Each is a public theorem with proof exactly `:= by sorry`, a complete source-based
argument in its docstring, and its own module and DAG node. The fully proved private
helper has no hole. The original module has no remaining sorry. Closing one and
adding two gives a net increase of one hole in this delivery's declarations;
the ledger should count the result as a decomposition.

Edge cases checked when stating the new theorems: zero complexes use empty
generator coproducts and the zero finite subcomplex; zero augmentations have
empty support; arbitrary original transitions need not be monic; negative and
stage-dependent upper bounds are allowed; degreewise splittings are not assumed
to be chain maps. The compact-support condition quantifies over arbitrary
families of module sheaves in the same universe and asks for actual finite
subcoproduct factorization, not for projectivity or arbitrary epi lifting.

## No longer needed

Removed the direct proof import
`Sheaf.Algebra.Homology.BoundedFlatReplacement` and the original direct proof
edge to `lem-pc-kflat-bounded-flat-replacement` from this module's node. Its
ordinary flat replacement interface is not used by this proof. This does not
claim that the module is globally unreachable: other target paths use it.

No other original import was removed. The two new modules and the Mathlib
ShortExact and DegreewiseSplit proof imports in the target module are all used.
The second reading removed the redundant public DegreewiseSplit import from the
new bar-enlargement module; its signature is already supported by FlatTelescopeStageMap. The proof does not
import `Sheaf.CategoryTheory.Abelian.SplitSESBoundaryComparison`; only its
explicit, already proved homotopy computation was reused locally.

## Where the brief, the DAG or earlier work was wrong

The original sole proof dependency provides flat bounded replacements but does
not supply a coproduct decomposition into compact generators, split transitions,
or the finite-piece/bar infrastructure. These are substantive missing interfaces,
now isolated as the two new statements rather than attributed to ordinary
flat replacement. The generator resolution is the relative cone induction of
[Stacks 06XX](https://stacks.math.columbia.edu/tag/06XX), using the generator class
in [03EW](https://stacks.math.columbia.edu/tag/03EW) and [077J](https://stacks.math.columbia.edu/tag/077J).
The second theorem retains the parent agent-written bar argument; it is not
claimed to be a literal Stacks assertion.

The unit `sk-thm-picard-duality` and its realized route were read and retained.
No target statement, unit statement, or unit step was changed. Mathlib searches
found factorization and simplicial extra-degeneracy APIs but no theorem supplying
these geometric interfaces. LeanSearch was unavailable; that result is recorded
as unavailable, not as a successful negative search.

## New nodes

`lem-sc-compact-flat-generator-tower-resolution` isolates the relative resolution
of the source, independently of any target telescope or bar construction. It
exposes exactly the coproduct-compact generator structure and split transitions
needed downstream; it does not assert the original target refinement.

`lem-sc-compact-flat-telescope-bar-enlargement` assumes that additional source
structure and isolates the finite-subcomplex and target-chain bar constructions.
Its output is a degreewise-split presentation and a geometric bar augmentation,
leaving the canonical telescope-cone construction to the proved caller. Both
inherit the original chapter, unit and nearest blueprint ancestor. Searches of
the imported blueprint for compact generator towers and bar enlargement found
no duplicate. The parent node's proof, proof dependencies and proof origin were
updated to match the complete Lean reduction. There are no change records because
no existing signature, definition, or visibility was changed.

## Second reading by G1

1. **Interface preservation: pass.** Compared the delivered target module with
   the repository by `diff -u` and checked the original theorem signature byte for
   byte, including all hypotheses and the three conditions on r. It is identical.
   No existing definition or visibility changed. The other two Lean modules are
   new. The existing node changes only `proof`, `proof_deps`, and `proof_origin`.
   No change record or forced adaptation is needed.

2. **Kernel proof and holes: pass as a decomposition.** Compiled all three files
   with lcompile.py, and compiled scratch copies with explicit `#print axioms`.
   The private `isIso_split_cone_augmentation` uses exactly propext,
   Classical.choice and Quot.sound; the public original theorem and the two new
   open theorems additionally use sorryAx. Read both summand calculations of the
   homotopy and the morphism of distinguished triangles: the third component is
   the canonical cone augmentation, rather than an unrelated isomorphism. The
   final proof establishes strict naturality, the zero shifted restriction, and
   the sum identity with the original types. Exactly the two named public new
   theorems have sorry, each as its whole proof. No forbidden axiom, unsafe
   declaration, opaque declaration, external implementation, or hollow definition
   occurs. The local splitting choices occur inside a theorem proof, not in a
   public definition built from arbitrary unproved existence data.

3. **Split statements: pass.** Read each new signature, docstring and node.
   The first statement isolates resolution of the source and mentions no target
   telescope. The second assumes compact-generator source structure and isolates
   the geometric enlargement and split presentation; it does not supply the cone
   comparison proved by the caller. These are distinct parts of the original
   argument, not its statement moved to a new name. Independently checked the
   zero complex, empty generator sums, zero augmentation, arbitrary original
   transitions, varying/negative upper bounds, and non-chain-map splittings.
   Compactness is only coproduct finite support: finite subcomplexes have finitely
   many compact generator terms, and factor through finite target cone blocks.
   At stage n only the first n+1 bounds are used. For fixed total degree k, bar
   degree p satisfies 0 <= p <= b-k, so every total diagonal is finite.
   The source diagram must retain stage labels; cofinality of its stage-n part
   follows by enlarging finite generator supports after applying transitions.
   This avoids an implicit compatibility assumption on generator decompositions.
   The new docstring and node now spell this out.

   Checked the cited sources directly: Stacks
   [03EW](https://stacks.math.columbia.edu/tag/03EW) supplies flat generator covers;
   [077J](https://stacks.math.columbia.edu/tag/077J) gives the generator-valued
   truncation tower; [06XX](https://stacks.math.columbia.edu/tag/06XX) contains the
   cone induction and strictification by extending a homotopy. The general source
   tower is the indicated relative version of that induction. The bar enlargement
   remains the explicitly identified agent-written expansion, not a claimed
   verbatim Stacks lemma. Both new nodes have source, complete proof, searches,
   creation/blueprint ancestry, chapter/unit, and matching Lean signatures.

4. **Shortest route, imports and unit: pass after pruning.** Independently searched
   with leanfinder for the canonical split-cone homotopy equivalence and for
   resolution/factorization through finite telescope blocks; searched loogle for
   descShortComplex and grep for split triangles, finite subcoproducts and compact
   flat objects. Also searched lean/ and read RelativeFlatExtension,
   TowerSplitComplexReplacement and SplitSESBoundaryComparison. None supplies
   either complete new geometric interface. Mathlib's descShortComplex theorem is
   a quasi-isomorphism, which alone does not give the required homotopy isomorphism.
   The existing boundary-comparison theorem is in the derived category, so the
   explicit local homotopy and triangle argument are appropriate here. Neither
   open geometric theorem can be closed by one of these results in a few minutes.
   Removed the redundant public DegreewiseSplit import from the new bar module:
   FlatTelescopeStageMap already exposes everything its statement needs. Kept
   DegreewiseSplit as an ordinary proof import in the original module, where its
   triangle API is used. The original removed dependency is exactly
   lem-pc-kflat-bounded-flat-replacement and its BoundedFlatReplacement module;
   the pruning section identifies it without claiming global unreachability.
   Read dag/units/sk-thm-picard-duality.json; its realized lists are empty and
   unchanged. No chapter/unit statement, step, or realized route was edited.

5. **DAG agreement: pass.** Checked all three Lean signatures against their
   recorded `lean.statement`. The parent node's two proof dependencies are exactly
   the geometric theorems applied by its proof, and its remaining steps describe
   the proved cone helper and final composition identities. Its proof origin
   accurately distinguishes the reused homotopy calculation from the new
   homotopy-category triangle argument. The two new nodes retain the parent's
   chapter/unit/blueprint ancestry and record their respective constructions.

Second reading changed the redundant public import and clarified the finite-source
indexing in the new bar theorem's proof docstring and corresponding node; no Lean
statement or proof body changed. It also corrected the import description above
and added this review. Holes closed: one original named theorem; holes added: two
named geometric theorems. This is a decomposition with net one additional hole,
not a hole-free proof of the geometric target.
