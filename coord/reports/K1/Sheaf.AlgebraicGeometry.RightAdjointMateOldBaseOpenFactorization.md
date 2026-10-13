## What changed

Replaced the sole sorry of `AlgebraicGeometry.rightAdjoint_mate_oldBase_open_factorization`
by a complete Lean proof from two strictly separate intermediate theorems. The existing
signature and docstring are unchanged. Constructed the genuine iterated pullback Q,
the comparison k from Q to the rectangle pullback, and the comparison r from the
restricted-source pullback to Q. Proved their projections and the equations r ≫ k = s
and r ≫ q = t using the pullback universal property. Chose the right adjoint d of the
canonical lifted direct image Q → T via its IsLeftAdjoint instance and
Adjunction.ofIsLeftAdjoint: its adjunction determines d up to the comparison used here.

The first intermediate theorem transports ordinary base-change invertibility and the
second mate across an arbitrary source-scheme isomorphism. It has one square, no old
base open, and no factorization conclusion. The second is the successive-square mate
pasting law on the genuine iterated pullback, with no restricted source or open model.
The main proof applies both, maps the pasted equality along r, and uses derived
pullback composition to identify its maps with the supplied s and t. The proved private
helper `transport_arrow_factorization` combines arrow isomorphisms by their source and
target projections, using Arrow.w and Arrow.iso_w. Neither the open mate nor the local
mate is inverted.

Added proof-only imports of RightAdjointMateSchemeIsoTransport,
RightAdjointMateSuccessiveBaseChange, and DerivedPullbackComposition to the item.
The two new modules publicly import only their statement interfaces, and privately
import DerivedBaseChangePasting and RingedSpaceDerivedDirectImageComposition for their
recorded proof plans. Updated the original node's proof and proof dependencies to
match the implemented reduction. No existing definitions or statement interfaces changed.

Compilation was performed through lcompile.py, both incrementally and as an import-ordered
set. Empty schemes, identity source isomorphisms, identity base morphisms, zero derived
objects, and noninvertible second mates were checked against the two statement forms:
the argument uses functoriality, adjunction identities, and ordinary base-change
invertibility only. In particular it does not require a second mate to be invertible.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.rightAdjoint_mate_oldBase_open_factorization`
(node `lem-sc-right-adjoint-mate-old-base-open-factorization`).
There is no sorry in the item's module or its private helper.

Added exactly two named holes, each in a separate public theorem with its own source,
proof in words, and DAG node:

- `AlgebraicGeometry.rightAdjoint_mate_scheme_iso_transport`, in
  Sheaf.AlgebraicGeometry.RightAdjointMateSchemeIsoTransport,
  node `lem-sc-right-adjoint-mate-scheme-iso-transport`.
- `AlgebraicGeometry.rightAdjoint_mate_successive_baseChange`, in
  Sheaf.AlgebraicGeometry.RightAdjointMateSuccessiveBaseChange,
  node `lem-sc-right-adjoint-mate-successive-base-change`.

This is a decomposition, not a sorry-free proof of the transitive closure: one upper
hole closed, two strictly separate lower holes added (net -1). No hole is hidden in a
definition. The only additional adjoint object is selected from an adjunction existence
instance, which determines it up to the equality/isomorphism used downstream.

## No longer needed

Removed the item's direct proof imports of
Sheaf.AlgebraicGeometry.DerivedBaseChangePasting and
Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition. They are now proof-plan
imports of the two lower modules, so this is a relocation, not a claim of global pruning.
The complete list of old proof-dependency edges removed from the item is:

- `def-pc-derived-base-change-map`;
- `lem-pc-derived-base-change-pasting`;
- `lem-pc-ringed-spaces-derived-direct-image-composition`.

The latter two correspond to the removed direct imports above. These nodes remain
necessary for the two separate categorical steps. The first edge is no longer direct at the item;
it remains a dependency of both lower statements. All original dependency nodes still
occur below the reduction. No globally unneeded nodes or modules are claimed; pruned none.

## Where the brief, the DAG or earlier work was wrong

The DAG's existing schemeDerivedBaseChange_pasting theorem controls upper-left transport
of the ordinary mate before unit cancellation. It does not already state either the
successive-square law for the fixed second mate or its invariance under a source-scheme
isomorphism. These are separate integration steps, now explicitly named. There is no
statement dispute or change to the unit route: the cartesian restriction comparison and
the successive-square mate argument from the original plan are both retained.

The local literature/stacks-project/duality.tex file is absent on this machine. Read the
cited official source pages instead: [Tag 0ATR](https://stacks.math.columbia.edu/tag/0ATR)
for the pasted second-mate diagram, and
[Tag 0E9S](https://stacks.math.columbia.edu/tag/0E9S) for the open restriction identification.
The new lemmas retain ordinary base-change invertibility as explicit assumptions; the
Tor-independence assumptions in Tag 0ATR supply those isomorphisms and are not used in
its categorical calculation. The existing factorization already has that abstraction.

## New nodes

`lem-sc-right-adjoint-mate-scheme-iso-transport` isolates the invariance of one square
under replacement of its source scheme by an isomorphic scheme. It supplies ordinary
invertibility for the genuine inner pullback and an arrow isomorphism comparing its
second mate with the restricted-source mate. Its statement has no open or factorization.

`lem-sc-right-adjoint-mate-successive-base-change` isolates horizontal pasting on the
genuine iterated pullback. It has no identification with an open restriction. The main
proof supplies the concrete maps, transports this equality, and composes its endpoint
comparisons with the first lemma. Both nodes belong to sec-picard-framework,
sk-thm-picard-duality, and inherit the original blueprint ancestor lem-sc-finite-duality.
No change record or forced adaptation is needed.

## Second reading by K1

1. **Interfaces unchanged: pass.** Read the full diff against the repository version.
   The existing theorem signature, including all hypotheses and the three-arrow
   conclusion, is byte-for-byte identical. The original docstring and public imports
   are unchanged. Only its proof, proof-only imports, and a proved private helper were
   added or changed. There are no definition changes or forced adaptations.

2. **Lean and axioms: pass as a decomposition.** Independently compiled all three
   modules in import order through lcompile.py: 5.3 s, 7.6 s, and 20.8 s, with no
   warnings or errors. Compiled scratch copies with #print axioms for all three
   public theorems and the private helper. The helper uses only propext,
   Classical.choice, and Quot.sound. The public theorems additionally use sorryAx,
   as expected from the two named lower holes and open upstream results. There are
   exactly two delivered sorry occurrences, each the entire proof of its named
   lower theorem; none is in a definition. No forbidden declaration or attribute
   occurs. The new right adjoint d is characterized by its supplied adjunction,
   so selecting it does not select arbitrary geometric data. The pullback maps
   k and r are explicit universal-property constructions.

3. **Lower statements: pass.** Read both signatures and their docstring arguments
   against the fixed dualityEquationBaseChangeMap construction and the cited
   [Tag 0ATR](https://stacks.math.columbia.edu/tag/0ATR) and
   [Tag 0E9S](https://stacks.math.columbia.edu/tag/0E9S).
   The first hole is invariance of one square under an isomorphism of its source,
   including transport of ordinary invertibility; it contains no open restriction
   or factorization. Its projection equations determine r as the base change of e.
   The second hole is horizontal pasting on the genuine iterated pullback; it
   contains no identification with the restricted-source model. Their combination
   requires the proved projection and arrow-transport glue in the item, so neither
   restates the item. Identity source isomorphisms reduce the first assertion to
   right-adjoint uniqueness. Identity base changes reduce the second to the unit
   laws. Empty schemes and K=0 impose no extra hypotheses, and noninvertible
   second mates remain permitted: only the ordinary comparisons are inverted.
   For arbitrary choices of adjunctions, the comparison isomorphisms must use their
   units and counits; right-adjoint uniqueness supplies exactly those identities.
   The universal quantifier over hβf in the first theorem is harmless by proof
   irrelevance. No counterexample or missing geometric assumption was found.

   Repeated search with different wording: Lean Finder for “Beck Chevalley
   transformation invariant under replacing the top scheme by an isomorphic
   scheme”, Loogle for conjugateEquiv, and local rg for mate/isomorphism/composition
   and base-change coherence. Read Mathlib's conjugateEquiv_comp and mateEquiv
   pasting laws and the upstream SixFunctors.BaseChange.Pasting module. The latter
   concerns underived etale sheaves; it does not identify these fixed derived
   module mates. The existing schemeDerivedBaseChange_pasting theorem concerns
   upper-left transport of an ordinary comparison, not either new second-mate
   assertion. Generic categorical results are useful ingredients, but closing
   either lower hole also requires the derived and QCoh comparison integration;
   neither has a direct existing match or a short complete replacement proof.

4. **Route and pruning: pass.** Traced the proof from the original theorem through
   the two smaller categorical steps. Read DerivedPullbackComposition and the
   ordinary-pasting and direct-image-composition interfaces. The private helper
   uses Arrow.w and Arrow.iso_w correctly, with the inverse of eo at the source.
   The equalities r ≫ k = s and r ≫ q = t follow from both projections, not from
   additional assumptions. The item has only the three needed proof imports;
   the lower modules retain the imports for their recorded open proof plans.
   Checked dag/units/sk-thm-picard-duality.json: its realized fields remain
   unchanged (currently empty), and no realized unit statement or step is bypassed.
   All three old direct dependency edges removed are now listed explicitly under
   No longer needed. They remain below the new reduction, so global pruning is
   none. This closes one upper hole and adds two lower holes: decomposition,
   net -1, not a proof of the whole import closure.

5. **DAG agreement: pass.** Parsed all three JSON nodes. Each lean.statement is
   byte-for-byte the delivered theorem signature, and each proof_deps equals the
   union of the proof steps' uses. The existing node changes only proof,
   proof_deps, and proof_origin. Both new nodes have their source, proof in steps,
   three successful search kinds, creation and blueprint provenance, status,
   chapter, unit, and complete Lean records. Their natural-language statements
   match the Lean, including ordinary invertibility and arbitrary specified
   adjunctions. The existing proof node now records the real reduction rather
   than claiming the lower categorical calculations were already formalized.

Second-reading changes: completed the explicit list of removed old dependency
edges in No longer needed and added this review with independent compile, axiom,
source, and search evidence. No Lean proof or statement required repair. Scratch
axiom probes were removed before delivery.
