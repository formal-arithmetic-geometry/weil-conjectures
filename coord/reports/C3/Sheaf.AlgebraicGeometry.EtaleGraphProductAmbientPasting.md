## What changed

Replaced the hole in `AlgebraicGeometry.Etale.etaleGraphProductAmbientPasting`
by a proof assembling two strictly smaller subgrid identities. The private
`paste_source_and_square` lemma proves the assembly for arbitrary categories:
it evaluates the two identities, combines maps under a functor, substitutes the
source identity, and uses naturality of the middle tail to move it past the lift.
Three private factorization lemmas identify the original diagram word and each
middle ambient change with these boundary words by reflexivity. The theorem
applies the assembly to each Boolean side, with its exact original statement
and docstring.

Extracted all 85 existing ambient geometry declarations, without changing their
names, signatures, attributes or bodies, into
`Sheaf.AlgebraicGeometry.EtaleGraphProductAmbientGeometry`. The original module
publicly reexports this module, which keeps the original public import. This
extraction allows both subgrid modules to import the explicit geometry without
an import cycle. It is not a split to evade the compilation time limit.

Added explicitly constructed `rawSquare`, and `e_side_square`, `R_q`,
`sourceTransport`, `middleTail` on each side. These contain only the existing
fixed proper/open exchanges and canonical compositors. No data comes from a new
existence claim. The new source and target subgrid modules are proof imports of
the original module.

The source identity contains the e-side exchange, the f-side ambient change and
the inverse B exchange; it has neither the supplied k-square exchange nor Q.
The target identity contains the supplied k-square, horizontal e/k factorization,
the middle side projection and Q; it has neither the f-side ambient change nor
the inverse B exchange. Each is a genuine part of the original argument and
neither states its conclusion with a renamed or repackaged hypothesis.

Change record: `coord/changes/etale-graph-product-ambient-boundaries.md`.

Server compilation succeeded for all four modules: geometry 56.8 s, source
subgrid 41.7 s, target subgrid 42.8 s, and the final assembly 7.8 s. A textual
check confirms the original geometry block and the main theorem's statement
and docstring are preserved exactly. Every Lean line is at most 100 characters;
there are no debug commands or holes in definitions.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.etaleGraphProductAmbientPasting`
(node `lem-pur-etale-graph-product-ambient-pasting`). Its assembly proof is complete.
The generic assembly lemma and the new geometric projection equations are proved.
No hole remains in the item module or in the extracted geometry module.

Added exactly two public theorem holes, each the whole proof `:= by sorry`:

- `AlgebraicGeometry.Etale.etaleGraphAmbientSourcePasting`, node
  `lem-pur-etale-graph-ambient-source-pasting`.
- `AlgebraicGeometry.Etale.etaleGraphAmbientSquarePasting`, node
  `lem-pur-etale-graph-ambient-square-pasting`.

Both have source citations and full proofs in words in their docstrings and
nodes. This is a decomposition: one upper hole closed, two strictly smaller
holes added, net minus one hole of progress. It is not a sorry-free proof of the
underlying coherence theorem. The existing downstream sorries are unchanged.

## No longer needed

No modules or mathematical dependencies pruned. The old direct public import of
`EtaleGraphProductInterchange` is supplied transitively by the extracted geometry
module, preserving all previous visibility. The original planned dependencies
are retained in the geometry and subgrid nodes. The original item now uses the
two subgrid lemmas and their geometry, and naturality for the assembly.

No auxiliary compactification or comparison of the two selected sides is used.
Neither `EtaleGraphProductRowPasting` nor `EtaleGraphProductShrinkPasting` is
imported into the proof, so the proof does not appeal to a parent obligation.

## Where the brief, the DAG or earlier work was wrong

No false statement found. The original node's e/B and k/Q calculations can be
separated at the explicit mixed-neighborhood sourceTransport. Previously the
item left their entire combined equality as one hole. The decomposition now
makes that common boundary and the naturality needed to combine it explicit.

Read the current blueprint's compact-support-base-change and composition units
and the A--F argument of Stacks Tag 0F7J. The unit route is unchanged. Checked
empty schemes and identity maps in the mathematical argument: every map is
constructed by pullbacks and all identities are functorial; no nonemptiness,
extra geometric hypothesis, weakened normalization or choice of a bare-endpoint
isomorphism is introduced.

Existing Cartesian ambient transport composition is not an exact substitute
for the displayed identities with the middle identity-graph splitting and the
supplied non-Cartesian k-square. It remains available for proving the lower
source subgrid. No unrelated source-library declarations were changed.

## New nodes

`def-pur-etale-graph-product-ambient-geometry` records the unchanged explicit
ambient data relocated out of the item, plus the constructed rawSquare,
sourceTransport and middleTail boundary words. It has no holes.

`lem-pur-etale-graph-ambient-source-pasting` is the source e/B subgrid, proved in
words by vertical exchange pasting and canonical proper-compositor coherence.
Its statement omits every k-side and Q exchange.

`lem-pur-etale-graph-ambient-square-pasting` is the k/Q subgrid, proved in words
by two vertical decompositions of the same rectangle and horizontal e/k
pasting. Its statement omits the source ambient change and the inverse B lift.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
