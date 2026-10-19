## What changed

Proved the refinement identity and composition laws, parallel-arrow independence,
common-refinement comparison independence, and the cocycle law directly from the
proper/open calculus and the supplied Geometry fields. Proved staircase associativity
componentwise from horizontal/vertical pasting, naturality, pAssoc and jAssoc. Reduced
binary comparison compatibility to the equation for one refining tower, now proved
componentwise from the six-square pasting calculation.
The original theorem signature is unchanged.

Private proved helpers isolate the open part of rho and its vertical-pasting law.
No scheme, functor, natural isomorphism, or other data is chosen from a holed theorem.

## Proved and sorry left

Closed the original single hole in
AlgebraicGeometry.ProperOpenCalculus.compactification_refinement_coherence,
node lem-sp-compactification-refinement-coherence. All eight clauses are proved.

Both retained helper obligations are now proved:

- AlgebraicGeometry.ProperOpenCalculus.properOpen_tower_refinement,
  node lem-sp-proper-open-tower-refinement: horizontal pasting, two vertical
  pasting equations, naturality, and the proper compositor associativity law.
- AlgebraicGeometry.ProperOpenCalculus.properOpen_staircase,
  node lem-sp-proper-open-staircase: horizontal and vertical pasting,
  naturality, and proper/open compositor associativity.

Holes closed in the original library module: one. Holes added: zero.
No sorry remains in any delivered module. No split-off remains unproved.

## No longer needed

Removed direct proof imports Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower
and WeilConjectures.Compactification.CategoryBaseChange. Their geometric existence
results are not used: the original statement already assumes the exact common
refinement and equalizer data as Geometry fields. Consequently proof dependencies
lem-cbc-compactifiable-cofiltered and lem-cbc-compactifiable-compatible-tower are
not used as proof lemmas. They remain legitimate statement dependencies, and the
calculus publicly imports its geometric interfaces, so this does not assert that
those modules disappear from the targets' full import closure.

## Where the brief, the DAG or earlier work was wrong

The old proof plan's geometric existence citations are redundant for this Lean
statement, whose Geometry parameter provides the needed data. The node and Lean
statement otherwise agree. Refinement composition and both identity-square laws
have the correct orientations. No statement or definition was changed.

All three delivered modules compile together through lcompile.py --all.
The original theorem signature and all three node signatures were compared with
the Lean files. There is no direct sorry in the delivery.

The earlier attempt's dry runs failed during shared worktree checkout, before
validation. The resumed dry run reached preflight and requested a change record
for the file-level elaboration options. This continuation supplies that record
and repeats launcher validation without changing any launcher tool.

Edge cases: the proofs work for empty assigned categories, identity refinements,
parallel refinements, and arbitrary supplied common refinements. Both new
statements quantify over existing towers, so they make no nonemptiness or
geometric-existence claim and require no added cartesianness on refinements.

## New nodes

lem-sp-proper-open-tower-refinement (ProperOpenTowerRefinement.lean) is the
proved single-arrow equation in steps 5–7 of the original proof, sourced from Stacks
Tag 0F7J, lemma-shriek-composition, the six-square calculation.

lem-sp-proper-open-staircase (ProperOpenStaircase.lean) is the proved fixed-staircase
calculation in steps 9–10, sourced from Tag 0F7K, lemma-pseudo-functor. It explicitly
transports the named boundary maps to literal composites before applying pasting.
Each node has its own source, full proof in words, exact Lean signature, and actual searches.
The file-level transparency options are recorded in
coord/changes/compactification-refinement-coherence-interface.md.
Existing theorem signatures and definitions are preserved.

## Second reading by Q5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
