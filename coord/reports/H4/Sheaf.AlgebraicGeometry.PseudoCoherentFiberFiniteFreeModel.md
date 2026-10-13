## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.exists_pseudoCoherent_fiber_finiteFree_model`
with a compiled proof combining a local bounded-above model with a bounded algebraic
replacement. Its signature and all public imports are unchanged.

Added `Sheaf.AlgebraicGeometry.BoundedFiniteFreeFiberModel` with a complete proof of
`AlgebraicGeometry.Scheme.exists_bounded_finiteFree_fiber_model`. The proof constructs
an actual stupid truncation, proves boundedness and finite freeness, and builds the
three-term short-complex isomorphism after extending scalars. It takes finrank of the
induced homology isomorphism. No arbitrary data is defined from an unproved existence.

Added `Sheaf.AlgebraicGeometry.PseudoCoherentFiberBoundedAboveModel` for the remaining
local affine and derived-fibre transport. The target imports these two modules privately. The bounded-above module privately
imports the affine-lift and flat-pullback modules named by its proof plan.
Updated the target node and added matching nodes for both intermediate declarations.
The blueprint unit route is retained: these are lower-level pieces of the original proof.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.exists_pseudoCoherent_fiber_finiteFree_model`
(node `lem-sc-pseudo-coherent-fiber-finite-free-model`) by decomposition.

Proved `AlgebraicGeometry.Scheme.exists_bounded_finiteFree_fiber_model`
(node `lem-sc-bounded-finite-free-fiber-model`) completely, without sorry.
The stupid truncation argument works for arbitrary integer bounds, zero terms, an
upper bound below the truncation cut, and the zero ring. The proof needs no separate
nonempty-prime-spectrum or finite-dimensionality hypothesis.

One new hole remains:
`AlgebraicGeometry.Scheme.exists_pseudoCoherent_fiber_boundedAbove_model`
(node `lem-sc-pseudo-coherent-fiber-bounded-above-model`). Its statement supplies only
a bounded-above complex; the boundedness and truncation step are proved separately.
It follows the source's affine model argument and computes all fibre degrees with
one complex. Its docstring and node give the complete remaining mathematical argument.

Thus one original hole is closed, one hole is added, and none remains directly in
the target module. This is a decomposition, not an axiom-free proof of the target.
All three modules compile with no errors or style warnings; the dry run checks axioms.

## No longer needed

Removed the target module's direct proof imports of
`Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback` and
`Sheaf.AlgebraicGeometry.AffineFiniteFreeSheafComplexLift`.
Their nodes `lem-pc-flat-complex-derived-pullback` and
`lem-pc-affine-finite-free-sheaf-complex-lift` remain required by the remaining
bounded-above model argument; these modules are not mathematically pruned.
The same is true of `def-pur-pseudo-coherent-complex` and `def-sc-derived-fiber-betti`:
they moved to the lower node's plan rather than becoming unnecessary.
No node or module is claimed globally unnecessary.

## Where the brief, the DAG or earlier work was wrong

The two existing proof-dependency declarations do not themselves express transport
from a localized open site to an affine open subscheme or the scalar identification
between derived residue fibres and algebraic residue-field homology. The existing
affine lift starts with an already transported sheaf complex. These interfaces
therefore leave substantial glue; it is isolated in the bounded-above model node.

Mathlib's `truncGE` is canonical truncation, whose boundary term is opcycles and need
not be free. The construction here uses `stupidTrunc`, preserving finite freeness.
Its term isomorphisms, rather than a global quasi-isomorphism, suffice for degree i.
The source is Stacks Tag 0BDI's affine reduction and stupid truncation argument.
LeanSearch was tried twice and was unavailable (HTTP Internal Server Error);
LeanFinder, Loogle and source grep supplied component results but no exact replacement.

## New nodes

`lem-sc-pseudo-coherent-fiber-bounded-above-model`:
`Sheaf.AlgebraicGeometry.PseudoCoherentFiberBoundedAboveModel`, the remaining local
finite-free affine representative and derived-fibre identification, without a lower bound.

`lem-sc-bounded-finite-free-fiber-model`:
`Sheaf.AlgebraicGeometry.BoundedFiniteFreeFiberModel`, the fully proved algebraic
stupid-truncation step. It is independent of schemes and pseudo-coherence.

No definitions, existing statements or visibility changed; no change record is needed.

## Second reading by H4

1. Compared the delivered target module and its node with the repository by diff.
   The original signature had two whitespace changes, which I restored. Its theorem
   signature is now byte for byte identical, and its public imports, universes,
   instances and docstring are unchanged. There are no definitions or change records
   in this delivery. The two other modules are new.

2. Compiled all three modules in dependency order through lcompile.py, without errors
   or style warnings. Scanned every delivered Lean file for forbidden declarations
   and kernel-check bypasses: none. The only sorry is the named theorem
   exists_pseudoCoherent_fiber_boundedAbove_model, listed above. Scratch #print axioms
   checks give only propext, Classical.choice and Quot.sound for the algebraic
   truncation theorem; the target and the open model also have sorryAx. The actual
   complex K is F.stupidTrunc, not a definition choosing data from an unproved theorem.

3. Read the new statements, proofs, docstrings and nodes against Stacks
   [0BDI](https://stacks.math.columbia.edu/tag/0BDI) and
   [08E7](https://stacks.math.columbia.edu/tag/08E7).
   The open theorem separates the affine bounded-above representative and all-degree
   fibre computation from the proved fixed-degree truncation. It is true locally:
   choose an affine open inside the pseudo-coherent neighbourhood, transport its
   finite-free complex, then compute derived residue pullback on that flat complex.
   The same representative works for all degrees; it has no lower bound.
   Its docstring includes the restriction, affine lift, one-point evaluation and
   residue scalar identifications still to formalize. This is not the original
   bounded-model statement under another name: boundedness and preservation of
   degree-i tensor homology are supplied by the fully proved second component.
   Checked zero terms, rank zero, negative i, upper bound b < i-1, and empty
   spectrum for the algebraic theorem; the scheme-local theorem requires x, so an
   empty scheme makes it vacuous. No quasi-separatedness or residue-map flatness
   is assumed. Independent LeanFinder and Loogle searches, and source grep under
   both Lean roots, found no exact replacement. AffinePseudoCoherentLift returns
   sheaf models with additional hypotheses; KFlatStalkResidueCohomology requires
   an already global representative. Neither closes the remaining local transports
   in a few minutes. Added this search evidence to the two new nodes.

4. Read the proof from the target down. It composes the model equality with the
   truncation equality at e(z). The algebraic proof preserves the three terms and
   both differentials, applies extension of scalars, builds ShortComplex.isoMk,
   and uses homologyMapIso and finrank_eq. No exact existing theorem shortens this
   route. StupidTrunc is a private proof import; the other public imports provide
   signature types or their required instances. The two removed target proof imports
   remain dependencies of the open model, so I restored them as private imports
   there. All four old proof_deps are accounted for under No longer needed, with
   none claimed globally pruned. Read sk-prop-av-cube.json: its realized statement
   and step arrays are currently empty; this delivery does not change that record
   or its general-cube route. The local affine/truncation split is below that route.

5. Checked each Lean signature against its node's lean.statement, both new nodes'
   chapter/unit, source, created, blueprint and search records, and every proof step
   against its proof_deps. The original node now names exactly the two results
   applied in the target. The bounded node follows the concrete Lean construction;
   the open node retains the original affine-lift and flat-pullback dependencies.
   Their imports now match that plan. The original node changes only proof,
   proof_deps and proof_origin. Verdict: valid decomposition, zero net holes closed;
   the algebraic truncation component is completely proved, one local-model hole
   remains, and no module is globally pruned.

Second reading changed signature whitespace, the open model's two private dependency
imports, and new-node search records. No mathematical statement or proof was changed.
