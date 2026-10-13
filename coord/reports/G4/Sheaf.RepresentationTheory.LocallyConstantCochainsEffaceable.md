## What changed

Reduced `Rep.exists_locallyConstantCochains_effaceable` without changing its signature.
Added proof-only imports for homological-complex abelian lemmas and three modules, one for each separate part of the argument:
`LocallyConstantCochainsExact`, `LocallyConstantCochainsInvariantsZero`, and
`LocallyConstantCochainsAcyclicEmbedding`. The original public imports and statement remain intact.

The private, fully proved `Rep.exists_homology_deltaFunctor` constructs every field of the
cohomological delta-functor directly from Mathlib's homology sequence. Degreewise short exactness
gives short exact complexes, the connecting maps are `ShortExact.δ`, and the three exactness fields
are `homology_exact₂`, `homology_exact₃`, and `homology_exact₁`. The degree-zero monomorphism follows
from `mono_homologyMap_of_mono_of_not_rel` because no natural number precedes zero. Connecting-map
naturality is `HomologySequence.δ_naturality` applied to the functorial morphism of short complexes.

The new degree-zero module is fully proved: evaluation on the unique zero-tuple identifies
zero-degree cycles with invariants; the constant-cochain map is its inverse. These are actual
additive maps, their inverse equations are proved, and naturality follows from the coefficient
coordinate equation and `cyclesMap_i`. The final theorem rewrites the family of homology functors
and derives effacement from exactness of the acyclic target and `IsZero.eq_of_tgt`.

The blueprint unit `sk-thm-br` has no realized statement or step at this node; the original unit
route is unaffected. No definitions or existing statements were changed, and no modules belonging
to another item were adapted. All four modules compile without warnings using `lcompile.py --all`.

## Proved and sorry left

Closed the original hole in `Rep.exists_locallyConstantCochains_effaceable`
(node `lem-sc-locally-constant-cochains-effaceable`) by a decomposition, not an unconditional proof.
The item's module now has no `sorry`.

Also fully proved the new `Rep.locallyConstantCochains_invariants_zero`
(node `lem-sc-locally-constant-cochains-invariants-zero`) and the private assembly helper
`Rep.exists_homology_deltaFunctor`.

Added exactly two remaining holes:

- `Rep.exists_locallyConstantCochains_exact`
  (`lem-sc-locally-constant-cochains-exact`): complex construction, the two coordinate equations,
  additivity, and degreewise short exactness. This covers parent steps 1 and the lifting part of 2;
  it asserts neither a delta-functor nor a degree-zero comparison nor effacement.
- `Rep.locallyConstantCochains_acyclic_embedding`
  (`lem-sc-locally-constant-cochains-acyclic-embedding`): parent step 4, constructing a monomorphism
  into an object whose specified complex is exact at every positive degree. It applies to any
  complex with the coordinate formulas and has no delta-functor or invariants conclusion.

Each remaining proof is exactly `:= by sorry`, has a complete proof in words and the source in its
docstring, and has its own new module and DAG node. No data is defined by choosing an arbitrary
witness of a holed existence theorem. The complex theorem determines its complex up to the natural
coordinate isomorphism; all subsequent uses are within a proposition proof.

This closes one original hole and adds two lower holes: net hole count -1, a decomposition.
The two lower statements were checked on the trivial group, zero coefficients and degree one:
zero-degree functions are the coefficient module, the differential is action minus identity,
and the contraction includes the degree-one case. The acyclic embedding deliberately excludes
zero degree, where the coinduced representation can have nonzero invariants. Integer coefficients
are allowed throughout; no finiteness of the scalar ring is assumed.

## No longer needed

None of the original imports or proof-dependency nodes is pruned. The homology long exact sequence
and naturality nodes are now used through their Mathlib matches. The original discrete-category
node is used in the construction and acyclicity subproblems. The delta-functor definition is used
by the proved assembly helper.

The finite-scalar-ring modules `ContinuousCochainsDeltaFunctor`,
`ContinuousCochainsInvariantsZero`, `CoinducedDiscreteEmbedding`, and `CoinducedHomotopyIdentity`
are not imported: their hypotheses do not apply to the integers. They were not baseline
proof dependencies, so this is not a claim that those modules leave the targets' closure.

## Where the brief, the DAG or earlier work was wrong

The original plan supplies existing Mathlib declarations for the homology sequence and its
naturality, but its construction, degree-zero comparison and integer coinduction steps did not
have usable separate Lean declarations. Existing continuous-cochain/coinduction modules impose
`Finite` on the scalar ring. That restriction cannot be instantiated for `ℤ`; the new modules
state the corresponding parts for integer coefficients. This is an interface gap, not a claim
that the original theorem is false.

All three new nodes cite Tag 0DVG, like the parent, but are distinct statements: construction and
exactness, the degree-zero comparison, and positive-degree acyclic embeddings, respectively.
The parent includes all three plus the delta-functor fields and effacement. These nodes preserve
the agent-supplied profinite construction and contraction provenance of the parent's source;
they do not attribute that unpublished contraction proof to Stacks.

## New nodes

`lem-sc-locally-constant-cochains-exact` is parent steps 1 and the finite-lifting part of 2.
Its module is `Sheaf.RepresentationTheory.LocallyConstantCochainsExact`. It is the construction
and degreewise exactness task, with one remaining hole.

`lem-sc-locally-constant-cochains-invariants-zero` is parent step 3.
Its module is `Sheaf.RepresentationTheory.LocallyConstantCochainsInvariantsZero`.
It is fully proved and introduces no hole.

`lem-sc-locally-constant-cochains-acyclic-embedding` is parent step 4.
Its module is `Sheaf.RepresentationTheory.LocallyConstantCochainsAcyclicEmbedding`.
It is the coinduced acyclicity task, with one remaining hole.

All new nodes are under `sec-curve-estimates`, in unit `sk-thm-br`, with actual Mathlib searches
recorded by `msearch.py`. LeanSearch was unavailable; Lean Finder, Loogle and grep ran.
The parent node's proof, proof dependencies and proof provenance follow the written Lean proof.
No change record is required because existing definitions and signatures are unchanged.

## Second reading by G4

1. Compared the delivered item with the repository version. The theorem signature of
   `Rep.exists_locallyConstantCochains_effaceable` is byte-for-byte unchanged; only proof imports,
   a private helper, and the proof body were added. Verdict: passed.
2. Compiled all four delivered modules with `lcompile.py --all` and checked that the only remaining
   `sorry`s are the two named split theorems, with no forbidden declarations or `sorry` in definitions.
   Verdict: passed.
3. Reviewed the two split statements and their DAG nodes. Each is strictly below the parent, has a
   source and complete proof description, and is tested in the report on trivial and degree-one cases.
   The proved degree-zero statement has no remaining hole. Verdict: passed.
4. Checked the proof route against the available Mathlib homology-sequence declarations and stated
   dependencies. The private delta-functor assembly uses homology exactness and naturality directly;
   all original public imports remain needed for signatures or definitions. Verdict: passed.
5. Checked node metadata and the unit record. The parent proof dependencies list the three new nodes
   and the homology/delta-functor dependencies used by Lean; the new nodes are under the same chapter
   and unit, and the unit route is unchanged. Verdict: passed.

I corrected this missing required section and fixed three new-node title typos in their JSON records.
