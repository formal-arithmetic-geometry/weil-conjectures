## What changed

Replaced the sole sorry in
`AlgebraicGeometry.Scheme.strictlyPerfect_relativeTensor_stalk_bound` by a complete
Lean reduction, preserving its signature and visibility. The proof explicitly
constructs the open stalk complex of L, maps its degree bounds and finite-free
retractions through the stalk functor, and proves every resulting term projective.
It then applies an algebraic Tor-amplitude bound and the comparison between local
model tensor homology and the prescribed K-flat sheaf tensor. The two cases of the
interval complement are closed using the derived t-structure, preservation of zero
objects by forgetting module structure, and transport through an isomorphism.

Added two public intermediate statements in separate modules, with two DAG nodes,
and updated only the original node's proof, proof_deps and proof_origin.
The new proof imports are `Sheaf.AlgebraicGeometry.OpenModuleStalkFreeProjective`,
`Sheaf.Algebra.Homology.BoundedProjectiveRestrictionTorAmplitude`, and
`Sheaf.AlgebraicGeometry.RelativeTensorStalkLocalModelHomology`.
No existing interface, target statement, definition, or other holder's module changed.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.strictlyPerfect_relativeTensor_stalk_bound`
(node `lem-pc-strictly-perfect-relative-tensor-stalk-bound`). Its proof has no holes.
The stalk degree bounds and projectivity of every stalk term are proved directly.

Added and left with exactly `:= by sorry`:

- `CochainComplex.boundedProjective_restriction_torAmplitude`
  (`lem-pc-bounded-projective-restriction-tor-amplitude`).
- `AlgebraicGeometry.Scheme.relativeTensor_stalk_localModel_homology_iso`
  (`lem-pc-relative-tensor-stalk-local-model-homology`).

This is a decomposition: one upper hole closed, two strictly smaller lower holes
added, net minus one before any pruning. It is not a sorry-free proof of the original
mathematical theorem. The algebraic statement involves no sheaves or local derived
representative; the comparison involves no perfectness, degree bounds or Tor bound.
Neither restates the original statement.

All three modules compile together in import order with lcompile.py, without errors
or warnings. The main proof works with the standard module derived-category instance,
so it adds no derived-category assumption to the original signature.

Edge cases checked mathematically: if r>s all terms vanish, so all tensor homology
vanishes; d=0 yields [r,s]; a single projective term gives its shifted Tor interval;
zero rings, zero complexes and rank-zero free modules are covered. The comparison
uses the same transported stalk module in all degrees and is valid for unbounded
or acyclic L. Its module witness is used only in a proof of a proposition, never
chosen to define data.

## No longer needed

Second reading removed the redundant baseline import
`Mathlib.Topology.Sheaves.Abelian` from the main module. Its required stalk
interfaces remain available through the statement imports. The other baseline
public imports support the unchanged statement, including the projective-resolution
instance needed to elaborate its Tor hypothesis. During development the new modules' unnecessary import of
`WeilConjectures.CategoryTheory.DerivedCategory.FlatModel` was replaced by the
smaller derived-monoidal and Tor-amplitude interfaces; the comparison's unnecessary
`Sheaf.AlgebraicGeometry.PerfectComplex` import was replaced by `DerivedCategory`.
These were development imports, not baseline pruning.

The old direct proof dependencies `def-pc-kflat-complex`,
`def-pc-quasi-iso-modules`, `lem-pc-kflat-resolution`,
`lem-pc-kflat-stalk-criterion`, `lem-pc-kflat-tensor-quasi-iso`,
`lem-weil-pbc-module-stalk-exact`, and `lem-pc-stalk-tensor-complex` are now below
(or statement dependencies of) the comparison node; they are still needed for
that argument. `def-pc-perfect-complex` remains directly used. No existing node
or module is claimed globally pruned. The unit's realized statement and steps
were not bypassed or changed.

## Where the brief, the DAG or earlier work was wrong

The two numbered original steps contain substantial algebra and comparison glue,
but their listed declarations alone do not state either combined step. The first
step can nonetheless be partially proved now: the explicit open stalk functor and
existing projectivity theorem give the bounded projective stalk complex directly.
The remaining independent pieces are stated in the two new nodes.

Tag 064L is tensor invariance for K-flat quasi-isomorphisms, rather than the
bounded-complex amplitude lemma. The algebraic node cites the directly relevant
Stacks Tags 066H, 066K and 0655, read online, in addition to the original 0B6G
verification. Tags 06YB, 08CG and 09U9 were also read online. The checkout lacks
the corresponding literature tex files; no project literature file was modified.

Mathlib searches were actually run through msearch.py and are in searches.jsonl.
LeanSearch returned Internal Server Error and is recorded unavailable; LeanFinder
returned t-structure, projective Tor, and flat tensor component lemmas, with no
exact match. Loogle did not know Tor'; targeted Mathlib grep found stalk exactness
but no full comparison. Library and blueprint searches found no exact duplicate.

## New nodes

`lem-pc-bounded-projective-restriction-tor-amplitude`, in
`lean/Sheaf/Algebra/Homology/BoundedProjectiveRestrictionTorAmplitude.lean`,
is the algebraic amplitude part of original step 1. Its proof plan uses a free
resolution of the test module, a bounded horizontal double complex, projective
column exactness, and finite spectral-sequence convergence. It is sourced to
Stacks Tags 066H and 066K; no scheme, strict-perfectness or K-flat sheaf comparison
is hidden in its conclusion.

`lem-pc-relative-tensor-stalk-local-model-homology`, in
`lean/Sheaf/AlgebraicGeometry/RelativeTensorStalkLocalModelHomology.lean`,
is original step 2 with all amplitude information removed. Its conclusion is an
actual homology isomorphism, retaining the real stalk scalar map and the actual
open-module stalk functor. Its complete proof sketch records inverse-image scalar
transport, local derived localization, K-flat tensor computation, and the two
stalk commutations. Both nodes retain chapter sec-picard-framework and unit
sk-thm-picard-duality, with blueprint ancestry lem-sc-finite-duality.

Second reading added the import-only change record
`coord/changes/StrictlyPerfectRelativeTensorStalkBound-imports.md`; no forced
adaptation is required.


## Second reading by H3

1. Compared the main module with the repository by `diff -u`. The only changes
   are the proof and imports; its existing declaration signature and docstring
   are byte-for-byte unchanged. There are no changed definitions or other
   existing declarations and no forced adaptations. An import-only change record
   documents removal of the redundant baseline public import.
   Verdict: pass.

2. Compiled all three delivered modules in import order with lcompile.py.
   Independently compiled scratch copies with `#print axioms` for each of the
   three declarations. Each lists exactly propext, Classical.choice, Quot.sound
   and sorryAx. The main proof contains no sorry; only the two named split
   theorems have `:= by sorry`. No forbidden declarations, attributes, or hollow
   definitions occur. The proof's complex C is explicitly the image of L;
   the comparison's existential M is eliminated only inside a proposition proof
   and never supplies definition data. Verdict: pass as a decomposition, not
   an axiom-clean mathematical proof.

3. Read both split signatures, docstrings and complete node records. Verified
   the amplitude argument against [Stacks 066K](https://stacks.math.columbia.edu/tag/066K)
   and [066H](https://stacks.math.columbia.edu/tag/066H), and the stalk K-flat
   comparison against [06YB](https://stacks.math.columbia.edu/tag/06YB).
   Checked the reversed interval, zero rings/modules, d=0 and single-degree
   complexes; the finite horizontal filtration remains convergent even for an
   unbounded free resolution. The comparison needs neither degree bounds nor
   projectivity, and uses a single transported stalk M in every degree.
   The amplitude lemma has no scheme or comparison hypotheses. Each is a
   genuine independent part of the original argument, not a restatement.
   Repeated LeanFinder, Loogle and targeted Mathlib/library/upstream searches
   with alternative terminology; no exact replacement was found. Loogle did
   not recognize the queried identifier. The available Tor/projective and
   localization lemmas supply components but do not close these statements
   in a few minutes. Verdict: pass; both lower holes remain.

4. Read the reduction from its conclusion downward: the existing projective
   stalk lemma proves projectivity using an explicit mapped retraction; the
   algebraic amplitude supplies the two t-structure bounds; homology vanishing,
   forgetting scalars and the comparison iso transfer zero to the required
   stalk. The three new proof dependencies are plain imports. Removed the
   redundant direct import Mathlib.Topology.Sheaves.Abelian and recompiled.
   Tested removing ModuleCat.Projective, but it is required publicly for the
   HasProjectiveResolutions instance in the original Tor hypothesis, so retained
   it. All seven old proof dependencies omitted from the new proof_deps are
   accounted for under No longer needed; none is claimed globally pruned.
   The unit record has empty realized lists; no realized statement or step is
   bypassed, and the unit/chapter records stay unchanged. Verdict: pass.

5. Checked each Lean signature against its node lean.statement and each new
   node's required source, proof steps, searches, status, ancestry, created and
   lean fields. Compared the original node JSON: only proof, proof_deps and
   proof_origin change. The union of step uses equals proof_deps. The explicit
   stalk construction and both reductions agree with the revised proof plan.
   Verdict: pass.

Second-reading changes: removed the redundant main-module public import
Mathlib.Topology.Sheaves.Abelian and updated the pruning/report evidence.
No proof body, declaration signature, definition, node statement or unit changed.
One original hole is closed and two lower holes are added: net minus one hole;
no globally pruned module is claimed.

The delivery dry run required a change record for that public-import removal;
added coord/changes/StrictlyPerfectRelativeTensorStalkBound-imports.md. The sole
direct importer already publicly imports Mathlib.Topology.Sheaves.Abelian and
imports this item privately, so its interface and all transitive users stay
unchanged. The record lists the full source-only downstream set.

The unchanged direct importer PerfectRelativeTensorLocallyBounded compiled
against the delivered overlay in 12.9 s, without errors or warnings.
