## What changed
Proved `AlgebraicGeometry.Etale.nonempty_complexPullbackPresentation` by constructing all
fields from termwise pullback coherence and single-triangle transport. Applied transport
to diagram arrows and cone projections, then cancelled the given object isomorphisms.
The original theorem signature, all hypotheses, and conclusion are unchanged.

Added two new obligation modules with concrete helper definitions. Replaced the structure's
identity-law right-hand side by `presentationIdentityMap D i (F i)`, a transparent definition
of exactly its old right-hand side. Its explicit type avoids expensive inverse-image
unfolding. The profiler measured 26.7 seconds for the old identity-law projection alone;
the complete repaired parent compiles in 18.8 seconds. Explicit scheme arguments in the
cone transport application fix a constant-diagram inference mismatch. The helper is a
public statement dependency; the coherence theorem remains a proof import.
Updated the parent proof plan and the new nodes to agree with the Lean.

## Proved and sorry left
Proved the sole original sorry:
`AlgebraicGeometry.Etale.nonempty_complexPullbackPresentation`.
There is no sorry in the parent module. The proof is a reduction from exactly two named
obligations, each strictly a part of its argument:

- `AlgebraicGeometry.Etale.presentation_pullback_coherence`, node
  `lem-weil-pbc-etale-complex-pullback-coherence`.
- `AlgebraicGeometry.Etale.presentation_pullback_transport`, node
  `lem-weil-pbc-etale-complex-pullback-transport`.

This is a decomposition, not a completed axiom-free proof: one hole closed and two
holes added, for a local net of -1. These are the only new sorries. Both are public
named theorems with proof `:= by sorry`,
a source, and a complete proof in words. Every definition has concrete data.
The complete three-module set compiles. The unchanged direct caller
`Sheaf.AlgebraicGeometry.DerivedEtaleCohomologyLimit` compiles against the repaired parent
in 38.9 seconds, including its use of the identity-law projection. No downstream source
adaptation is required, since the field remains definitionally identical.

## No longer needed
Removed the parent's three direct proof imports:

- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.

The old direct proof-dependency nodes `def-weil-pbc-derived-inverse-image`,
`def-weil-pbc-etale-cohomology`, and `lem-weil-pbc-inverse-image-composition` are now
used through the split obligations rather than directly by the parent proof. They
remain transitively needed; `lem-weil-pbc-exact-functor-derived-factorization` stays
in the parent proof dependencies. No old dependency is silently discarded.

Also removed redundant direct public imports of ExactFunctor, Derived.LowerShriek, and
UpperLowerStar.Coherence from the new transport module: GlobalSections already publicly
imports them. These modules and the corresponding source dependency nodes remain needed
transitively, so no node is claimed globally pruned. The proof uses the two new obligations
and the exact-functor factorization; the existing unit sk-prop-h2 has no realized entries
for this node. No unit statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong
The previous reduction had never compiled as a complete parent. Profiling identified
expensive equality transport in the structure's identity law, rather than an infrastructure
failure. Giving that same comparison an explicit type repaired the cause for every caller.
The cone transport application also needed explicit X, Y, T to avoid inferring X through
the constant diagram. The geometry needs no cofilteredness or universal property of c;
transport needs no diagram, cocone, boundedness, or continuity. Identity triangles,
identity transitions and the zero complex satisfy the formulas, with no extra hypothesis.
The two intermediates do not repackage the parent's full conclusion: one states geometric
coherence only, and the other a commuting square for one triangle only.

## New nodes
`lem-weil-pbc-etale-complex-pullback-coherence` states the unit, associativity and cone
laws for the explicit termwise family. Its source is Stacks Tag 0GIT's termwise pullback
argument, expanded by inverse-image coherence.

`lem-weil-pbc-etale-complex-pullback-transport` states a commuting square for a single
triangle and representative q. Its source is the representative and canonical-map
identifications of Tags 0GIT and 0EZM. Naturality, localization comparisons and cancellation
give its proof. It also records the concrete comparison and representative helper definitions,
including `presentationIdentityMap`. Source searches found the ingredients; none found
an already assembled presentation or transport theorem.

Change record: `coord/changes/etale-complex-presentation-identity-comparison.md`.
It records the old and new field, semantic equivalence, all 170 downstream modules,
and validation of the direct projection caller. No target changes meaning.

## Second reading by C2
1. **Statements and interfaces.** Compared the delivered presentation module with the
repository version. The target theorem binders and conclusion are byte-for-byte unchanged.
The structure field has the same meaning: `presentationIdentityMap` expands to the old
identity comparison. The two new theorem statements are strict subclaims of the original
construction and introduce no extra assumptions beyond their displayed data. Verdict: pass.

2. **Proof validity.** Compiled all three delivered modules with `lcompile.py --all`.
The parent has no `sorry`; the only remaining holes are the two named public split theorems
`presentation_pullback_coherence` and `presentation_pullback_transport`, each with a
blueprint node and proof docstring. No forbidden declarations or hollow definitions occur.
Explicit scratch `#print axioms` checks show only `propext`, `Classical.choice`,
`Quot.sound`, and `sorryAx` for the parent and two split obligations; the identity
helper uses only the three permitted axioms. Verdict: pass, with decomposition recorded above.

3. **Search and pruning.** Checked the imported declarations and searched the local library
for existing coherence or transport results. An independent Loogle search for
`NatIso.mapHomologicalComplex` found only the lifting construction and component formulas.
`compatiblePullbackSheafSystem` has a preorder index hypothesis and supplies degreewise
ingredients but cannot directly cover the arbitrary small-category statement here.
The helper definitions are concrete and are
used by the parent proof. The three former direct proof imports are removed; no additional
node is claimed globally pruned because their declarations remain transitively required.
Verdict: pass.

4. **DAG agreement.** Read all three node files and matched their `lean` declarations,
proof steps, proof dependencies, and `proof_origin` to the delivered code. The unit record
has no realized entry for this item, so the route does not bypass a realized unit step.
Verdict: pass.

5. **Statement and source review.** Checked the source citations, edge cases (identity
arrows, constant diagram, and zero-degree complexes), and the identity-comparison change
record. The change is definitionally equivalent and its downstream projection caller was
compiled. Verdict: pass.

Changed during second reading: added this review section, explicitly classified the delivery
as a decomposition with one hole closed and two added, and named all former direct proof
dependencies in the pruning report. No Lean declarations or node statements were altered.
