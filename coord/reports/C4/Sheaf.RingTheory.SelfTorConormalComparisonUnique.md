## What changed

Proved AlgebraicGeometry.selfTorConormalComparison_unique in
Sheaf.RingTheory.SelfTorConormalComparisonUnique without changing its signature,
visibility, or public import. Added a fully proved private helper
exists_koszul_conormal_test_data in the same module: it constructs the normalized
Koszul chain-map lift and the standard top-wedge cycle. Proof-only imports are
Sheaf.RingTheory.KoszulGeneratorChainMap and
Mathlib.LinearAlgebra.ExteriorPower.Basis. The former supplies the already proved
ExteriorAlgebra.boundary_wedge; the latter supplies finite-free exterior bases.
Updated the existing node's proof, proof_deps and proof_origin to match this route.

The helper follows Stacks Tag 00LS (1) using projective factorization, exactness
and ChainComplex.mkHom. It uses no regularity or assumption that g generates I.
It proves all quotient tensor differentials zero by the contraction formula and
span induction, then uses iCyclesIso to construct the cycle. The main proof
cancels the resolution isomorphism on each lifted conormal wedge and extends
by span induction; each quotient scalar is lifted to A before using A-linearity.
No arbitrary witness from an unproved existence theorem is used in a definition.
The empty tuple, I=A, I=0 and the zero ring are included in the construction.

## Proved and sorry left

Closed the sole original hole:
AlgebraicGeometry.selfTorConormalComparison_unique
(new-r4-self-tor-conormal-comparison-unique).
The new private helper is fully proved. No sorry remains in the assigned module;
no hole was added or split off. This is a proof, not a decomposition.

## No longer needed

None: the original public predicate import is retained. The original node had
no proof-dependency imports or named planned dependency nodes to prune. Neither
SelfTorConormalComparisonExistence nor any regular-sequence resolution or
conormal-basis theorem is used. No claim is made that these modules leave the
whole target closure, since other theorems can still need them.

## Where the brief, the DAG or earlier work was wrong

The original DAG first step gave the degreewise lift with uses=[] and
elementary=false. Its missing argument is now fully formalized locally using
Mathlib's projective lifting API. The contraction formula is reused from the
existing generator-chain-map module, rather than introducing another formula.
The blueprint unit's realized statement/steps are empty; no unit route is bypassed.

At first the last green compiled library still exposed the foundational
conormal declarations from their former parent module and lacked the new
SelfTorConormalComparisonPredicate and ConormalExteriorModule artifacts.
The complete proof compiled cleanly in 4.5 seconds against the last green
build using the formerly public parent definitions. Its #print axioms output
was exactly propext, Classical.choice, Quot.sound. The delivery dry run
failed at local compilation with "object file .../SelfTorConormalComparisonPredicate.olean
of module Sheaf.RingTheory.SelfTorConormalComparisonPredicate does not exist".

Proof development in scratchpad used the existing public parent definitions;
the delivery retains the assigned predicate import and needs final compilation
against the refreshed build. Scratchpad files are not delivery files.

The pending global batch compiled successfully but was marked red at
2026-10-13T20:45:20Z: its axiom/sorry probe failed on an existing duplicate
symmetric-category instance between Sheaf.Paper.ModuleCupKInjectiveTarget and
Sheaf.Paper.GlobalTensorPullbackMonoidalNormalization, affecting unrelated
cup-product modules. Consequently the new predicate artifact was not published.
This is outside the assigned module and no forced adaptation in this delivery
could repair those files.

Change record: `coord/changes/selfTorConormalComparisonUnique-proof-imports.md`.

## Earlier second reading (a previous round; superseded)

Pending the independent second reader. The module compiles with the direct
predicate import and the proof uses only the existing Koszul generator-chain
map theorem plus Mathlib exterior-basis APIs. The target signature is unchanged,
and no new sorry or node was introduced.

## Second reading by C4

1. PASS. Compared the delivered module with the repository version using diff;
   the sole existing theorem signature is byte for byte identical. Its docstring,
   visibility and public predicate import are unchanged. No existing definition,
   target statement or consumer is edited. The added theorem is private.
2. PASS. Compiled the delivered module using lcompile.py against the refreshed
   green library: clean, 5.6 seconds. The axiom audit of
   AlgebraicGeometry.selfTorConormalComparison_unique reports exactly propext,
   Classical.choice and Quot.sound. The private helper is used by that theorem,
   so this also audits its dependencies. There are no sorry declarations or
   forbidden constructs, and no new definition or arbitrary unproved witness.
   The historical missing-predicate artifact blocker recorded above is resolved.
3. PASS. Nothing was split off; zero new holes or nodes. Read the fully proved
   helper: its free-term projective lifting and zero quotient differentials
   require neither regularity nor generation of I. Checked degree zero (empty
   wedge and zero outgoing differential), I=0, I=A and the zero ring. All are
   covered without nonzero or positive-rank assumptions.
4. PASS. Read the proof from the normalization predicate downward and searched
   lean/Sheaf and lean/WeilConjectures for alternate Koszul lifts and comparison
   uniqueness, plus Mathlib via msearch.py grep for exterior generation and
   lifting APIs. No existing theorem removes the normalization-test construction.
   Existing comparison/basis results require regular sequences and cannot replace
   it here. Both new imports are private and used: boundary_wedge and the exterior
   basis. The original proof_deps was empty, so No longer needed is complete.
   The unit sk-thm-picard-duality has empty realized statement and step lists;
   this local proof bypasses no realized unit node.
5. PASS. Compared the old and delivered node. Only proof, proof_deps and
   proof_origin change; the contraction node new-q2-koszul-generator-chain-map
   is the sole named library proof dependency. The lifting, quotient-tensor
   calculation and wedge-generation steps match the Lean proof.

Second-reading changes: removed the diagnostic #print axioms command from the
production module after verifying its output; replaced abbreviated Old/New
signatures and the vague downstream-users row in the proof-import change record
with the complete unchanged signature and sole direct importer. No mathematical
proof edits were necessary. Closed selfTorConormalComparison_unique (one of one
original holes); added zero holes and split off zero statements; pruned none.
