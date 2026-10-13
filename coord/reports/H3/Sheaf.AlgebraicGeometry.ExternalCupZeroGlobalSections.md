## What changed

Reduced externalCup_zero_globalSections to internal degree-zero cup compatibility
and degree-zero pullback compatibility. The proof unfolds externalCup, rewrites
with the internal cup formula and both projection pullback formulas, and closes
by reflexivity. Two new statement modules and their nodes supply the two parts.
No existing signature or definition changes. Repaired the saved internal cup
statement by opening CategoryTheory.MonoidalCategory so F ⊗ G denotes the
categorical tensor rather than the tensor product of types.

## Proved and sorry left

Closed the one original hole:
AlgebraicGeometry.Scheme.Modules.externalCup_zero_globalSections
(lem-sc-external-cup-zero-global-sections).

Added two holes, each in a separate module:

- AlgebraicGeometry.Scheme.Modules.scalarCohomologyCup_zero_globalSections
  (lem-sc-scalar-cup-zero-global-sections).
- AlgebraicGeometry.Scheme.Modules.scalarCohomologyPullback_zero_globalSections
  (lem-sc-scalar-pullback-zero-global-sections).

This is a decomposition, not a net reduction in holes. Each lower statement is
strictly a part of the original argument: internal cup evaluation on one scheme,
and pullback evaluation along one morphism. Neither restates the external cup
formula. Zero sections, zero coefficients and empty schemes require no added
hypotheses. lcompile.py --all compiled all three modules successfully on
2026-10-13; the external cup proof contains no sorry. The two named lower
statements remain exactly by sorry, with sources and proof explanations.

## No longer needed

None. The public comparison import is needed for the statements and definitions;
the two proof-only imports supply the two necessary compatibility formulas.
No original dependency is pruned. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The plan names definition nodes but did not separately state the internal cup
and pullback evaluation formulas; the two new nodes isolate these calculations.
The saved draft failed to open CategoryTheory.MonoidalCategory, causing Lean to
interpret F ⊗ G as a tensor product of types. This is repaired and the complete
reduction now compiles.

The earlier missing-source blocker is resolved in the current read-only checkout.
Both the assigned original module and ScalarGlobalSectionsComparison source are present.

## New nodes

lem-sc-scalar-cup-zero-global-sections states internal cup compatibility with
global sections, from Stacks Tags 01DZ, 01F7 and 0FKV. Its docstring gives the
resolution/Ext and tensor-coefficient calculation. Searches in the saved node
found general cochain and Ext tools rather than this scalar comparison formula.

lem-sc-scalar-pullback-zero-global-sections states pullback compatibility with
the tensor-pullback unit on top sections, from Stacks Tags 01DZ, 01F7 and 0096.
Its docstring gives the constant-unit adjunction and coefficient calculation.
The saved searches found generic pullback tools rather than this formula.

## Second reading by H3

1. Compared the delivered external-cup module with the repository using diff.
   Its existing signature and docstring are byte for byte unchanged; only two
   plain proof imports and the proof body differ. No definition or statement
   change, and no change record is needed. The two new modules contain the two
   reported new statements only. Verdict: pass.
2. Compiled all three modules locally with lcompile.py --all, then compiled a
   scratch copy with #print axioms for all three declarations. Only propext,
   Classical.choice, Quot.sound and sorryAx occur. The external theorem has no
   sorry; each new theorem has exactly its named by-sorry proof. No definitions
   or forbidden declarations are added. Verdict: pass as a decomposition,
   closing one original hole and adding two, net minus one hole closed.
3. Read the defining scalar comparison, cup, pullback, tensor coefficient and
   section maps. Each residual is the corresponding degree-zero evaluation
   identity, strictly part of the original external calculation. Zero inputs
   evaluate to zero by additivity; zero coefficient sheaves and empty schemes
   have singleton section and degree-zero groups; identity pullback evaluates
   to the adjunction unit. No extra hypothesis is needed. Repeated leanfinder,
   loogle and grep searches with different queries: generic unitHomEquiv and
   Ext.mapExactFunctor_mk₀ tools exist, but no complete matching statement.
   The resolution comparison calculation is substantial, not a few-minute
   application. Sources and full prose arguments are present. Checked Stacks
   https://stacks.math.columbia.edu/tag/01DZ (derived cohomology),
   https://stacks.math.columbia.edu/tag/01F7 (functoriality), and
   https://stacks.math.columbia.edu/tag/0FKV (cup compatibility).
   Verdict: pass; neither residual merely renames the external theorem.
4. The proof unfolds externalCup, rewrites internal cup once and projection
   pullback twice, then reduces the tensor lift on a pure tensor by reflexivity.
   No shorter complete library lemma was found. All three imports are needed;
   only ScalarGlobalSectionsComparison is public, as required by the signatures.
   The original proof_deps are retained. Read sk-prop-av-cube.json: its current
   realized statement and step arrays are empty; this delivery changes neither
   them nor the unit route. No pruning is claimed. Verdict: pass.
5. Read all three nodes against the Lean: the external proof uses exactly the
   two new residual nodes and the original definition nodes. New nodes have
   source, proof steps, dependencies, origin, searches, creation, blueprint,
   chapter, unit and verbatim Lean statements. Verdict: pass after repair.

Changed: restored the existing external node's current review records rather
than overwriting them with stale saved records; retained only its permitted
proof, proof_deps and proof_origin changes. Updated the new cup docstring and
node proof to describe exists_scalarTensorCoefficient as the evaluation theorem
it currently is. Added independent searches to both new nodes and removed the
obsolete missing-source blocker from this report. No Lean proof was rewritten.
