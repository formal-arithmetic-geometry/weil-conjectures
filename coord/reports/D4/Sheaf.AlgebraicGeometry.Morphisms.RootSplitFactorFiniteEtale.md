## What changed

Proved `AlgebraicGeometry.Scheme.root_split_factor_finite_etale` in
`Sheaf.AlgebraicGeometry.Morphisms.RootSplitFactorFiniteEtale`, with its original
signature and public imports unchanged. Added four proof-only imports:
`Sheaf.AlgebraicGeometry.Morphisms.RootSplitAwayCoverEtale`,
`Sheaf.AlgebraicGeometry.Morphisms.RootSplitAwayCoverPoint`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Finite`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FlatDescent`.

The proof constructs the factor map V -> D(g) using the open immersion's lift,
proves it etale and surjective using the two existing root-cover lemmas, and gets
quasi-compactness from affineness of both basic opens. It identifies the original
pullback as a pullback over D(g) via `PullbackCone.isLimitOfFactors`, transports the
finite etale coproduct fold along delta, and applies singleton fpqc descent.
Updated the existing node's proof, proof_deps and proof_origin to match this proof.

Read the existing root-cover modules and nodes, the unit record
`sk-prop-input-spreading`, and Stacks
[02LA](https://stacks.math.columbia.edu/tag/02LA) and
[02VN](https://stacks.math.columbia.edu/tag/02VN).
The unit route is preserved: this implements the existing finite-etale descent
step in the trait-case root-chart argument.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.Scheme.root_split_factor_finite_etale`
(node `lem-sbc-root-split-factor-finite-etale`). One of one sorries proved;
zero sorries added, zero split off, and none remain in the delivered module.
Both imported root-cover lemmas already have complete proofs. The source-library
finite coproduct and finite-descent declarations also have complete proofs.

The file compiles with `lcompile.py`. The proof treats d=0 by the finite coproduct
instance; empty D(g) by vacuous pointwise surjectivity; n=1 by the existing root
lemmas. No nontriviality, regularity, or divisor hypothesis is introduced.

## No longer needed

No imports removed and no existing dependency nodes or modules pruned: the
original node had no proof dependencies and the module had only statement imports.
The proof does not need to prove finiteness of V -> D(g), its finite-free rank,
or a new root-algebra construction: the existing etaleness and point-lifting
results, and affine basic opens, give precisely the descent hypotheses.

## Where the brief, the DAG or earlier work was wrong

The original node's single proof step had no recorded proof dependencies despite
using the punctured-root calculation. Its proof now records the existing root
etaleness and point-lifting nodes and the complete categorical assembly. The
original statement is valid and unchanged. The recently landed root modules were
initially absent from the published compiled build; compilation succeeded after
they became available. No tool workaround, interface change, or forced adaptation
was needed.

## Second reading by D4

1. Compared the delivered module and node with their repository versions using
   `diff -u`. The existing theorem signature is byte-for-byte unchanged, as are
   its docstring, public visibility, and four public statement imports. The only
   Lean changes are four plain proof imports and replacement of the sole sorry
   by a proof. There are no definitions, interface changes, or forced adaptations.
   Verdict: pass.
2. Independently compiled the delivered file with `lcompile.py`: no errors or
   warnings. Compiled a scratch copy with `#print axioms
   AlgebraicGeometry.Scheme.root_split_factor_finite_etale`: exactly `propext`,
   `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Read the entire proof:
   the constructed lift factors the root map through D(g); etaleness cancels the
   open immersion; the point lemma supplies surjectivity; affine basic opens
   supply quasi-compactness. The pullback-factor lemma and the supplied equation
   for delta give finite etale second projection, and fpqc descent gives the
   claimed properties of j. No sorry, forbidden declaration, or arbitrary data
   chosen from an unproved existence theorem occurs. Verdict: pass.
3. No statements were split off and no new declarations or nodes were added.
   Independently checked the imported root-cover proofs, finite coproduct proof,
   and finite descent proof. The final axiom check also verifies that none of
   their proof dependencies introduces an unfinished theorem. The empty basic
   open, zero ring, d=0 and n=1 introduce no extra assumption: point lifting is
   used only on existing points, and finite coproduct stability includes the
   empty index type. Verdict: pass.
4. Checked for a shorter existing route with a fresh Loogle search for
   `"IsFinite", "DescendsAlong"`, and local searches of Mathlib and both library
   roots. Mathlib provides etale descent; the source library supplies finite
   descent and finite coproduct stability, exactly as used here. The nearby
   finite-etale descent theorem concerns a different Noetherian local setting
   and cannot replace this argument. All four added proof imports supply used
   declarations or instances; all existing public imports serve the statement.
   The original proof_deps was empty, so the No longer needed list is complete.
   Read sk-prop-input-spreading, including its realized field: this proves a
   subordinate root-chart descent step within the trait-case route and bypasses
   none of the unit's steps. Verdict: pass.
5. Compared the existing node's changed fields and read both dependency nodes.
   Only proof, proof_deps and proof_origin changed. The two root-cover dependency
   nodes match the two explicit theorem applications; the remaining steps use
   the named Mathlib or proved source-library constructions and descent tools.
   The proof_origin describes the route actually compiled. The statement and
   lean record remain unchanged. Verdict: pass.

Second reading changed only this report, adding the independent checks above.
No repair to the Lean proof or node was needed. Confirmed accounting: one hole
closed, zero holes added, zero split off, and no imports or modules pruned.
