## What changed

The original theorem `AlgebraicGeometry.Scheme.Modules.exists_chow_twist_finite_cohomology`
has a complete Lean proof, with its signature and visibility unchanged. Put
`p = π ≫ i`, form its closed projective graph over `X`, choose a twist with positive
higher images zero, prove coherence of its pushforward, and transport finite cohomology
through a base-linear Leray equivalence and `pushforwardComp`. Only proof imports were
added to the existing module; its public imports are unchanged.

Four new modules isolate the independent projective argument. The finite-type theorem
is proved: it constructs the projective embedding after restriction to each affine open,
uses degree-zero projective finiteness, identifies cohomology with sections, proves the
restriction map semilinear by naturality of `p.app`, and applies the existing affine
finite-type criterion. The other three statements isolate distinct parts of the argument.
The original node now records this route. No existing definition or statement changed,
no other existing module was adapted, and the blueprint unit's Chow/projective route stays.

## Proved and sorry left

One original hole closed, by declaration name:
`AlgebraicGeometry.Scheme.Modules.exists_chow_twist_finite_cohomology`.
The item module now contains no `sorry`.

Three holes added, each a public theorem with proof exactly `by sorry` in its own module:

- `AlgebraicGeometry.Scheme.Modules.finite_H_projective_affine_independent`
  (`lem-pc-m1-projective-affine-finite-cohomology-independent`): finite cohomology of a
  finitely presented quasi-coherent module on a specified projective model over an affine
  Noetherian base. It assumes neither high twisting nor vanishing nor a coherent pushforward.
- `AlgebraicGeometry.Scheme.Modules.exists_isZero_higherDirectImage_graph_twist`
  (`lem-pc-m1-projective-graph-twist-vanishing`): relative vanishing of the specified graph
  twist. It concludes neither coherence nor finite cohomology on the base.
- `AlgebraicGeometry.Scheme.Modules.nonempty_linearEquiv_H_pushforward_of_higherDirectImage_vanishing`
  (`lem-pc-m1-leray-acyclic-pushforward-linear-comparison`): the base-linear Leray comparison
  assuming positive higher-image vanishing, without properness, coherence, or finiteness.

Also proved, with no local hole:
`AlgebraicGeometry.Scheme.Modules.isFiniteType_projective_pushforward_independent`
(`lem-pc-m1-projective-pushforward-finite-type-independent`), and its private helper
`restrict_sections_smul`. This is a decomposition of the original hole into three
strictly partial statements, not a net sorry reduction or an axiom-free proof of the target.
The helper and main theorem still depend on the remaining public holes.

All five sandbox modules compile together. The remaining statements include empty-coordinate
cases in their proof descriptions; empty coordinates force the closed source empty.
The graph threshold uses a Noetherian, hence quasi-compact, base to obtain one bound.
The Leray result explicitly fixes both base-ring actions rather than merely asserting
an additive cohomology comparison. No data definition is made from an existence hole.

## No longer needed

The original file had no private proof imports to remove. During implementation, the direct
imports of `WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula` and
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel` were removed as redundant.
The restriction finite-presentation instance is imported directly from
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`.
ProjectionFormula remains available through the needed projective twisting-sheaf module;
this does not claim that it leaves the targets' import closure.

The old direct proof dependency `lem-pc-derived-direct-image-composition`, module
`Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded`, is not used: the
argument uses Leray for the single composite `p` and the ordinary pushforward isomorphism.
The old `lem-pc-relative-kill-by-twisting`, module
`Sheaf.AlgebraicGeometry.RelativeSerreVanishing`, is replaced by the independent graph
vanishing statement; its general proper-base-change route is unnecessary here.

`lem-pc-closed-immersion-coherent-cohomology` is no longer a direct step for `i` in the
main proof. It remains a planned ingredient of the independent projective finiteness
statement, so it is not globally pruned. The old projective cohomology finiteness and
Chow relative ampleness nodes likewise remain mathematical ingredients below the new
statements, not new imports of the main theorem. No unit statement or realized step is pruned.
Whether other targets still reach the removed nodes is the maintainer's closure calculation.

## Where the brief, the DAG or earlier work was wrong

Several originally proposed imports close library import cycles: projective cohomology
in `WeilConjectures.AlgebraicGeometry.Cohomology.Projective`, relative Serre vanishing,
and closed-immersion module finiteness already transitively import the assigned module.
The projective higher-direct-image finite-presentation argument also invokes general proper
coherence, which is the theorem being constructed. These are interface/import obstacles,
not objections to using statements whose proofs remain `sorry`. No unrelated module was
edited to bypass the cycles.

The existing projective finiteness interface is over `Spec A`; the needed statement is over
an arbitrary affine scheme with its displayed global-section action. The existing closed
immersion cohomology comparison uses a field in its available interface and does not supply
the required linear comparison over an arbitrary Noetherian ring. A general Leray comparison
with the exact two restricted actions is therefore stated separately. The graph ampleness
interface uses a fixed `ULift (Fin (m+1))` coordinate type and tensor pullbacks; the assigned
statement has an arbitrary finite coordinate type and ordinary pullbacks. The vanishing
statement records the necessary reindexing, pullback identification, and empty case.

The source citations were checked: projective finite cohomology is Tag 01YS,
Lemma 30.14.1 (3); relative Serre vanishing is Tag 02O1, Lemma 30.16.2; projective
pushforward coherence is Tag 02O4, Lemma 30.16.3. The assigned theorem's statement
was not disputed or weakened. LeanSearch was unavailable; LeanFinder and Mathlib-source
searches are recorded verbatim in every new node.

## New nodes

`lem-pc-m1-projective-affine-finite-cohomology-independent`, module
`Sheaf.AlgebraicGeometry.ProjectiveAffineFiniteCohomologyIndependent`: the independent
projective finite-cohomology step, from Tags 01YS and 01Y6. Its proof plan is the
standard-cover degree bound and descending induction using finite sums of twists;
it must not appeal to general proper coherence. One sorry remains.

`lem-pc-m1-projective-graph-twist-vanishing`, module
`Sheaf.AlgebraicGeometry.ProjectiveGraphTwistVanishing`: graph ampleness and relative
Serre vanishing for the exact integral twist of the assigned statement, from Tags
02O5 and 02O1. One sorry remains.

`lem-pc-m1-leray-acyclic-pushforward-linear-comparison`, module
`Sheaf.AlgebraicGeometry.LerayAcyclicPushforwardLinearComparison`: the scalar-compatible
collapsed Leray comparison, from Tag 01F4 (1) and naturality in Tag 01EY. One sorry remains.

`lem-pc-m1-projective-pushforward-finite-type-independent`, module
`Sheaf.AlgebraicGeometry.ProjectivePushforwardFiniteTypeIndependent`: finite type of
projective pushforward, from Tag 02O4, proved from the first new statement and existing
quasi-coherence and affine criteria. Its restriction and scalar glue are proved in Lean.
No change record is needed because no existing interface changed.

## Second reading by M1

1. Compared the delivered item module with the repository version. The theorem signature and all existing declarations are unchanged; only the proof and proof imports changed. Verdict: pass.
2. Compiled all five sandbox modules with `lcompile.py --all`; there are no errors, forbidden declarations, or remaining `sorry` in the item theorem. The three split-off statements retain documented `sorry`s and matching nodes. Verdict: pass.
3. Read each split-off statement and its node. The statements are strict partial steps (projective affine finiteness, graph-twist vanishing, and linear Leray comparison), with sources and proof descriptions, and are not restatements of the target. Verdict: pass.
4. Checked the proof route and imports. The proof uses the independent projective pushforward theorem, the graph vanishing theorem, and linear Leray comparison; no unit step is bypassed. Direct redundant imports were removed as recorded above. Verdict: pass.
5. Checked DAG `proof`, `proof_deps`, and `proof_origin` against the Lean route and verified all new nodes carry the required metadata. Verdict: pass.

I changed only this report section during second reading; no Lean statements or proofs required repair.
