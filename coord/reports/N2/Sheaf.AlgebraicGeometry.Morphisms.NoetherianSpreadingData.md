## What changed

Replaced the single hole in
`Sheaf.AlgebraicGeometry.Morphisms.NoetherianSpreadingData` by a complete Lean proof
combining two strictly smaller, independently stated steps of the limit reduction.
The signature, universes, existing declarations, and six public imports are unchanged.
Two proof-only imports were added:
`Sheaf.AlgebraicGeometry.Morphisms.NormalFamilyGenericLimit` and
`Sheaf.AlgebraicGeometry.Morphisms.PointedGaloisCoverLimitDescent`.

The family theorem constructs the normal Noetherian family stages, two generic-fibre
inverse systems, their limits, and compatible generic sections, without any torsor
input. The descent theorem selects a stage for a pointed finite torsor on two arbitrary
qcqs affine inverse systems, with no normality, Noetherianity, smoothness, or group-order
invertibility assumptions. The original theorem selects the resulting stage, transports
its point along the inverse field-spectrum isomorphism, proves the two generic-section
equalities by associativity, and supplies all the original conjunctions. Neither new
statement is the original conclusion under another name or with repackaged hypotheses.

Updated `lem-sbc-noetherian-spreading-data`'s proof, proof dependencies and proof origin
to this exact assembly. The unit's limit-reduction route is retained. No statement or
definition was changed, and no choice from an unproved existence theorem was put in a
definition: all witnesses are eliminated inside the theorem proof.

All three modules compile together in import order with `lcompile.py --all`, without
errors or warnings. The new statements were checked on constant diagrams (ordinary
pointed torsors), the trivial finite group, and empty systems' scheme objects; cofiltered
indexing ensures a stage exists. Empty C is excluded by the section from integral S.
For a normal Noetherian base (in particular a field), a constant family system meets
the intermediate signature; it does not require finite type over the integers. The
family lemma also allows n=1; n=0 gives no unit on the nonempty integral base.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.GaloisCover.exists_noetherian_spreading_data`
(node `lem-sbc-noetherian-spreading-data`). No `sorry` remains in the item's module.

Added two holes, each a public theorem with proof exactly `:= by sorry`:

- `AlgebraicGeometry.Scheme.exists_normal_family_generic_limit`
  (node `lem-sbc-normal-family-generic-limit`, module `NormalFamilyGenericLimit`).
- `AlgebraicGeometry.Scheme.GaloisCover.exists_pointed_stage_of_affine_limits`
  (node `lem-sbc-pointed-galois-cover-limit-descent`, module
  `PointedGaloisCoverLimitDescent`).

This is a decomposition, not a net proof of the limit reduction: one upper hole is
closed and two lower holes are added (net -1). The target proof contains no partial
holes; the unproved mathematics is exactly in these two new modules.

## No longer needed

None. No existing imports, nodes or modules were pruned: the original node had no
named proof dependencies and its six public imports support its unchanged signature.
Both new proof-only imports are used. In particular the Noetherian extension theorem
and the general cover-extension theorem are not used in this reduction; there were
no imports of them to remove.

## Where the brief, the DAG or earlier work was wrong

The DAG's one combined proof step names no dependency despite bundling several pages
of approximation, finite-presentation descent, and pointed finite-cover descent. The
new nodes expose these two main parts rather than hiding their proof in the target.

The phrase "normalizing each stage in the base ... these normalizations are finite"
needs precision. A full relative integral closure in an arbitrary extension field need
not be finite: the integral closure of Z in an algebraic closure of Q contains
infinitely many algebraic integers and is not a finite Z-module. The family step uses
normalization of the integral finite-type image in its own fraction field; this is
finite, and normality of S factors its dominant projections through it. The old images
already exhaust the affine coordinate rings, so these enlarged stage rings still have
S as limit. This realizes the same normal-approximation part of the unit's route,
without asserting finiteness of integral closure in an arbitrary extension field.

No shorter declaration was found. LeanFinder returned Mathlib normalization maps for
family approximation, and eventual-equality/factorization lemmas for pointed descent.
Loogle (`"IsNoetherian", "IsPullback"`) returned no hits. LeanSearch was unavailable
with an Internal Server Error for both new statements; this is recorded as unavailable,
not as a negative result. Mathlib grep returned no normal-family approximation or
pointed Galois-cover limit-descent theorem. Local library and whole-DAG/blueprint
searches checked the absolute Noetherian approximation, finite-presentation descent,
finite/étale inverse-limit descent, section components, and Tag 0BTV; none supplies
either complete intermediate statement. The source read was Stacks Tag 0EZJ and its
cited Tag 0BTV (Lemma 58.14.1).

The new nodes quote existing generic tools `prop-nagata-noetherian-inverse-system`,
`thm-pd-spreading-out`, `lem-weil-pbc-finite-type-z-domain-normalization-finite`,
`lem-weil-pbc-descend-finite`, and `lem-weil-pbc-descend-etale` from other units in their
remaining proof plans. They serve exactly their general approximation/descent purposes;
they do not replace a step of the spreading unit. The maintainer may record these as
tool uses. The section-component step uses the already stated
`lem-sbc-smooth-section-component-geometrically-irreducible` from this chapter.

## New nodes

`lem-sbc-normal-family-generic-limit` is in
`dag/nodes/sec-smooth-base-change/lem-sbc-normal-family-generic-limit.json` and is stated
in `lean/Sheaf/AlgebraicGeometry/Morphisms/NormalFamilyGenericLimit.lean`. It is the
family-only normal approximation and generic-limit portion of Stacks 0EZJ. Its full
natural-language proof is in its docstring and node; it has three recorded search kinds.
It introduces no new definitions or structures.

`lem-sbc-pointed-galois-cover-limit-descent` is in
`dag/nodes/sec-smooth-base-change/lem-sbc-pointed-galois-cover-limit-descent.json` and is
stated in `lean/Sheaf/AlgebraicGeometry/Morphisms/PointedGaloisCoverLimitDescent.lean`.
It is the finite-cover/group-action/point portion of Stacks 0EZJ, generalized to two
qcqs affine inverse systems. Its proof plan first descends the finite étale cover,
then the finite action and torsor inverse, and finally descends a section of the
pullback cover along the second system. It has three recorded search kinds and
introduces no new definitions or structures. No change record is required.


## Second reading by N2

1. Compared the entire item module with the repository using diff, and separately
   compared the declaration text before `:= by` byte for byte: identical. The only
   item Lean changes are its proof and the two plain, proof-only imports. Existing
   node changes are confined to proof, proof_deps and proof_origin. There are no
   definitions or statement changes and no change record is required. Verdict: pass.
2. Compiled all three modules in import order with lcompile.py: no errors or warnings.
   Independently compiled scratch copies with #print axioms for all three declarations:
   precisely propext, Classical.choice, Quot.sound and sorryAx. The item has no sorry;
   the two new public theorems each have exactly `:= by sorry`. No definition, axiom,
   unsafe, opaque, extern or implemented_by was introduced. Existential witnesses are
   eliminated only inside the theorem proof, not used to define arbitrary data.
   Verdict: a valid conditional assembly, not an axiom-clean completed target.
3. Read Stacks 0EZJ, 0BTV and 01ZM and the actual GaloisCover structure. The family
   lemma retains qcqs, integral normal base, smooth geometrically connected family,
   its section, invertibility and both generic-section equations, but has no cover
   input. The descent lemma needs only qcqs affine-transition limits and compatibility
   of the two sections; finite G supplies finitely many action equations and the
   torsor inverse descends by finite presentation. Neither restates the item. Tested
   the constant diagrams, trivial group, empty stage objects and n=0/1 in words:
   cofilteredness excludes empty indexing; an empty limit forces an empty stage by
   compactness; n=0 is excluded by integral nonempty S. Finite etale torsors need not
   be connected. Repeated LeanFinder search with the query beginning "Finite etale
   torsors and sections descend" returned only eventual equality/factorization and
   global-section limit results. Grep on Mathlib AffineTransitionLimit and local and
   upstream searches for approximation, torsor descent and function-field limits
   found no complete match. Read upstream Scheme.isLimitFunctionFieldCone: it concerns
   the affine opens of one integral scheme, not this normal family system. The holes
   need substantial new formalization, not a few-minute specialization. Verdict: true,
   strictly smaller residual statements with source/docstring proofs and nodes.
4. Followed the assembly downward: family limit data, pointed stage selection, then
   transport by e.inv. The two section equations are associativity; the point equation
   is associativity and hz0. Every new import is used, and all six old public imports
   support the unchanged signature. The old proof_deps is empty, so "No longer needed"
   is complete. Read sk-prop-input-spreading.json: realized has empty entries; the
   decomposition preserves its limit-reduction step and does not bypass any recorded
   realization or use the cover-extension theorem. Verdict: pass, decomposition with
   one closed hole and two added holes, net -1, no module pruned.
5. Matched the three nodes' Lean records with their declarations. The item's two
   proof dependencies are exactly the two applied lemmas; its final elementary step
   matches the Lean transport calculation. New nodes have matching chapter/unit,
   source, blueprint ancestry, creation records, searches, Lean signature and split
   status. The approximation/finite-presentation tools are used for their general
   purposes, as reported above, and not to replace the unit's route. Verdict: pass.

Changes in this second reading: clarified the new family docstring and matching node
step to say normalization in the integral image's own fraction field, embedded in
k(S), rather than a potentially infinite normalization in k(S). Added the coinitial
reindexing argument from a small cofiltered category to a directed poset to the
pointed-descent docstring/node, since the cited Stacks lemmas use directed sets. Made
its surjectivity argument explicit using the clopen complement system and compactness
of inverse limits. No Lean signature, proof term, definition, dependency or import
changed. Added this review and independently checked the axioms.
