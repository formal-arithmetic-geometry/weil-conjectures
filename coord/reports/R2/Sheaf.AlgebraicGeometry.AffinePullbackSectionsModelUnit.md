## What changed

Reduced `AlgebraicGeometry.exists_affinePullbackSections_model_unit` to the two genuine
steps of its existing plan. The original signature, universes, binders and visibility
are unchanged. Added two modules:

- `AffinePullbackModelComparisonsIsIso`: constructs the canonical sections morphism and
  the fixed pullback counit morphism explicitly, and states their invertibility on the
  K-flat associated-sheaf model.
- `AffinePullbackSectionsUnitUncancelled`: states the normalized unit identity for an
  arbitrary sheaf complex, before any comparison is cancelled. It assumes the original
  `hr` compatibility and does not assume K-flatness or quantify over isomorphisms b.

The original module constructs b as derived B-sections of the fixed counit followed
by the inverse of the fixed B-sections comparison. Its proof precomposes the
uncancelled identity with s.hom, postcomposes with exact restriction of the inverse
B-comparison, and cancels both comparisons in Lean. Data in both new definitions is
explicit, not chosen from mere existence. `asIso` takes the inverse of a fixed map,
whose inverse is uniquely determined by its invertibility theorem.

Validation: `lcompile.py --all` compiled all three delivered modules without warnings.
The declaration comparison reports no changed existing signature, the original named
hole closed, and no new hole inside the original module. The delivery dry run printed
OK; no push was made. All delivered Lean lines are at most 100 characters.

## Proved and sorry left

Holes closed in the item's module: 1, namely
`AlgebraicGeometry.exists_affinePullbackSections_model_unit`
(node `new-affine-pullback-sections-model-unit`). This is a decomposition, not a
complete mathematical proof or a net reduction of the sorry ledger.

Holes added: 2, each a named public theorem with proof exactly `by sorry`:

- `AlgebraicGeometry.affinePullbackModelComparisons_isIso`
  (node `new-affine-pullback-model-comparisons-isIso`). Its conclusion consists only of
  invertibility of two explicitly specified comparison maps; it mentions neither
  v, r, hr, s nor the desired adjunction-unit equation.
- `AlgebraicGeometry.affinePullbackSections_unit_uncancelled`
  (node `new-affine-pullback-sections-unit-uncancelled`). Its conclusion is the
  comparison identity before cancellation for all sheaf complexes, without K-flatness,
  any invertibility assumption, or an existential model isomorphism.

There is no sorry in the item's proof, in a definition, or in a private declaration.
The two comparison definitions are explicit composites of existing canonical maps.
The remaining statements have detailed source-based proof docstrings and DAG steps.

## No longer needed

Removed direct proof imports from the original module:
`Sheaf.AlgebraicGeometry.Modules.IsKFlatTilde`,
`Sheaf.AlgebraicGeometry.TensorPullbackTilde`, and
`Sheaf.AlgebraicGeometry.AffineTildeDerivedSectionsUnitIsIso`.
Their nodes (`lem-pc-affine-tilde-kflat`,
`lem-weil-pbc-tilde-pullback-base-change`,
`new-affine-tilde-derived-sections-unit-isIso`) remain in the proof plan of the new
comparison-invertibility item. They are not mathematically pruned; work on them is
still needed by that step. No complete module or theory is claimed permanently
unnecessary. The original module now needs only the two new proof imports in addition
to its unchanged public imports. Its old proof_deps are replaced by those two nodes;
the old geometric dependencies are carried by the invertibility node and the
normalization dependencies by the uncancelled identity node.

## Where the brief, the DAG or earlier work was wrong

The earlier universal-isomorphism equation was false: changing b by an automorphism
changes its left side. This delivery never imports or reinstates that equation or
the unsupported arbitrary-existence split. It fixes both morphisms first and states
an identity about those morphisms. On the identity morphism of Spec Z with Z in
degree zero, the comparison is the fixed normalized one; its sign twist is not a
possible input to the uncancelled statement. Zero rings and zero complexes are
allowed in both new statements, and no flatness of the ring map or boundedness has
been added. The supplied v and r can vary, but the original hr is retained exactly.

The unit record `sk-thm-picard-duality` has empty realized statement/step entries.
The two steps of the item's own plan are preserved. No definition or statement of
another existing module changed and no forced adaptations are needed.

The local checkout does not contain the Stacks .tex source. Read the corresponding
primary-source pages for Tags 06Z0, 08DV, 08DW, and 0AA7 online, and the existing Lean
proofs and signatures. LeanSearch returned Internal Server Error; recorded it as
unavailable, not as evidence of no match. Loogle found derivedη_fac_app, and local
searches found the normalized Hom-equivalence theorem, the tilde K-flat theorem,
the tensor/tilde isomorphism, and the proved affine sections invertibility theorem.

A further proof experiment is retained only in
`scratchpad/comparisons/lean/Sheaf/AlgebraicGeometry/AffinePullbackModelComparisonsIsIso.lean`.
It develops the generic-to-sheaf K-flat translation and counit uniqueness argument,
then attempts tensor/tilde transport of the affine sections unit. The counit branch
elaborated in an earlier run, while the sections branch encountered functor-instance
and homotopy-quotient transport mismatches. A fuller attempt reached the 60-second
compiler limit. This experiment is not a delivered proof, and no inner sorry from
it occurs in the delivery tree. The next worker should use the explicit comparison
interfaces and the full docstring argument, not treat this scratchpad as verified.

## New nodes

`new-affine-pullback-model-comparisons-isIso`, in
`dag/nodes/sec-picard-framework/`, realizes the first step of the original item:
K-flat counit invertibility and affine acyclicity after tensor pullback of tilde.
It records the exact two definitions as well as the invertibility theorem in the
new module's Lean record. The proof uses the same geometric ingredients as before.

`new-affine-pullback-sections-unit-uncancelled`, in the same chapter, realizes the
second step before cancellation. Its source is the normalized unit calculation of
the original node and Mathlib's derived adjunction factorization. The proof sketch
specifies the Hom-equivalence specialization, composition unit, hr specialization,
and Q/Qh transport. The parent node's proof, proof_deps and proof_origin now record
the actual construction and cancellation.

No statement-change record is required: all existing statements and definitions stay
unchanged. No second-reading section has been written by this worker.

## Second reading by R2

1. I compared the delivered item's module with the repository version. The existing
 declaration has the same binders, universes, hypotheses, conclusion, and visibility;
 only proof-only imports, a private cancellation lemma, and the proof body changed.
 The two added declarations are new split-off statements and are recorded by matching
 DAG nodes. Verdict: pass.

2. I compiled all three delivered modules with `lcompile.py --all` and compiled each
 file separately. They compile without errors or warnings. The only remaining `sorry`s
 are the two named public split-off theorems; no definition or private declaration
 contains `sorry`, and no forbidden command occurs. Verdict: pass.

3. I checked the new statements against their Lean signatures and the edge cases
 described in their docstrings. The comparison maps are explicit composites, while the
 two open theorems assert only invertibility and the uncancelled identity respectively;
 neither restates the parent existential theorem or adds an arbitrary witness. Their
 nodes contain source, proof steps, dependencies, Lean records, and searches. Verdict:
 pass.

4. I checked the proof route from the target downward. The parent proof uses the two
 new nodes, constructs its comparison isomorphism from `asIso`, and cancels the fixed
 comparisons. The unit's two realized steps remain represented by the comparison and
 uncancelled-identity nodes. The three old direct proof imports are removed because
 their work is now dependencies of the comparison node, and this is listed above.
 Verdict: pass.

5. I checked the DAG `proof`, `proof_deps`, and `proof_origin` against the Lean proof,
 including the exact fixed comparison definitions and cancellation route. The parent
 node's statement and the unit route are unchanged; the two new node records agree with
 their modules. Verdict: pass.

I changed no statements or definitions. I added this second-reading record and
verified the delivered files and node metadata; no further repair was needed.
