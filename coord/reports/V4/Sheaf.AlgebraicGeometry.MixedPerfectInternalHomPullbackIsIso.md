## What changed

Proved `AlgebraicGeometry.mixedPerfect_internalHom_pullback_isIso` in
`Sheaf.AlgebraicGeometry.MixedPerfectInternalHomPullbackIsIso` without changing its signature.
Added a proved private noncomputable construction `mixedTensorHomCore` of the
canonical tensor/internal-Hom adjunction from its natural Hom bijections.
Added proof imports of `PerfectImpliesQCoh`, `CanonicalPullbackTensorMonoidalRealization`,
and `import all PerfectInternalHomPullbackIsIso`. The last import reuses its already
proved, universe-independent private theorem `monoidal_adjunct_isIso`; the public
scheme specialization is not applicable because it requires module localization
in the same universe. No helper proof was duplicated or dependency module adapted.

The argument extracts an exact pairing from `perfect_rhom_tensor_comparison`,
realizes the normalized tensor comparison monoidally, applies the generic rigid mate
calculation, and identifies its arrow with the prescribed canonical evaluation mate.
The final equality is explicit congruence of tensorator and counit equalities, avoiding
expensive broad rewriting through concrete adjunctions. Local compilation takes about
23 seconds; the heartbeat setting is needed for shared tensor-instance elaboration.

Read Stacks Tags [08I3](https://stacks.math.columbia.edu/tag/08I3) and
[0FPC](https://stacks.math.columbia.edu/tag/0FPC) online (the local tex is absent).
08I3 specifies precisely evaluation preceded by the inverse tensor comparison;
0FPC supplies perfect duality. The chosen local adjunction uses the fixed canonical
family, so the conclusion concerns exactly this map. The proof uses arbitrary N,
independent universes u,w, and no flatness, qcqs, nonzero or nonempty assumptions.
For zero M and empty source all steps still apply without an excluded case.
The unit `sk-thm-picard-duality` has no realized statement/step nodes; its route is unchanged.

Searches run through msearch.py: LeanFinder on strong monoidal functors and the
internal-Hom mate returned eight rigid-mate/Frobenius hits, no exact match;
Loogle `Adjunction.rightAdjointUniq` returned unknown identifier/zero hits;
grep `monoidal_adjunct_isIso|internalHom.*pullback` returned three unrelated
Mathlib Leibniz-pullback hits. Direct repository reading found and reused the
proved generic private helper in `PerfectInternalHomPullbackIsIso`.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.mixedPerfect_internalHom_pullback_isIso`
(node `lem-sc-mixed-perfect-internal-hom-pullback-isIso`).
No sorry remains in this module. No new hole or axiom is added; zero statements split off.
The private construction has complete naturality proofs.
This is a proof from existing library dependencies, not a decomposition into new holes.

## No longer needed

None. Both original proof dependencies remain needed: perfect duality and normalized
tensor pullback. All three original public imports are required by the unchanged
statement. All proof imports are used by name; the `import all` supplies the generic
private categorical helper, not the stronger public specialization.
The proof does not request new local-complex or gluing nodes: the existing perfect
comparison supplies its pairing. No existing planned node is dropped.

## Where the brief, the DAG or earlier work was wrong

The recorded plan is sound. Its equivalent strong monoidal duality route is now
implemented. The public `perfect_internalHom_pullback_isIso` requires an additional
module derived-category universe assumption and cannot directly prove this statement.
Its proved private generic helper does not have that assumption and is available via
Lean's `import all`; reusing it avoids duplicating the categorical proof.
The updated node records the actual dependencies and explicit morphism equality.

## Second reading by V4

1. **Interfaces: pass.** Compared the only delivered Lean module with the repository
   version using `diff -u`. The existing theorem signature, universes, instance
   assumptions, visibility and docstring are byte-for-byte unchanged. All new
   imports are proof-only. There are no adaptations or change records.
2. **Proof and data: pass.** Independent local compilation succeeded without warnings
   in 26.1 seconds. No `sorry`, forbidden axiom declaration or unsafe mechanism occurs
   in the delivered module. A scratch copy printed axioms for the theorem and
   `mixedTensorHomCore`: both use `propext`, `Classical.choice`, `Quot.sound` and
   inherited `sorryAx` from still-open dependencies. The reused
   `monoidal_adjunct_isIso` uses only the three permitted standard axioms.
   The private core constructs its data explicitly from the already fixed canonical
   bijections and proves naturality; it does not choose an arbitrary witness.
   The extracted dual is constrained by equality to RHom(M,O), and its evaluation
   and coevaluation are pinned by the comparison theorem. The proof identifies
   the source counit and tensorator explicitly, so it proves invertibility of the
   precise displayed map, for arbitrary N and independent universes.
3. **Split statements: pass (none).** One original hole is closed; zero are added.
   There are no new public statements or nodes requiring a truth check or a
   docstring proof. The argument needs no nonempty, nonzero, flatness or boundedness
   assumptions; its exact-pairing calculation also applies to zero objects and
   an empty source.
4. **Route and pruning: pass.** Independently searched with LeanFinder for right
   adjoints to tensor under monoidal functors (eight rigid-adjunction hits), Loogle
   for `Adjunction.homEquiv_symm_rightAdjointUniq_hom_app` (service could not resolve
   the identifier), and grep for `ExactPairing.map|tensorRightAdjunction` (the
   Mathlib rigid adjunction). Read the reused generic helper and the library's
   other tensor-adjunction construction. No shorter applicable public theorem
   was found: `canonicalTensorHomAdjunction` and the public perfect pullback
   specialization carry the extra module localization assumption. The private
   local construction avoids adding an unrelated proof-module dependency.
   Both old proof dependencies are used and none can be listed as pruned.
   Each added proof import supplies a declaration used explicitly. The three public
   imports remain necessary for the unchanged statement. The unit's `realized`
   statement and step arrays are empty, as reported, and are unchanged.
5. **DAG: pass.** Compared the delivered node with its repository version: only
   `proof`, `proof_deps` and `proof_origin` differ. The dependency list is exactly
   the union of the steps' uses. The steps record quasi-coherence, the exact pairing,
   canonical adjunction construction, monoidal realization and the generic private
   mate helper; they agree with the Lean proof. The helper's node is used for its
   proved private categorical result, not its stronger public specialization.

Second reading changed only this report: added the independent checks and clarified
that the theorem still inherits `sorryAx` from open upstream dependencies. No repair
of the Lean proof or DAG was needed.
