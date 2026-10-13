## What changed

Reduced `AlgebraicGeometry.mixedInternalHom_baseChange_exchange` to preservation of the
counit-defined direct-image tensor pairing by the canonical base-change mate. Its
signature, public imports, and existing docstring are unchanged. Added the proof import
`Sheaf.AlgebraicGeometry.MixedTensorPairingBaseChange` and `import all Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso` for its private
Tensor-Hom naturality lemma, plus private proved evaluation and pairing-naturality helpers. The monoidal namespace is opened for their notation;
this syntactic change has its required change record. The new module constructs the pairing directly from
the fixed adjunction counits and normalized tensorator; no data is chosen from a new
existence theorem. The existing node now records the actual evaluation proof.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.mixedInternalHom_baseChange_exchange`
(node `lem-sc-mixed-internal-hom-base-change-exchange`). Added one hole:
`AlgebraicGeometry.mixedTensorPairing_baseChange`
(node `lem-sc-mixed-tensor-pairing-base-change`). This is a decomposition, not a
sorry-free proof: one original hole is closed and one structural tensor hole is added.
The item's private helpers have complete proofs. The new pairing definition has no
hole. The remaining theorem concerns arbitrary tensor morphisms and no internal Hom,
evaluation, or tensor-Hom bijection, so it is a strictly different structural part of
the original argument rather than a renamed exchange statement.

## No longer needed

No original import or module is pruned. These old direct proof dependencies are no
longer used directly by the item's reduction and instead occur in the new structural
lemma's proof plan:

- `def-pc-derived-pullback-tensor-comparison`;
- `lem-pc-kflat-resolution`;
- `lem-pc-ringed-spaces-derived-pullback-composition`;
- `lem-weil-pbc-module-pullback-tensor`.

They are retained transitively, so this claims no module pruning. The base-change
map definition remains a direct proof dependency: the reduction defines beta from it. The
single-universe `InternalHomBaseChangeExchange` was tested as a possible shortcut
and is not imported in the delivery: it needs extra module-localization instances
and compares different selected tensorators. No unit statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The DAG's representative argument describes tensorator/composition compatibility,
but none of its existing dependency signatures directly states the required tensor
pairing compatibility. The delivery isolates precisely that step. There is no claimed
mathematical error in the original statement. The Stacks sources were read online:
Tags 08HY (counit description), 079U (K-flat pullback tensor comparison), 08I3
(pulled-back evaluation) and 0AA8 (final comparison diagrams). The new structural
lemma is an agent-written refinement of those constructions, not an assertion that
0AA8 states the unrestricted tensor formula verbatim.

Edge cases: identity base change gives tensor-pairing naturality; either zero tensor
input or the zero map gives the zero composite on both sides. The statement never
assumes beta is invertible, so it also covers non-flat base change. It imposes no
boundedness, perfectness, properness, quasi-coherence or module-universe assumptions.

Searches: LeanFinder first returned generic exponentiable-morphism evaluation lemmas. A more
focused search found `Adjunction.rightAdjointLaxMonoidal_μ` and its counit equation,
and `CanonicalPullbackTensorMonoidalRealization` realizes the pinned tensorators
by monoidal structures. No existing declaration supplies monoidal coherence of
the pinned derived composition comparisons or the required base-change pairing
identity. The generic right-adjoint structure does not alone give that compatibility;
LeanSearch was unavailable with an Internal Server Error; Loogle did not resolve the
requested identifiers; Mathlib grep found no monoidal base-change pairing theorem.
Repository and blueprint searches found no exact pairing compatibility statement.

## New nodes

`def-sc-mixed-direct-image-tensor-pairing` records the explicit adjunction transpose
of the tensor of counits, in `MixedTensorPairingBaseChange`. This definition is fully
constructed and adds no hole.

`lem-sc-mixed-tensor-pairing-base-change` records the remaining tensor compatibility
step in the same module. Its proof in words expands the base-change mates, checks
normalized tensorator/composition compatibility on K-flat representatives, and uses
naturality to transport an arbitrary tensor morphism. The proof-only namespace opening is recorded in
`coord/changes/mixed-internal-hom-proof-tensor-notation.md`, as required by the
syntactic visibility check. All existing signatures and public imports are unchanged;
no other module is adapted.

## Second reading by E1

1. PASS: diffed both delivered modules against the repository (the pairing module
   is new). Extracted the existing theorem header and checked it byte for byte.
   Its universes, hypotheses, conclusion, docstring and public imports are unchanged;
   no existing definition or target statement was changed. The recorded namespace
   opening only supplies proof notation. No consumer adaptation is delivered.
2. PASS: compiled both modules independently in import order with lcompile.py;
   no errors or warnings. The only textual hole is the named public theorem
   `AlgebraicGeometry.mixedTensorPairing_baseChange`, exactly `:= by sorry`.
   The new definition transposes actual tensorators and counits and chooses no
   existence witness. No forbidden declaration mechanism occurs. The delivery
   probe checks every added constant; the explicit axiom check is recorded below.
3. PASS: read the new pairing definition and structural theorem from their types,
   docstring and nodes. Transposing under the upper pullback adjunction reduces
   the identity to monoidality of the fixed composition comparisons and counit
   naturality; the normalization equations on K-flat representatives supply that
   monoidality. Tensor products of K-flat complexes and their pullbacks remain
   K-flat. Identity base change reduces to the same counit-pairing diagram, while
   a zero map or zero input gives zero on both sides; no beta is cancelled.
   This isolates the tensor step of the original plan and contains no internal Hom
   or evaluation, so it is a genuine decomposition, not a renamed exchange hole.
   Independently searched LeanFinder for Beck-Chevalley/lax-monoidal mates,
   Loogle for adjunction/monoidal results, Mathlib grep for mates and monoidal
   transformations, and the repository for tensor/base-change/composition results.
   Mathlib's right-adjoint tensor and mate equations help the abstract calculation
   but do not establish coherence of these pinned derived composition maps.
   The single-universe exchange still needs additional localization instances and
   different chosen tensorators. No immediate closing shortcut was found.
   Read Stacks [08HY](https://stacks.math.columbia.edu/tag/08HY),
   [079U](https://stacks.math.columbia.edu/tag/079U) and the final diagrams of
   [0AA8](https://stacks.math.columbia.edu/tag/0AA8); these support the construction
   and representative argument, rather than stating this unrestricted formula
   verbatim. Fetching 08I3 failed, so that source was not independently verified.
4. PASS: the main proof applies Tensor-Hom injectivity, computes the direct-image
   comparison's evaluation and uses tensorator/pairing naturality before the
   structural lemma. Both new imports are proof-only. The new module publicly
   imports the modules needed by its exposed definition and theorem types.
   Every removed old direct proof dependency is now listed above; none is a
   pruned module. Inspected `dag/units/sk-thm-picard-duality.json`: its realized
   statement and step lists are currently empty; this below-unit refinement
   changes neither the unit nor its route through finite duality.
5. PASS after metadata repairs: checked new-node sources, proof plans, search
   records, chapter/unit, blueprint ancestry and verbatim Lean statements. The
   existing node changes only its permitted proof fields and Lean record.
   Each proof_deps list is the union of its proof steps' uses. Retained the
   base-change definition in the main node, and added K-flat pullback preservation
   and tensor-product closure to the structural lemma's representative step.

Changed only dependency metadata and report accuracy/completeness during this
second reading. No Lean proof or signature required repair. One original hole
closed and one structural hole added: decomposition, net zero holes, no pruning.

Explicit scratch-copy `#print axioms` checks passed: the main theorem, pairing
construction, structural theorem, pairing naturality, direct-image evaluation and
evaluation formula use only `propext`, `Classical.choice`, `Quot.sound` and
`sorryAx` from open statements. The tensor-interchange helper uses only `propext`;
the functor-composition helper uses no axioms. The scratch copy was removed.
