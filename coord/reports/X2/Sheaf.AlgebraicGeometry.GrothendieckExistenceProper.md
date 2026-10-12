## What changed

Replaced the only hole in `Sheaf.AlgebraicGeometry.GrothendieckExistenceProper` by a
compiling contradiction argument. Its declaration and every public import are unchanged.
A maximal failing closed quotient supplies a non-algebraizable formal module. The proved
comparison provides a nonzero-power ideal and a map to a completion with torsion error.
Maximality supplies the positive-thickening equivalences; the existing
`grothendieck_existence_devissage` algebraizes the module, giving the contradiction.

Added three modules, one public theorem per module:

- `GrothendieckExistenceMaximalFailure`: the remaining Noetherian reduction, stated as a
  named theorem with a complete proof in words and its own node.
- `GrothendieckExistenceProjectivePullback`: proved from Chow's constructed modification,
  the existing proved finite-coordinate embedding, projective existence, formal pullback,
  and the full-subcategory inclusion equation.
- `GrothendieckExistenceProperComparison`: proved from the preceding pullback theorem,
  Mathlib's vanishing-ideal/support/power lemmas, and formal-systems push-pull.

The last two modules contain no direct holes. They explicitly import the existing
statements their proofs use. All four delivered modules compile cleanly with
`lcompile.py --all`; the import pruning was compiled again. The existing unit statement
and its realized steps are untouched. The route still uses proper full faithfulness,
Noetherian maximality, closed-quotient correspondence, Chow, projective algebraization,
push-pull, and devissage.

The maximal-failure statement was checked against the first two paragraphs of
https://stacks.math.columbia.edu/tag/088C. Its conclusion is a failing object on a maximal
closed quotient, not the proper-existence theorem under another name. The proof combines
that reduction with separately proved geometric comparison and the existing devissage
statement. No data definitions, arbitrary witness definitions, or axioms were added.
The preimage chosen in the projective-pullback proof is under a completion equivalence;
full faithfulness determines it up to isomorphism, which is the equality used downstream.

## Proved and sorry left

Closed the direct hole in `AlgebraicGeometry.grothendieck_existence_proper`
(node `prop-weil-pbc-grothendieck-existence-proper`).

Also proved, with complete Lean bodies:

- `AlgebraicGeometry.proper_existence_projective_pullback`
  (`lem-weil-pbc-proper-existence-projective-pullback`).
- `AlgebraicGeometry.proper_existence_comparison`
  (`lem-weil-pbc-proper-existence-comparison`).

Added exactly one direct hole:
`AlgebraicGeometry.proper_existence_maximal_failure`
(`lem-weil-pbc-proper-existence-maximal-failure`), in the new module
`Sheaf.AlgebraicGeometry.GrothendieckExistenceMaximalFailure`.
Its whole proof is `:= by sorry`; there are no partial-proof or private holes.
There are no holes left in the assigned module. This is a decomposition, not a proof
free of sorry: one original hole closed, one new lower hole added, net zero direct holes.
Existing projective-existence, formal-pullback, push-pull and devissage statements remain
proof dependencies; their earlier holes are not claimed closed by this delivery.

Edge cases checked: empty X is permitted by the original theorem and by the proved
projective-pullback helper. A maximal failing quotient must be nonempty since completion
on the empty scheme algebraizes its zero system. K = top gives the empty quotient and is
included among the nonzero ideals. The comparison permits U = X; its complement ideal is
then top and its powers remain nonzero when X is nonempty. Positive exponents are used
explicitly, with no assertion at exponent zero. No nontrivial-ring hypothesis was added;
when the base ring is zero every proper scheme over it is empty and the counterexample
hypothesis is impossible. Noetherian witnesses are propositions and the thickening
hypothesis accepts every witness. The finite-coordinate theorem includes the empty index.

## No longer needed

Removed these ordinary proof imports from the assigned module:

- `Sheaf.AlgebraicGeometry.ClosedImmersionCoherentEquivalence`
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAbelian`
- `Sheaf.AlgebraicGeometry.FormalCompletionFullyFaithfulProper`
- `Sheaf.AlgebraicGeometry.FormalSystemsPullback`
- `Sheaf.AlgebraicGeometry.FormalSystemsPushPull`
- `Sheaf.AlgebraicGeometry.GrothendieckExistenceProjective`
- `Sheaf.AlgebraicGeometry.ModulePullbackIdealQuotient`
- `Sheaf.AlgebraicGeometry.NoetherianQuasicoherentSubmodules`
- `Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme`
- `WeilConjectures.AlgebraicGeometry.ChowLemma`
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`

The assigned module now needs only the maximal-failure, comparison and devissage proof
imports. Public imports are preserved. Apart from the following actual simplification,
the removed direct imports' mathematical work remains in the proved helper dependencies
or in the explicitly stated plan of maximal failure; they are not claimed globally pruned.

The route does not need `lem-weil-pbc-reduced-induced-closed-subscheme` or its module
`Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme`. For the complement ideal we use
Mathlib's actual `Scheme.IdealSheafData.vanishingIdeal`,
`coe_support_vanishingIdeal`, `support_pow`, and `support_bot` directly. No reduced
closed-subsheme uniqueness, affine description or residue-field calculation is needed.
Its import and proof-dependency edge have been removed. Whether other targets still
reach that module is a global queue question; this delivery does not claim otherwise.

Complete list of old direct `proof_deps` edges removed from the assigned node:

- `def-nagata-extended-ideal`
- `def-sbc-closed-immersion-ideal-sheaf`
- `def-weil-pbc-coherent-formal-module`
- `def-weil-pbc-noetherian-ring`
- `def-weil-proper-morphism`
- `lem-weil-pbc-chow-noetherian`
- `lem-weil-pbc-closed-immersion-coherent-equivalence`
- `lem-weil-pbc-closed-immersion-comp`
- `lem-weil-pbc-closed-immersion-factor-ideal-inclusion`
- `lem-weil-pbc-closed-immersions-equal-ideal-isomorphic`
- `lem-weil-pbc-coherent-formal-modules-abelian`
- `lem-weil-pbc-finite-type-over-noetherian`
- `lem-weil-pbc-formal-completion-fully-faithful-proper`
- `lem-weil-pbc-formal-systems-pullback`
- `lem-weil-pbc-formal-systems-push-pull`
- `lem-weil-pbc-grothendieck-existence-projective`
- `lem-weil-pbc-immersion-closed-image-closed-immersion`
- `lem-weil-pbc-module-pullback-ideal-quotient`
- `lem-weil-pbc-noetherian-acc-quasi-coherent`
- `lem-weil-pbc-proper-fp-permanence`
- `lem-weil-pbc-proper-over-separated`
- `lem-weil-pbc-quasi-coherent-ideal-closed-subscheme`
- `lem-weil-pbc-reduced-induced-closed-subscheme`
- `lemma-nagata-projective-space-base-change-proper`

These are removed direct edges, not a claim that all their modules leave the target closure.
The definition nodes still describe the unchanged signature. The maximal-failure node
retains the full-faithfulness, ACC and closed-quotient work in its stated proof plan;
projective-pullback retains Chow, proper-over-separated, the closed immersion and
projective-existence work; comparison retains push-pull. Proper composition and
projective-space properness are supplied by library instances in these helpers.
The abelian module is still needed for the comparison's public kernel/cokernel signature.
Only the reduced-induced-closed-subscheme lemma's work is actually bypassed, using
Mathlib's vanishing-ideal and support lemmas instead.

## Where the brief, the DAG or earlier work was wrong

No disputed mathematical statement or forced adaptation. The original plan omitted the
interface bridge from Chow's arbitrary finite homogeneous index to the standard
`ULift (Fin (n + 1))` required by projective existence. The already proved
`ProjectiveSpace.exists_isClosedImmersion_finite_coordinates` supplies it; a draft
reindexing lemma was discarded and is not delivered. The bridge is a closed linear
embedding, so no new projective-space definition or index nonemptiness assumption is needed.

The maximal-failure proof still needs to identify the two written forms of the completion
ideal: the kernel of Spec(A/I) -> Spec A and `ofIdealTop` applied to I transported along
`GammaSpecIso`. This is an affine kernel computation and is specified in that theorem's
proof in words. The projective-pullback and comparison proofs use the kernel form
throughout and compile without such a transport.

The checkout omits the untracked Stacks source files. The cited proof was read at the
Stacks 088C page; source records name that accessible source. LeanSearch was unavailable
(Internal Server Error), recorded without inferring absence. LeanFinder gave eight
unrelated affine-limit/integral/finite-morphism results for maximal-failure search. Loogle
found the general equivalence interface, and direct library search found all the used
ingredients. Blueprint searches for maximal counterexample and 088C found no existing
statement of the remaining reduction. The existing 088E Chow comparison concerns proper
support and does not yield the required algebraization comparison on an already proper X.

## New nodes

`lem-weil-pbc-proper-existence-maximal-failure` records steps 1--3 of Stacks 088C:
proper full faithfulness, maximal failing ideal, nonempty closed replacement, and
algebraization of every nonzero quotient. It is the only new item with sorry.

`lem-weil-pbc-proper-existence-projective-pullback` records the proved steps 4--5:
Chow's modification, the existing finite-coordinate embedding, the projective case,
and the formal-category inclusion transport to an ambient pullback isomorphism.

`lem-weil-pbc-proper-existence-comparison` records the proved steps 6--7:
the nonzero powers of the complement ideal and the push-pull comparison data. Its proof
has no induction or thickening-algebraization assumption.

All three inherit the assigned node's chapter, unit and blueprint ancestor. The original
node's proof, proof_deps and proof_origin now describe the actual three-part contradiction
argument. Existing statements, lean records and unit records are unchanged. No change
records are needed because no existing definition, signature or public import changed.

## Second reading by X2

1. Interface preservation: PASS. Diffed the assigned module against the repository.
   The theorem header, its docstring, and all existing public imports are byte for byte
   unchanged. Only proof imports and the proof body change. All other delivered Lean
   modules are new; there are no adapted modules or changed definitions. Checked the
   change-record references to this item: they require no adaptation here.
2. Proof and trust: PASS. Independently compiled all four modules in import order with
   `lcompile.py --all`; no errors or warnings. Scanned all delivered sources: the only
   direct hole is `AlgebraicGeometry.proper_existence_maximal_failure`, exactly `by sorry`.
   No forbidden declarations, attributes, hollow definitions or arbitrary-witness data
   definitions occur. Scratch-copy `#print axioms` checks show only the permitted standard
   axioms and `sorryAx` from the explicitly open reduction and upstream dependencies.
   This delivery is a decomposition, with one original hole closed and one lower hole
   added, not an axiom-free proof of proper existence.
3. Split statement: PASS. Read the maximal-failure header, its complete proof docstring,
   node and the proof of Stacks 088C. Noetherian ACC on failing quotient ideals, proper
   full faithfulness and closed-immersion correspondence give precisely its conclusion.
   It does not assert algebraization on the maximal quotient and does not repeat the
   item's conclusion. Empty X, the zero base ring, K = top and all positive powers were
   checked: empty schemes have only the zero system, and no exponent-zero claim is used.
   The kernel/ofIdealTop identification is an explicitly recorded affine computation,
   not an assumed definitional equality. Repeated LeanFinder search with “ascending
   chain maximal element closed subscheme completion essentially surjective”; results
   were only basic Noetherian scheme facts. Qualified Loogle search found the generic
   equivalence interface, not this reduction. Direct searches for algebraization,
   essential surjectivity and maximal failure found no reusable reduction. Read the
   existing system-support/Chow-comparison route: it proves proper support and cannot
   replace this reduction without circularly using proper existence.
4. Route and pruning: PASS after report repair. Read the proof from the assigned theorem
   down through comparison and projective pullback, checking their dependency statements.
   The inclusion equation determines formal pullback and the completion equivalence
   determines the preimage up to isomorphism. The shortest available finite-coordinate
   embedding is already used. Ordinary imports are the proof dependencies; public imports
   support signatures (including tensor pullback and the formal-category zero morphisms).
   Checked `dag/units/sk-thm-p1.json`: its statement and every `realized` entry stay intact.
   Completed the removed direct-edge list above and distinguished relocation into helpers
   from the actual reduced-complement lemma bypass. No global pruning total is claimed.
5. DAG agreement: PASS after a notation repair. The original node changes only `proof`,
   `proof_deps` and `proof_origin`. Their dependency union matches the three applications
   in Lean. Each new node has its declaration, source, search records, creation record,
   blueprint ancestor, chapter and unit; proved helper steps match their Lean bodies.
   Corrected the maximal-failure node's prose composition from j composed with f to
   f composed with j, matching the Lean expression `j ≫ f`.

Second-reading changes: completed the pruning report, corrected composition order in
one new node's natural-language statement, and added this independent review. No Lean
proof or declaration needed repair. The remaining reduction is substantial and is not
claimed closed by this reading. Temporary axiom probes are excluded from the delivery.
