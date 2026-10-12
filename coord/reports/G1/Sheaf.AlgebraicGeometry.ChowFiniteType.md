## What changed

Proved `AlgebraicGeometry.exists_chow_finite_type` without changing its signature.
The proof follows Stacks 0202: use the proved 01ZJ finite-presentation envelope,
choose the proved 01ZA Noetherian approximation, descend the envelope with the
proved combined 01ZM/01ZQ interface, apply the proved Noetherian Chow modification,
and perform the two base changes explicitly. Pullback stability establishes
properness, surjectivity and immersion; pullback equations establish the equation
of structure morphisms.

Added `Sheaf.AlgebraicGeometry.ProjectiveSpaceFiniteCoordinates`, with a proved
closed immersion from any finite-coordinate projective space into one indexed by
`ULift (Fin (n + 1))`. Enumerating `Option N` and killing its extra coordinate gives
a surjective graded polynomial-ring map. Renaming supplies a homogeneous right
inverse and verifies the irrelevant-ideal condition. The proved source theorem
`Proj.isClosedImmersion_map` gives the integral closed immersion; its pullback
along the base structure morphism gives the required immersion over S. This is
exactly the polynomial-ring Proj construction of Stacks 01ND and the closed
immersion assertion of 01N0. Neither declaration uses a new assumption.

Updated the original node's proof, proof_deps and proof_origin. All new proof
imports are private imports; the existing public imports and statement stay as
before. The new node and module are already proved, rather than parallel sorry
items. Local compilation of both modules in import order succeeded without
warnings. The required delivery dry run also runs the axiom and server checks.

## Proved and sorry left

- `AlgebraicGeometry.exists_chow_finite_type`
  (lem-weil-pbc-chow-finite-type): proved; its original sorry is removed.
- `AlgebraicGeometry.ProjectiveSpace.exists_isClosedImmersion_finite_coordinates`
  (lem-weil-pbc-projective-space-finite-coordinates): proved.

No sorry remains in either delivered module, and none is split off. The delivery
axiom probe checks the transitive proof dependencies against the three allowed
axioms.

## No longer needed

Removed these proof imports:

- `Sheaf.AlgebraicGeometry.ExistsIsSeparatedOverPullbackMap`: replaced by the
  already proved source combined finite-presentation/separated descent theorem.
- `Sheaf.AlgebraicGeometry.LimitAffineTransition`: the approximation already
  includes its limiting cone and its IsLimit proof.
- `Sheaf.AlgebraicGeometry.NagataFinitePresentationEnvelope`: use the source
  existence theorem directly instead of a chosen envelope definition.

Removed these direct proof dependencies from the item's node:

- def-nagata-finite-type-closed-in-fp
- def-weil-closed-immersion
- def-weil-open-immersion
- lem-weil-pbc-cofiltered-limit-directed-reindex
- pqf-def-affine-morphism
- lem-weil-pbc-limit-affine-transition
- lem-weil-pbc-finite-type-over-noetherian
- lem-weil-pbc-locally-noetherian-quasi-separated
- def-weil-proper-morphism
- def-weil-pbc-scheme-conventions

The direct proof no longer invokes these nodes separately: the established
approximation/descent interfaces and Mathlib property instances supply their
needed facts. Definition nodes still needed by the statement remain in
stmt_deps. This report claims pruning from this item's route, not that these
nodes or modules are globally unreachable from all other targets. No unit's
realized statement or step has been bypassed: this item is not itself a realized
statement or step of sk-thm-p1.

## Where the brief, the DAG or earlier work was wrong

The DAG's seven-step route is mathematically sound, but asks for an unnecessary
directed-set reindexing and separate limit-existence and separatedness lemmas.
The source library already exposes a small cofiltered Noetherian approximation
and a proved combined descent interface accepting it directly.

The source Chow modification uses an arbitrary finite coordinate type, whereas
the item's exact conclusion uses `ULift (Fin (n + 1))`. That conversion was absent
from the stated dependencies. The added proved lemma fixes it without changing
the item's statement. Adding one coordinate avoids any nonemptiness assumption:
for N empty the polynomial-ring Proj source is empty and its embedding into P⁰
is still valid; for N a singleton it embeds P⁰ as a hyperplane in P¹. For an
empty base the same pullback construction still applies. No excluded edge case
or target signature change is introduced.

Searches were run with msearch.py: LeanFinder for Chow's lemma returned only
Mathlib properness/Proj facts; Loogle and grep gave no exact finite-coordinate
embedding theorem. The new-node LeanSearch query returned HTTP 500 and is
recorded as unavailable, not as a negative search result. Direct source searches
found the already proved surjective-Proj-map theorem used in the new proof.
Blueprint searches for "finite coordinates", "projective space finite" and
"linear closed" found no existing statement of this embedding; the one
finite-coordinate hit was an unrelated linear-algebra sequence detection lemma.
The existing prop-nagata-relative-proj-functoriality states the general
surjective-map property, not this finite-coordinate embedding, and its affine
clause is used through the already proved source theorem.

## New nodes

`lem-weil-pbc-projective-space-finite-coordinates` records the finite-coordinate
embedding and its complete Lean proof in
`lean/Sheaf/AlgebraicGeometry/ProjectiveSpaceFiniteCoordinates.lean`. Its source
is Stacks 01N0 and 01ND; it serves the numerical coordinate requirement in the
Chow step of the existing finite-etale-lifting route. It introduces no sorry
and no change record is needed, since no existing definition, signature or
public import is changed.

## Second reading by G1

1. **Visible declarations: pass.** Diffed both delivered modules against the
repository (the coordinate module is new). The only changes in the existing
module are private proof imports and the body of `exists_chow_finite_type`.
Its signature and docstring are byte-for-byte unchanged; all public imports
are preserved. There are no changed definitions or change records. Read
[Stacks 0202](https://stacks.math.columbia.edu/tag/0202): its qcqs base,
separated finite-type morphism, numerical projective space, proper surjection,
immersion and equation over the base all match the Lean conclusion.

2. **Proof and axioms: pass.** Independently compiled both modules with
`lcompile.py --all`, without errors or warnings. Scratch copies with
`#print axioms` for each of the two delivered theorems report exactly
`propext`, `Classical.choice`, `Quot.sound`; neither uses `sorryAx`.
Scanned both files: no sorry, axiom, unsafe, opaque, extern, implemented_by,
or kernel-check bypass. Scratch copies were removed before delivery.

3. **New statements: pass; none split off.** Read the new coordinate theorem
and all of its polynomial construction. The map from the polynomial ring on
`Option N` kills `none`; renaming along `some` gives the explicit right inverse
`hφ`, preserving each degree. `hirr` lifts each positive-degree homogeneous
element, so `Proj.map` is defined everywhere. Read the proof and hypotheses of
`Proj.isClosedImmersion_map` (Functor.lean:81) and checked that `hsurj` supplies
exactly its surjectivity hypothesis. The final pullback gives a closed immersion
over S. This agrees with
[Stacks 01N0(2)](https://stacks.math.columbia.edu/tag/01N0) and
[01ND, Definition 27.13.2](https://stacks.math.columbia.edu/tag/01ND).
For N empty, Proj of the trivially graded integer ring is empty and the map is
its closed immersion into P⁰; for N singleton the construction embeds P⁰ as
a hyperplane in P¹. An empty S is allowed throughout. No nonemptiness or
Noetherian assumption is smuggled into this lemma. Independent msearch
LeanFinder query "Projective space embedding induced by an injection of finite
homogeneous coordinate sets" found only vector-space Projectivization results;
grep for Proj renaming and ProjectiveSpace equivalences found no scheme theorem.
Read both upstream ProjectiveSpace files and searched lean/Sheaf with different
coordinate/finite-projective phrases: no duplicate statement. This lemma is
strictly the coordinate conversion, not a relabelled Chow theorem.

4. **Route and pruning: pass after correction.** Read the envelope theorem
(AffineTransitionLimit.lean:4592), the combined separated descent theorem
(:3519), NoetherianApproximation and its existence theorem, ChowModification,
and ProjectiveSpace's pullback interface. The envelope applies because the
first two lines establish X qcqs. Approximation supplies qcqs Noetherian stages;
descent gives separated finite-presentation g₀, so ChowModification applies.
H′ pastes the model square with the modification pullback; the next pullback
restricts to X. Properness/surjectivity survive both base changes, and the
closed immersion into the first pullback composes with jY and k to give the
claimed immersion. The over-S equation is proved explicitly. The upstream
ProjectiveDomination proof has the same reduction but assumes a proper map and
an affine base, so cannot replace this theorem. Read sk-thm-p1.json `realized`:
neither this item nor its pruned helper nodes realizes a unit statement or step;
the envelope/approximation/descent/Chow route is preserved. Compared old and
new proof_deps as sets: all ten removed direct dependencies are listed above.
Restored `lem-weil-pbc-qcqs-morphism-permanence`, since its clause (2) is used
explicitly to establish CompactSpace X and QuasiSeparatedSpace X.

5. **Nodes: pass after correction.** Existing node changes are limited to
proof, proof_deps and proof_origin. Each proof step names statements providing
the fact taken: the separated envelope; approximation and separated descent;
Noetherian Chow; projective-space/base-change and proper/surjective permanence;
closed-immersion base change; and the new coordinate embedding with immersion
composition (clause (e) of proper-fp-permanence). The new node's three steps
match the Lean graded surjection, affine Proj closed immersion, and base change.
Its source, statement dependencies, proof-dependency union, origin, chapter,
unit, creation, blueprint and verbatim Lean statement records are present.
The recorded unavailable LeanSearch request is honestly marked unavailable.
The stronger description that n may be |N| is witnessed by the proof's final
`refine ⟨Fintype.card N, ...⟩`.

Second reading changed only the original node's first proof step and
proof_deps to restore the qcqs permanence citation, and this report's pruning
list. Both Lean proofs were retained unchanged.
