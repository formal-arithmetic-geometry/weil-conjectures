## What changed

Proved `AlgebraicGeometry.exists_purely_inseparable_generic_base_spread` in
`lean/Sheaf/AlgebraicGeometry/PurelyInseparableGenericBaseSpread.lean` with its exact original
signature. Added proved private helpers `fraction_at_generic`, `perfectClosure_fractionRing`,
`perfectClosure_universalHomeomorphism`, and `evaluation_congr_inv`.

The concrete model is the spectrum of Mathlib's `Subalgebra.perfectClosure` of the section ring
inside the specified extension. Clearing a denominator proves that its fraction field is the
specified field. Integrality, lying over, and uniqueness of characteristic-power roots prove
that its spectrum map is a universal homeomorphism. Fraction-field uniqueness and evaluation
naturality prove compatibility with the specified embedding.

Added proof imports for Mathlib's function-field API and the source library's algebraic
universal-homeomorphism API. Updated the existing node's proof, proof dependencies, and proof
origin. Its statement and all existing public signatures and visibility remain unchanged.
The unit's route remains unchanged.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_purely_inseparable_generic_base_spread`
(node `lem-sbc-purely-inseparable-generic-base-spread`).
No holes remain in the module, and no holes were added or split off.
The four private helpers are fully proved.

The completed file compiles through lcompile.py. An explicit `#print axioms` check reports
only `propext`, `Classical.choice`, and `Quot.sound` for the main theorem.

## No longer needed

No original imports, named nodes, or modules were pruned: the original node had no proof
dependencies. The finite-generator selection and finite-subalgebra construction of the
original proof plan are unnecessary, since the conclusion only asks for integrality.
The existing finite-extension binder is preserved verbatim although this proof does not use it.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The original node compressed the entire algebra and scheme
argument into one step with no dependencies. The updated proof records the Mathlib generic
fraction-field leaf, lying over, the radicial field-point criterion, and the universal
homeomorphism definition.

Edge cases checked in the proof: characteristic zero uses exponential characteristic one;
its power-root uniqueness argument does not assume the target field has characteristic zero.
The denominator is nonzero by the fraction-field injection. Empty integral schemes are
excluded by the existing integral-scheme assumptions. No normality or Noetherian condition is
needed, and the model is not claimed finite. The original docstring retains the valid finite
construction from Tag 0559 as an alternative; the Lean proof and updated node use the full
power-root subalgebra instead.

## Second reading by J2

1. Compared the complete delivered Lean file and node against the repository versions.
   The original theorem signature, visibility, module header, and docstrings are byte for
   byte unchanged. The only Lean additions are four private proved helpers, two plain
   proof imports, and the replacement of the original `sorry`. There is no definition or
   statement change and no change record is required.
2. Compiled the delivered module with `lcompile.py`: exit 0, no warnings (5.2 seconds).
   Read each helper and the main proof. There are no remaining `sorry`s, new axioms,
   unsafe declarations, opaque declarations, or foreign implementations. The explicit
   scratch-copy axiom check for the main theorem reports only `propext`,
   `Classical.choice`, and `Quot.sound`; delivery also probes all declarations.
   The model B is the actual power-root subalgebra, not an arbitrary existence witness.
   The final field equivalence is the unique equivalence of the two fraction fields
   commuting with the section-ring maps.
3. No statement was split off and no new hole or node was introduced. Checked the helper
   edge cases: p=1 gives exponent one and identity root uniqueness even when the test
   field has different characteristic; for prime p the map from A forces the test field
   to have characteristic p. In denominator clearing p^n is positive, d remains nonzero
   under the injective field maps, and the scaled numerator has the asserted power.
   The existing integral assumptions exclude an empty scheme. No normality or
   Noetherian assumption enters the argument.
4. Read the construction of A-prime in the second proof of
   [Stacks Tag 0559](https://stacks.math.columbia.edu/tag/0559), and Tag 030R for its
   extension-field context. The existing statement asks for an integral affine model
   and universal homeomorphism, with no finite-morphism conclusion; using all power
   roots therefore satisfies every clause without weakening anything. Independently
   searched `lean/Sheaf`, `lean/WeilConjectures`, upstream's universal-homeomorphism
   algebra module, and Mathlib's purely-inseparable API. The additional LeanFinder
   query about perfect-closure subalgebras returned prime-spectrum homeomorphism lemmas,
   but no exact theorem for this generic spread or its universal base-change property.
   The upstream field-extension instance assumes a field base, so does not replace the
   argument for the section ring A. Both plain imports supply APIs used in the proof;
   both public imports supply notions used in the existing signature. No original
   proof dependencies existed to prune. Read `sk-prop-normal-form.json`: its realized
   statement and step lists are empty, and this change replaces no unit realization.
5. Read all four updated proof steps and the records for the generic affine fraction
   field, lying over, the radicial field-point criterion, and universal homeomorphisms.
   The cited fraction-field theorem supplies exactly the section-ring fraction-field
   structure; lying over uses the proved integrality and injectivity of A to B; the
   field-point criterion uses equality of the composites on A. The last step really
   proves compatibility with the specified embedding: evaluation naturality reduces
   it to the computed q.appTop identity, and fraction-ring extensionality extends
   equality on A to K. The node's proof, proof_deps union, and proof_origin agree with
   these steps. Its statement and lean record are unchanged.

Verdict: the proof passes the second reading. No Lean or node repair was necessary;
this second-reading section is the only change made by the second reader. Closed one
original hole, added zero holes: this is a proof, not a decomposition.
