## What changed

Proved `AlgebraicGeometry.cartesian_tensor_data_comparison` in
`Sheaf.AlgebraicGeometry.CartesianTensorDataComparison` without changing its signature,
visibility, definitions or existing docstring. Added proof-only imports of
`DerivedDirectImageCompositionUnbounded`, `DerivedAdjoint`,
`DerivedPullbackMonoidalModel` and `PointwiseLeftDerived`. The existing public import
closure already supplies derived pullback composition and the exact-functor API.

The proof first applies the existing canonical relatively flat tensor base-change theorem.
It then uses the scheme isomorphism supplied by `sq.isoPullback`, the invertible unit of
the derived adjunction, direct-image composition, and the derived pullback tensorator.
Two proved private helpers show that tensor pullback along a scheme isomorphism is an
equivalence and that its exact termwise functor computes derived pullback of any complex.
Finally the given degreewise comparisons produce an actual complex isomorphism, which
is mapped by Q, tensored with the given identification of E, and pushed forward.

Updated the existing node's proof, proof dependencies and proof origin to record this
argument, including the adjunction and monoidal model previously implicit in the plan.
The unit's route is retained. The adjunction and monoidal-model nodes are generic tools;
they do not replace any semicontinuity or base-change unit step.

Validation: the complete module compiles locally with no errors or warnings. All lines
are at most 100 characters. The statement uses ordinary termwise pullback of G throughout;
no O_X-flatness, perfectness or extra geometric hypothesis is introduced. Exactness is
used only for pullback along the scheme isomorphism, so zero complexes and empty schemes
are covered by the same constructions.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.cartesian_tensor_data_comparison`
(node `lem-pc-cartesian-tensor-data-comparison`).

Added zero holes. No `sorry` remains in the delivered module. Both private helpers,
`tensorPullback_iso_equivalence` and `iso_pullback_computes`, are proved.
This is a proof from existing library declarations, not a decomposition into new holes.

## No longer needed

No original import, planned dependency node, or planned dependency module was
removed. The second reader removed the redundant added proof-only imports
`Sheaf.AlgebraicGeometry.DerivedPullbackComposition` and
`Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`; their APIs remain available
through the retained import closure, and their used DAG dependencies remain recorded. No new intermediate node or module is needed: the scheme-isomorphism transport
and complex-identification glue are proved in this module. The exploratory import-pruning
check confirmed `PointwiseLeftDerived` is required for
`Functor.isLeftDerivedFunctor_of_inverts` and it remains imported.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The original plan implicitly required the
strong monoidal derived-pullback comparison and the derived adjunction; the updated DAG
makes these dependencies explicit. Computing ordinary pullback of G under the scheme
isomorphism requires exactness, not the bounded-above flat-complex lemma (whose O_X-flat
hypothesis is unavailable here). Exactness follows from the ordinary pullback equivalence,
and the uniqueness of left-derived functors supplies the comparison without a new hole.

Lean's native `Scheme.Modules` carrier hides the shared sheaf category from instance
search when an exact derived functor is inferred without a type annotation. The helper
therefore types its ordinary functor explicitly on the shared `SheafOfModules` categories;
no category, localization or instance is replaced.


## Second reading by S3

1. PASS: compared the sole delivered module with the read-only repository version.
   The existing theorem signature is byte for byte identical. The docstring and all
   existing public imports are unchanged; no definition or public interface changed.
   The node changes only `proof`, `proof_deps` and `proof_origin`.
2. PASS: independently compiled the module without errors or warnings. A scratch-copy
   `#print axioms` probe checked the target and both private helpers. The ordinary
   pullback equivalence uses only `propext`, `Classical.choice`, `Quot.sound`; the
   computation helper and target also use `sorryAx` inherited from existing imported
   declarations. No delivered declaration contains `sorry`, and there are no new
   axioms, unsafe code, opaque declarations, foreign implementations or definitions.
   Chosen isomorphisms and adjunctions are used locally in proofs of propositions;
   no object is defined by choosing an arbitrary witness of an open existence claim.
3. PASS: zero split-off statements and zero new nodes. Independently searched Loogle
   for functor equivalences, Lean Finder for exact-functor derived computation, and
   both Lean roots for tensor-pullback equivalences and derived-computation lemmas.
   The Mathlib exact-functor API used here is the relevant shorter route; the existing
   open-restriction analogue does not cover arbitrary scheme isomorphisms. Both private
   helpers are proved categorical glue. Identity squares, zero complexes and empty
   schemes require no exceptional hypotheses. The equation `he` supplies exactly the
   complex-map compatibility, with its direction reversed for `isoOfComponents`.
4. PASS after import cleanup: the proof starts with the existing canonical relatively
   flat base-change theorem, then transports along the cartesian-square isomorphism.
   The unit `sk-thm-picard-semicon` and its `realized` record are unchanged; no unit
   step is bypassed. Every original proof dependency remains used, so the original
   `No longer needed` list has no omitted node. Scratch removal checks showed that
   the added `DerivedPullbackComposition` and `ExactFunctor` imports are redundant;
   removed both. Each of the four remaining added imports is necessary: deleting it
   makes the corresponding referenced declaration unavailable.
5. PASS: read the updated node and the recorded declarations of all its dependencies.
   The steps describe the actual equivalence, adjunction unit, exact-computation,
   tensorator and complex-identification argument. `proof_deps` is exactly the union
   of the steps' `uses`, and `proof_origin` identifies the source and implemented route.
   No new-node requirements apply.

Second-reading changes: removed the two redundant added proof-only imports and updated
this report. Kept the correct proof and node unchanged. One original hole is closed,
zero holes are added; this is not a decomposition. The inherited `sorryAx` means this
is a local hole closure, not a claim that the target's entire dependency closure is proved.
