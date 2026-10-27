## What changed

Preserved the complete statement of `WeilConjectures.isomorphismMultiplicationConeDescent`.
Its proof assembles three independent strict comparisons, constructs the isomorphism
on good representatives by whiskering and composition, and applies the existing
normalized uniqueness clause of `integralOperationsWellDefined` to descend it.
Postcomposition and inverse cancellation prove the representative equation;
naturality proves the formula for every isomorphism from every good representative.
Neither of those last steps is postponed.

The unclaimed `Sheaf.Paper.IntegralDerivedOperations` packages its existing
normalized pullback functor, comparison and universal property in
`IntegralPullbackDescent` and `integralPullbackDescent`, following the tensor record
already in that module. Both existing public pullback definitions retain their
signatures and reduce to precisely their old choices through the new projections.
The item uses the record's universal field instead of opening nested existential
choices. No data is chosen anew, no proof is postponed, and this module has zero
holes. The consumer audit confirms definitionally equal values; the audit and
exact old/new bodies are in `coord/changes/V2-integral-pullback-descent-model.md`.

The seven existing strict-quotient definitions move to
`Sheaf.TraceFormula.IsomorphismStrictQuotientModels`, publicly re-exported by the
item. All seven types and bodies are preserved. The five former abbreviations use
`@[reducible] def` to preserve elaborator reducibility with ordinary kernel hints.
The relocation avoids cyclic imports for the three smaller lemmas. The item's eight
previous public imports remain. No existing signature, mathematical definition,
universe, hypothesis, or source-library declaration changes.

The normalized pullback section and comparison modules locally prefer
`integralTowerHasDerivedCategory` at priority 3000, matching `IntegralOperationsWellDefined`. They use the same standard
localization, and no global instance priority or existing registration changes.

The retained draft's import failures have cleared. This attempt repairs its actual
elaboration failures: normalized descent uses the packaged universal property; the component
of the whiskered comparison is simplified explicitly; the two invertible maps are
cancelled directly; and naturality transports the result to every resolution.
Private proved helpers keep naturality, cancellation of two inverse pairs,
and the logical combination of independent witnesses abstract. The complete descent and its two component formulas are proved in the
private lemma `assembled_cone_descent`. Local irreducibility attributes keep the
strict Roos and tower constructions closed during that proof; their original
reducibility is restored for the public theorem's coordinate statement. Private comparison builders, their proved component formula and the full
normalized descent argument handle functor reassociation and naturality before
specialization to Roos complexes. The mathematical values of
the exported definitions are unchanged. The completed
commutative-ring presentation and `sheafCompose` are locally `implicit_reducible`,
as in the neighboring normalization modules, so instance checking sees their
unchanged underlying ring sheaf. The item enables respect for local transparency controls.
No check is disabled and the 60-second limit is preserved.

Validation: all six modules passed clean single-file compilation and the local axiom checks. The assigned module's
final proof passed in 54.7 seconds. Profiling options are removed from the delivered
source. The required delivery tool performs compilation and the packet checks.
The assigned theorem and both existing pullback definitions retain their exact
textual signatures. All six Lean files have lines of at most 100 characters.

## Proved and sorry left

Closed one original hole:
`WeilConjectures.isomorphismMultiplicationConeDescent`, by a complete assembly and
descent proof from the three lemmas below and existing library declarations.

Added holes, each the whole body of its named public theorem in its own module:

- `WeilConjectures.isomorphismStrictQuotientMultiplication`
  (`lem-trf-isomorphism-strict-quotient-multiplication`): multiplication on the
  actual strict quotient tower, with the two unit-generator equations (steps 3--4).
- `WeilConjectures.isomorphismQuotientRoosComparison`
  (`lem-trf-isomorphism-quotient-roos-comparison`): product invertibility, the
  difference square and diagonal cone comparison (steps 1 and 5).
- `WeilConjectures.strictQuotientCompletionRealization`
  (`lem-trf-strict-quotient-completion-realization`): the normalized completion
  comparison on simultaneous strict presentations (steps 2 and 8).

No `sorry` remains in the item.
No data definition has a hole. The common definition module and repaired pullback
dependency module have zero holes. Hole accounting: one upper hole replaced by three
strictly smaller holes; this is a decomposition, not a net reduction of the sorry count.
The derived natural isomorphism, its representative equation and its every-resolution
formula have complete, compiling Lean proofs from the three named lemmas.

Edge cases checked mathematically: the identity scheme isomorphism gives ordinary
multiplication and identity product comparison; the zero complex gives zero towers
and zero cones; n=0 means the positive first quotient exponent 1, so no nonexistent
zeroth quotient is used. The cone formula applies to all integer degrees, including
negative degrees; no boundedness or completeness assumption was introduced. Scalar
formulas are on sheafified unit generators, not an assertion that arbitrary sections
of the sheafification are pure tensors.

## No longer needed

The new common module retains only three direct public imports; five other direct
imports were already supplied transitively by those three. The item preserves all
eight of its existing public imports.

Removed these unused proof-only imports from the item:

- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`;
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`;
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso`;
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`.

The item does not directly invoke `lem-pc-kflat-resolution`,
`lem-weil-proetale-countable-products-exact`,
`lem-weil-sheaf-scalar-extension-ring-iso`,
`lem-weil-strict-roos-comparison`,
`lem-cbc-exact-product-functor-strict-limit`,
`def-pur-sheaf-tensor-product`, or
`lem-weil-pbc-site-derived-tensor-descent`.
Their uses in the strict-comparison plans are retained below the corresponding
new statements. The item needs no separate homotopy descent or localization theorem:
its existing normalized pullback universal property already descends the assembled
comparison and specifies its representative components. The final equation is a
consequence of naturality and inverse cancellation. No entire module is claimed
unreachable, and no module or DAG node is withdrawn. The unit route is retained.

## Where the brief, the DAG or earlier work was wrong

The generic scalar-extension and exact-product declarations do not directly give
the comma-normalized strict-tower and cocone equations in this item. The three
new statements isolate those constructions and the simultaneous-presentation
normalization, rather than replacing the derived theorem by a renamed copy.

No statement error was found. The previous attempt's missing published object files
are available again. Its proof also needed the elaboration repairs described above.
The original plan's separate
localization/natural-transformation argument is already available in the normalized
uniqueness clause of `integralOperationsWellDefined`. Reusing that clause avoids
reproving the homotopy and localization infrastructure. A search also found
`NormalizedCompletionRealization.descent_data`, but it obtains rho by applying this
very item, so using it here would be circular; it was not imported.

The current `literature/blueprint/latest/` snapshot reorganizes trace transport and
no longer contains the integral-model page cited by this older assigned node.
The delivery preserves the assigned statement and the recorded unit route; it
uses the existing node's strict-system argument and its Stacks references.

## New nodes

`def-trf-integral-pullback-descent-model` records the existing normalized pullback
data, its proved universal property and the definitionally unchanged projections.
It adds no mathematical assumption or new choice.

`def-trf-isomorphism-strict-quotient-models` attaches the seven definitions with
unchanged types and bodies to their common module; it introduces no alternative
mathematical object. Five declarations use ordinary kernel hints while retaining
their original elaborator reducibility.
`lem-trf-isomorphism-strict-quotient-multiplication` isolates steps 3--4.
`lem-trf-isomorphism-quotient-roos-comparison` isolates steps 1 and 5.
`lem-trf-strict-quotient-completion-realization` isolates steps 2 and 8.
Each theorem is strictly part of the argument and has a complete proof in words,
source citations and recorded Mathlib searches. The original node's Lean attachment
and proof route now follow the delivered assembly.

Change records: `coord/changes/V2-isomorphism-strict-quotient-models.md` and
`coord/changes/V2-integral-pullback-descent-model.md`.

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
