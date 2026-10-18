## What changed

Replaced the one sorry in
`AlgebraicGeometry.isConstructibleEtaleModuleSheaf_higherDirectImage_prime_of_projective_curve`
by a complete compatibility proof using the existing source-library theorem
`AlgebraicGeometry.Etale.isConstructibleSheaf_homology_rightDerivedLowerStar_zmod`.
No theorem signature, definition, instance, visibility or public import changed.

The proof extracts the closed projective embedding from `IsProjective`, constructs
`HasInvertibleExponent` using the prime and the supplied unit, and converts the given
algebraic-closure fibre bound to the source theorem's arbitrary algebraically closed
field-valued fibre bound. For the latter, every field-valued point factors through its
residue field; both its fibre and the prescribed algebraic-closure fibre have the same
dimension as that residue-field fibre, by the proved
`topologicalKrullDim_pullback_eq_of_field`.
Finally `rightDerivedFunctorPlusCompatibility` identifies the cohomology sheaves, and
`isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf` converts constructibility.
These operations also cover negative degrees and empty schemes without new assumptions.

The node is reattached to the existing source theorem, which explicitly cites this
same blueprint label. This avoids treating its mathematical statement as a new
split-off node. Its original nine-step proof and proof dependencies remain, since
that source theorem is still open. The former attached declaration is now a proved
API wrapper. The node's proof_origin records this reuse.

New proof imports:

- `WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison`
- `WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension`
- `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ProjectiveCurve`

Validation: the delivered module compiles through lcompile.py, without warnings.
No new module, theorem, definition or sorry is introduced.

## Proved and sorry left

Closed 1 of the assigned module's 1 holes:
`AlgebraicGeometry.isConstructibleEtaleModuleSheaf_higherDirectImage_prime_of_projective_curve`.
The assigned module now has zero textual sorry. Added zero holes; split off zero statements.

This is reuse of an existing theorem, not an independent proof of projective-curve
finiteness. The existing source declaration
`AlgebraicGeometry.Etale.isConstructibleSheaf_homology_rightDerivedLowerStar_zmod`
still contains sorry and is the canonical remaining obligation of node
`thm-fin-projective-curve-constant`. Its proof imports also reach other existing
obligations. No claim of sorry-free transitive axioms or positive net target-closure
progress is made; the ledger measures that separately.

## No longer needed

Removed the following proof-only imports from this wrapper:

- `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Sheaf.AlgebraicGeometry.ConstantFiniteComparison`
- `Sheaf.AlgebraicGeometry.ConstructibleSubsheafNoetherian`
- `Sheaf.AlgebraicGeometry.FiniteConstructibleDirectImage`
- `Sheaf.AlgebraicGeometry.FiniteGenericCurveModel`
- `Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison`
- `Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange`
- `Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper`
- `Sheaf.AlgebraicGeometry.ProjectiveSmoothCurveFiniteness`
- `Sheaf.AlgebraicGeometry.UniversalHomeomorphismInvariance`
- `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact`
- `WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm`
- `WeilConjectures.ConstructibleSheaf.Biproduct`
- `WeilConjectures.ConstructibleSheaf.Defs`
- `WeilConjectures.ConstructibleSheaf.Pullback`
- `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine`
- `WeilConjectures.SixFunctors.Finite.Stalk`

No mathematical dependency node is declared obsolete: the canonical source theorem
still needs the original generic-model, comparison, descent and Noetherian-induction
argument. In particular its original proof_deps and tool_uses are retained, rather
than pruning obligations merely because an equivalent source declaration was reused.
The retained public imports serve the unchanged statement/API.

## Where the brief, the DAG or earlier work was wrong

The node's Lean attachment overlooked the source theorem with the identical blueprint
label in `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ProjectiveCurve`.
Its different interfaces (explicit projective embedding, all algebraically closed
field-valued points, invertible exponent, total derived category, finite-stalk
constructibility) require the conversions implemented here, but do not require a
second mathematical proof or new intermediate statements. Reattaching the original
node preserves the outstanding mathematical work instead of hiding it behind the
proved wrapper. No statement was disputed or weakened. The unit record has no
realized statement or proof steps to bypass; the mathematical route is preserved.

## Forced adaptations

The returned delivery failed with this import cycle:

`Sheaf.AlgebraicGeometry.ProjectiveCurveConstant -> WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ProjectiveCurve -> WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage -> WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Proper -> WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Projective -> Sheaf.AlgebraicGeometry.ProjectiveLineConstructible -> Sheaf.AlgebraicGeometry.ProjectiveCurveFiniteGroup -> Sheaf.AlgebraicGeometry.ProjectiveCurveConstant`.

The adapted module `lean/Sheaf/AlgebraicGeometry/ProjectiveCurveFiniteGroup.lean`
(currently unclaimed) removes only its unused proof-only import of
`Sheaf.AlgebraicGeometry.ProjectiveCurveConstant`. The original module fails by
the cycle above; the adapted module compiles with the item and preserves every
existing declaration and signature. This forced line removal is recorded in
`coord/changes/ProjectiveCurveFiniteGroup-import-cycle.md`.

## Second reading by J5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
