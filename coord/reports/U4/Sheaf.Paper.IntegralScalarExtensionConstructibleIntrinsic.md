## What changed

Proved `WeilConjectures.sfIntegralScalarExtension_constructible` in
`lean/Sheaf/Paper/IntegralScalarExtensionConstructibleIntrinsic.lean`, with its existing
signature unchanged. The proof uses `purCoefficientModel` and
`purCoefficientModel_predicates` to compare intrinsic and unrestricted completeness on
an object isomorphic to the input. Their finite-reduction constructibility predicates
and uniform intervals agree definitionally. It applies the existing
`integralScalarExtension_constructible` theorem and transports its conclusion back
through the target counit and the image of the source counit. No geometric finiteness
hypothesis is used. The restricted functor and its already proved linearity are unchanged.

The proof adds private imports of `IntegralScalarExtensionConstructible`,
`CompletedCoefficientPresentationTransport`, and `SfIntegralConstructibleTriangulated`
(all under `Sheaf.Paper`). The public imports remain unchanged. The owning node records
the intrinsic transport argument, the complete retained legacy proof route, and the linearity step.

Repair of reviewer C-7f34a (returned head 7f34aa450a), points 1–4:

1. Kept delivered proof steps 1, 3, and 4 unchanged. Replaced delivered step 2 by a
   contextual introduction for the transported object K₀, followed by the seven
   sheaf-dag preservation steps verbatim, including their uses, elementary flags,
   and source records. The old eighth linearity step is not duplicated.
2. Restored the sheaf-dag list of 15 proof dependencies in its original order and
   appended `def-pur-completed-coefficient-presentation-transport` and
   `lem-weil-integral-constructible-triangulated`.
3. Restored all eight sheaf-dag `tool_uses` entries byte for byte and in order.
4. Set `proof_origin.place` to the exact wording requested in the return.

The Lean file is unchanged from the returned delivery.
No statement or definition repair, consumer adaptation, or new module is delivered.

## Proved and sorry left

Closed 1 of the 1 holes present in the current item:
`WeilConjectures.sfIntegralScalarExtension_constructible`
(node `lem-weil-integral-scalar-extension-constructible`). Added 0 holes; split off 0
statements. No `sorry` remains in the delivered module. The already landed
`sfConstructibleIntegralScalarExtension_smul` proof is retained unchanged.

The existing `WeilConjectures.integralScalarExtension_constructible` in
`Sheaf.Paper.IntegralScalarExtensionConstructible` remains an unproved dependency, with
the same owning node. Applying this pre-existing legacy declaration is permitted proof
reuse; no new restatement is introduced. The DAG records the seven steps of the retained residue-layer, finite-filtration,
and normalized-tower argument for this intra-node application without a self-edge. The coefficient completeness comparisons also
remain existing proof dependencies. This delivery proves the intrinsic interface from
those declarations; it does not claim to close their holes.

Validation: the retained proof passed a fresh `deliver3.py --no-push` compile and server
preflight. The object-level argument is valid for the empty scheme, zero object, equal
coefficient fields, and arbitrary schemes: it uses only coefficient equivalences and
isomorphism closure, with the same finite-level bounds.

## No longer needed

The following direct proof imports are removed from the current item:

- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`
- `Mathlib.Algebra.Homology.HomologicalComplexLimits`
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
- `Mathlib.CategoryTheory.Abelian.FunctorCategory`
- `Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic`
- `Mathlib.CategoryTheory.Limits.FunctorCategory.Basic`
- `Mathlib.CategoryTheory.Sites.Abelian`
- `Mathlib.CategoryTheory.Sites.Sheafification`
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses`
- `Sheaf.CategoryTheory.SiteInverseImageTensor`
- `Sheaf.CategoryTheory.StrictRoosDerivedLimitComparison`
- `Sheaf.CategoryTheory.Triangulated.DerivedLimitProducts`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`
- `Sheaf.Paper.FiniteFieldSheafScalarExtension`
- `Sheaf.Paper.IntegralScalarExtensionUniverses`
- `Sheaf.Paper.IntegralScalarExtensionWellDefined`
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`
- `Sheaf.Paper.NormalizedDVREffectivity`
- `Sheaf.Paper.NormalizedDVRTower`
- `Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated`
- `Sheaf.Paper.ProEtaleConstructibleSheaf`

No DAG node or library module is pruned. All 15 legacy proof dependencies remain
necessary for the legacy declaration used by the intrinsic proof, and all eight approved
tool uses remain recorded. The list above describes only imports removed directly from
the intrinsic module; it does not remove the legacy module's proof obligations.
`Sheaf.Paper.IntrinsicFiniteTorsionConstructibility` remains publicly available through
the unchanged public import of `SfIntegralConstructible`, so removing its redundant
direct proof import bypasses no unit statement. The unit record has no realized
statement or steps for this auxiliary lemma.

The retained earlier helper attempts `IntegralScalarFiniteBounds`,
`IntegralScalarFiniteLevelBounds`, and `IntegralScalarTowerEffectivity` (under
`Sheaf.Paper`) are kept only in the sandbox scratchpad and are not delivered or imported.
No existing library module is withdrawn, and no new node is delivered.

## Where the brief, the DAG or earlier work was wrong

The retained first attempt duplicated a finite-filtration and normalized-tower argument
already stated by the legacy preservation theorem. The intrinsic interface instead
follows by the existing canonical coefficient presentation equivalence. Its completeness
comparisons have no Noetherian or dimension hypothesis; the separate bounded-predicate
comparison, which does require geometric hypotheses, is not used.

The old report overstated pruning: the finite-level theory is still needed to prove the
legacy dependency. This report distinguishes removed direct imports from that remaining
work. Reviewer C-7f34a correctly required that the owning node retain this route as well:
the legacy declaration and intrinsic declaration share the node. The repaired node
therefore includes both the intrinsic transport and the verbatim seven-step legacy
preservation argument. Restoring the tool approvals corrects the prior unjustified
withdrawal; no mathematical route has been pruned.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
