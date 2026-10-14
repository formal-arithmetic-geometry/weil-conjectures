## What changed

Replaced two holes in `WeilConjectures.ConstructibleSheaf.FinitePushforward` with compiling proofs from the existing library and three new proved helper modules. Finite presentability uses a finite affine-free presentation and preservation of filtered colimits by affine etale sections. Noetherian descent reindexes the existing Noetherian approximation by a directed partial order and descends the affine-free presentation and relations. Every original declaration signature and visibility is unchanged. The added helpers generalize the finite-coefficient support, presentation, and limit-descent arguments to the coefficient generality required by the source module. Their public theorems have complete proofs from existing declarations, with no local `sorry`.

## Proved and sorry left

Closed 2 of the 4 original holes:

- `AlgebraicGeometry.Etale.isFinitelyPresentable_of_isConstructibleSheaf` — `lem-weil-pbc-constructible-finitely-presented`.
- `AlgebraicGeometry.Etale.exists_isNoetherian_upperStar_iso` — the descent step of `lem-weil-pbc-constructible-finite-pushforward-approximation`.

Remaining original holes:

- `AlgebraicGeometry.Etale.isIso_unit_constantSheaf_of_isIntegrallyClosed` — `lem-weil-pbc-normal-constant-generic`; needs the normal strict-henselization generic-fibre argument and its compatibility with the adjunction unit.
- `AlgebraicGeometry.Etale.exists_mono_biproduct_lowerStar_of_isNoetherian` — `lem-weil-pbc-constructible-finite-pushforward-noetherian`; needs normalized generic trivialization, finite-stage factorization of integral pushforward maps, and finite stalk-test selection in the Noetherian-coefficient module generality.

Added no `sorry` declarations. Existing imports may still rest on their own documented holes, as intended by stage 3. All four delivered modules compile without warnings. The dry run checks the declarations' axioms as well as the source files.


Explicit scratch `#print axioms` checks found only `propext`, `Classical.choice`, and
`Quot.sound` for `AlgebraicGeometry.Etale.isFinitelyPresentable_of_isConstructibleSheaf`,
`AlgebraicGeometry.Scheme.constructibleModuleSupport_general`, and
`AlgebraicGeometry.Scheme.exists_affine_free_etale_presentation_general`.
`AlgebraicGeometry.Etale.exists_isNoetherian_upperStar_iso` and
`AlgebraicGeometry.Scheme.exists_constructible_limit_descent_general` additionally use
`sorryAx` through the existing `AlgebraicGeometry.Scheme.exists_affineEtaleSite_colimit`
input (the eventual-hom-lift and free/shriek comparison inputs themselves pass without
`sorryAx`). Thus finite presentability is fully proved;
Noetherian descent closes its local hole by reduction to the existing limit-descent inputs.
No lower hole is added by this delivery.

## No longer needed

Removed these direct proof-only imports from the item module:

- `Sheaf.AlgebraicGeometry.ConstantSheafGeometricStalk`
- `Sheaf.AlgebraicGeometry.ConstructibleFiniteSelection`
- `Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePresentation`
- `Sheaf.AlgebraicGeometry.EtaleLocalRingTriples`
- `Sheaf.AlgebraicGeometry.EtaleSheaves`
- `Sheaf.AlgebraicGeometry.NormalScheme`
- `Sheaf.AlgebraicGeometry.StrictHenselization`
- `Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula`
- `Sheaf.RingTheory.EtaleColimitNormalLocalDomain`
- `Sheaf.RingTheory.StrictHenselizationTriples`
- `WeilConjectures.AlgebraicGeometry.Sites.ConstantSheafSections`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`

The finite-presentability route uses `new-constructible-affine-free-presentation-general` instead of `lem-weil-pbc-constructible-module-finite-presentation`, whose Lean statement assumes a finite coefficient ring. The descent step uses `new-constructible-limit-descent-general` instead of the finite-coefficient `lem-weil-pbc-constructible-module-noetherian-descent` wrapper. Thus those specialized modules are unnecessary to these two proofs. The normal and Noetherian-embedding holes retain their mathematical plans; their proof-only imports are absent until a proof actually uses them. No UNIT realization is bypassed.


The second reader additionally removed the redundant direct proof import
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, already public through
`WeilConjectures.ConstructibleSheaf.Defs`, and made
`Mathlib.AlgebraicGeometry.AffineTransitionLimit` a plain proof import in the new descent module.

Every old proof dependency removed from the two revised DAG nodes is listed here:

- `lem-weil-pbc-constructible-module-finite-presentation`
- `lem-weil-pbc-filtered-colimit-sets-elementwise`
- `def-weil-pbc-category-colimit`
- `def-weil-sheaf-of-modules-category`
- `def-weil-presheaf-modules-sheafification`
- `lem-weil-pbc-affine-morphism-permanence`
- `def-weil-pbc-scheme-conventions`
- `lem-weil-pbc-constructible-module-noetherian-descent`
- `lem-weil-pbc-constructible-module-finite-pushforward-noetherian`

These are removed direct proof dependencies; definitions and shared modules may still be
needed transitively or by other targets. A source import-graph comparison from `TargetsCheck`
finds one module leaving the targets' closure:
`Sheaf.RingTheory.EtaleColimitNormalLocalDomain`. The maintainer's pinned sorry ledger remains
the authority for progress counts.

## Where the brief, the DAG or earlier work was wrong

The relevant existing Sheaf presentation and descent APIs assume `[Finite Λ]`, whereas the source declarations require only `[IsNoetherianRing Λ]`. Applying the finite-coefficient APIs directly does not prove the source signatures. This delivery proves the general forms, using `IsConstructibleSheaf` and module finite generation. Earlier notes about the source constructibility interface lacking constructible strata are stale: the current definition includes them. The four, rather than five, original holes were confirmed by the delivery declaration parser; the approximation and final embedding declarations already had proofs.

## New nodes

`new-constructible-module-support-general` attaches `AlgebraicGeometry.Scheme.constructibleModuleSupport_general` in `lean/Sheaf/AlgebraicGeometry/ConstructibleModuleSupportGeneral.lean`. It proves geometric-point independence of vanishing and constructibility of support for arbitrary commutative coefficients, including zero sheaves and empty strata.

`new-constructible-affine-free-presentation-general` attaches `AlgebraicGeometry.Scheme.exists_affine_free_etale_presentation_general` in `lean/Sheaf/AlgebraicGeometry/ConstructibleAffineFreePresentationGeneral.lean`. It proves a finite presentation from finite stalk generators, constructible cokernel support, compactness in the constructible topology, and constructibility of kernels over a Noetherian coefficient ring.

`new-constructible-limit-descent-general` attaches `AlgebraicGeometry.Scheme.exists_constructible_limit_descent_general` in `lean/Sheaf/AlgebraicGeometry/ConstructibleLimitDescentGeneral.lean`. It descends the finite affine families and their matrix of relations, then forms their cokernel at one stage and compares its pullback with the original sheaf. No change record is needed: the delivery changes no existing statement, definition, visibility, or public import.

## Second reading by X2

1. **Interfaces: pass.** Read the complete diff of the item against the repository and
   compared the declaration parser's statements and visibility for all eight existing
   declarations. They are unchanged. Only two original proof bodies, private helpers,
   and proof imports change. The other three modules and their nodes are new; no existing
   definition or target interface changes, so no change record is required.
2. **Proofs and trust: pass.** Compiled all four files through `lcompile.py` in import order,
   without errors or warnings. Inspected every new definition: each is an explicit
   composition of adjunction equivalences or a representability comparison, with no
   arbitrary witness chosen from an unproved existence theorem in a definition. The two
   remaining direct `sorry`s are exactly the original named normal-unit and Noetherian
   embedding theorems reported above. No forbidden declarations or hidden holes occur.
   Scratch axiom checks give the exact distinction recorded above: finite presentability
   and its support/presentation helpers have only the three allowed axioms; descent still
   depends on upstream `sorryAx`. The delivery tool also probes every delivered declaration.
3. **New statements and searches: pass.** There are no split-off holes. Read all three
   helper proofs and their nodes. The support theorem uses zero-stalk independence,
   constant-stalk comparisons, open etale cover images, and the finite stratification;
   its topological argument makes a clopen subset of a constructible stratum constructible.
   The presentation theorem uses finite stalk generation, compactness of the constructible
   topology, and the Noetherian kernel theorem. Descent uses affine site object descent,
   eventual hom lifting, and preservation of cokernels. Checked empty schemes/strata,
   zero sheaves, empty sums, and a nonfinite coefficient ring such as the integers:
   finite generation, rather than finiteness of the underlying module, is what is used.
   Searched `lean/Sheaf`, `lean/WeilConjectures`, the source checkout, and Mathlib with
   `rg`, plus fresh LeanFinder, Loogle, and recorded `msearch.py` grep queries.
   The existing support, presentation, family-model, arrow-descent, and descent APIs all
   require `[Finite Λ]`; the new general forms are needed for the unchanged signatures.
   Mathlib's sheaf-of-modules finite-presentation results use a different interface and
   supply no shorter proof of these etale constructibility statements.
4. **Route and pruning: pass after report/import repairs.** Read
   `dag/units/sk-thm-p1.json`, especially its `realized` statement and four steps.
   None of the replaced presentation/descent tool nodes is a realized unit step;
   the chapter/unit route, finite-pushforward embedding, and finite base change remain.
   The finitely presentable proof is the finite-colimit route of 09Z4/095N/0738.
   Descent retains the common-stage objects, relation arrow, and cokernel argument of
   09YU. Added the complete list of removed old proof dependencies above. Removed the
   redundant UpperLowerStar.Defs import and changed the new descent module's proof-only
   AffineTransitionLimit import from public to plain.
5. **DAG agreement: pass after metadata cleanup.** Read each delivered node's proof,
   proof_deps, proof_origin, source, Lean attachment, and creation/search fields.
   The existing nodes now describe the affine-free finite-colimit proof and directed
   Noetherian descent actually written in Lean. Each new node has the required fields
   and records its public theorem. Removed six copied blueprint-history fields from each
   new node: they described the parent finite-presentability lemma instead of that new
   statement. Kept the actual blueprint ancestry, chapter, unit, proofs and sources.

Second reading changed imports, removed stale copied metadata from the three new nodes,
and completed pruning and axiom reporting. It changed no proof argument or existing signature.
