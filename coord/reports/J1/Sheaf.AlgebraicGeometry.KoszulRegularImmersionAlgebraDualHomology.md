## What changed

Proved `AlgebraicGeometry.koszulRegularImmersion_algebraDual_homology` in the assigned
module, with its public signature and public imports unchanged. The proof reuses
`AlgebraicGeometry.koszulRegularImmersion_derivedInternalHom` for the scalar calculation,
then upgrades the scalar cohomology isomorphism to an algebra-module isomorphism.

Three fully proved private helpers supply the glue:
`closedImmersion_scalar_locallySurjective` lifts ring sections on affine neighborhoods;
`scalarRestriction_fullyFaithful` uses Mathlib's locally-surjective restriction Hom
equivalence; and `koszulRegularImmersion_scalar_homology` takes homology of the existing
scalar derived-Hom comparison. The last helper computes through one actual K-injective
resolution in both the standard and the given derived universe, so it adds no assumption
on the derived universe of Z. The main proof uses uniqueness of right adjoints, exact
scalar restriction commuting with homology, and fully faithful lifting of isomorphisms.

Added proof imports: `Sheaf.AlgebraicGeometry.KoszulRegularImmersionDerivedHom`,
`Sheaf.AlgebraicGeometry.DerivedRHomAlgebraModule`,
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory`,
`Mathlib.Algebra.Homology.ShortComplex.Homology`, and
`Mathlib.Topology.Sheaves.LocallySurjective`. Retained the affine evaluation comparison.
Updated the assigned DAG node's proof, proof dependencies and proof origin accordingly.
No definitions or existing signatures changed; no other module was adapted.

## Proved and sorry left

Closed the one hole in `AlgebraicGeometry.koszulRegularImmersion_algebraDual_homology`
(node `lem-sc-koszul-regular-immersion-algebra-dual-homology`).
There are zero remaining sorries in the assigned module and zero newly added holes.
All three private helpers are proved. This is a proof from existing named dependencies,
not a decomposition into newly holed statements.

The existing `AlgebraicGeometry.koszulRegularImmersion_derivedInternalHom`
(node `lem-sc-koszul-regular-immersion-derived-hom`) remains an unproved dependency in
its original module; this delivery does not claim to close its hole or the transitive
holes beneath it. The proof compiles through the prescribed single-file compiler.
The delivery dry run also checks compilation, preserved interfaces and forbidden axioms.

## No longer needed

Removed four direct proof imports and corresponding direct proof dependencies:

- `Sheaf.RingTheory.KoszulRegularSequenceDualComplex`
  (`lem-sc-koszul-regular-sequence-dual-complex`).
- `Sheaf.AlgebraicGeometry.AffineModuleCorrespondence`
  (`lem-weil-pbc-affine-module-correspondence`).
- `Sheaf.Algebra.Homology.DerivedHomFiniteFreeModel`
  (`lem-sc-derived-hom-finite-free-model`).
- `Sheaf.Paper.DerivedInternalHomRestrictOpen`
  (`lem-sc-derived-internal-hom-restrict-open`).

These local calculations are no longer repeated here: the existing scalar theorem
encapsulates them. They remain reachable through other imports, including that scalar
theorem and the public direct-image-algebra definitions. Consequently this is pruning of
the assigned node's direct proof route, not a claim that these modules have left the
whole targets' import closure. No unit statement or realized unit step is bypassed;
`dag/units/sk-thm-picard-duality.json` has empty realized statement and step lists.

## Where the brief, the DAG or earlier work was wrong

The planned separate verification of the algebra action is unnecessary for a closed
immersion: locally surjective restriction of ring scalars is fully faithful, so every
scalar-module morphism between these algebra-module sheaves is already algebra-linear.
The scalar Koszul theorem was already available and does not reach the assigned module
(the import-direction check returned yes). Its same-universe derived-category binder
on Z prevents a direct application in the arbitrary given universe; computing through
a common K-injective Hom complex resolves this without changing either signature.

The local Stacks source file is absent in this checkout. Read the official sources
[Tag 0BQZ](https://stacks.math.columbia.edu/tag/0BQZ) and
[Tag 0AX3](https://stacks.math.columbia.edu/tag/0AX3), and the existing theorem's complete
DAG proof and Lean signature. No new mathematical statement with an unproved proof is
introduced. Negative degrees, empty schemes, empty rank strata and rank zero require
no additional hypothesis: the existing scalar theorem and zero-differential homology
calculation cover them, while affine local scalar lifting holds independently of rank.

## Second reading by J1

1. Compared the delivered module with the repository version. The theorem signature and all existing declarations are unchanged byte for byte; only proof imports, private helpers, and the target proof changed. Verdict: pass.
2. Compiled the module with `lcompile.py`; it succeeds with no errors. Searched for forbidden constructs and remaining `sorry`; none occur in the delivered module. Verdict: pass.
3. Checked the DAG node against the Lean proof and dependencies. The node records the scalar theorem, internal-Hom definition, derived RHom algebra-module definition, and affine counit used by the proof. No new split-off statement was introduced. Verdict: pass.
4. Reviewed the route for shorter existing results and pruning. The proof reuses the scalar Koszul theorem and removes four redundant direct proof imports. The unit route is preserved; no realized unit step is bypassed. Verdict: pass.
5. Checked the public imports and theorem statement against the repository and confirmed the DAG proof text follows the implementation. Verdict: pass.

Changed only the assigned module proof/imports, its DAG proof metadata, and this report. No definitions, public signatures, or new holes were added.
