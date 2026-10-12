## What changed

Proved `CategoryTheory.siteLeray_degenerate` with its original signature and universe
parameters unchanged. Two proved private helpers construct the pushed-forward injective
resolution and transfer finite-limit preservation from set to abelian inverse image.
The proof compares the two derived-section computations of the same section complex.
It transfers the result to the arbitrary Ext universe in the original signature via
`InjectiveResolution.extAddEquivCohomologyClass` for the same resolutions.

Added proof imports `Sheaf.CategoryTheory.SitePullbackAbelianUnderlying`,
`Sheaf.CategoryTheory.Sites.CohomologyRightDerivedSections`, and
`Mathlib.CategoryTheory.Abelian.Injective.Ext`. Replaced the broad public pullback-cohomology
import with the Mathlib imports required by the existing statement. Updated the existing
DAG node's proof route and dependencies. No other module or statement was changed. The public-import change is recorded in
`coord/changes/site-leray-degenerate-imports.md`; the sole direct importer
`Sheaf.AlgebraicGeometry.EtaleZariskiQcohComparison` (held by ORCHESTRA) compiled
unchanged against the delivered module, so no forced adaptation is needed.

Single-file compilation passes without warnings. `#print axioms` has the standard axioms
and transitive `sorryAx` from the existing `sitePullback_abelian_underlying` dependency;
the derived-section comparison has only the three standard axioms. No new hole is added.

## Proved and sorry left

Closed the one original hole: `CategoryTheory.siteLeray_degenerate`
(node `lem-weil-pbc-site-leray-degenerate`). No `sorry` remains in the delivered module.
No holes added and none split off. The two private helpers are fully proved. Existing
holes below the underlying-set comparison remain other workers' items.

## No longer needed

Removed imports:

- `Sheaf.CategoryTheory.SiteCohomologyPullback` (public; replaced by statement-level Mathlib).
- `Sheaf.CategoryTheory.SitePullbackAbelianExact` (proof-only).
- `Sheaf.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy` (proof-only).

The proof no longer needs `lem-weil-pbc-site-cohomology-pullback`,
`lem-weil-pbc-site-pullback-abelian-exact`,
`lem-weil-pbc-lift-to-injective-unique-up-to-homotopy`, or
`lem-weil-pbc-injective-resolution-lift-exists`: neither pullback cohomology maps nor lifts
between auxiliary resolutions are constructed. The degree-zero argument is directly
kernel preservation, so the separate node
`lem-weil-pbc-left-exact-injective-resolution-degree-zero` is unnecessary.
The separate proof dependency `lem-weil-pbc-sheafification-exact` is also unnecessary;
sectionwise limits and reflection are provided by Mathlib. These are local pruning
claims, not claims that no other target imports these modules. The unit record
`sk-thm-p1` realizes none of these removed auxiliary nodes as its own statement or steps.

## Where the brief, the DAG or earlier work was wrong

The natural-language node specifies the pullback-counit edge map and its degree-zero
identity. The unchanged Lean theorem states only existence of an objectwise family
of isomorphisms. Accordingly the delivered proof establishes precisely the existing
Lean statement and does not establish the additional edge-map clauses. This mismatch
already existed at stage 2; no signature or node statement has been weakened here.
The independent reader/maintainer should account for this in the statement-fidelity
review. The resolution argument itself requires no spectral sequence.

The existing `sitePullback_abelian_exact` theorem requires explicit `hcover` and
`hpullback` arguments absent from this module's signature. Its needed finite-limit
clause instead follows from `sitePullback_abelian_underlying` using the supplied
set-valued finite-limit hypothesis, as the private helper proves.

## Second reading by V1

1. Compared the delivered module with the repository version. The theorem signature is byte-for-byte unchanged; only the proof, proof imports, and corresponding DAG route were changed. The import change is documented in `coord/changes/site-leray-degenerate-imports.md`.

2. Compiled `lean/Sheaf/CategoryTheory/SiteLerayDegenerate.lean` successfully with `lcompile.py`. The module has no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`; the target's only nonstandard transitive axiom is the pre-existing `sorryAx` in `sitePullback_abelian_underlying`.

3. Checked the private resolution and finite-limit helpers and the existential target construction. No new public statement or split-off hole was added; the target statement remains exactly the existing Lean statement. The underlying helper is an existing dependency rather than a duplicated theorem.

4. Reviewed the proof route against Mathlib and imported declarations. The pushed-forward resolution is constructed directly, and section cohomology is compared through the existing right-derived-sections isomorphisms. The imports removed in the report are unused by this proof. The unit record `sk-thm-p1` remains respected; the DAG proof and dependencies match the code.

5. Checked the DAG node, proof dependencies, proof origin, and the documented statement-fidelity caveat. They agree with the delivered Lean proof; no natural-language edge-map claim was silently added to the weaker existential Lean theorem.

Changed after reading: added this review record only; no proof or statement changes were necessary.
