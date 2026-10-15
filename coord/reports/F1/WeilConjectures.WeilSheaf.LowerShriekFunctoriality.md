## What changed

Changed `lean/WeilConjectures/WeilSheaf/LowerShriekFunctoriality.lean` and the proof records of
`prop-functor-package` and `prop-sf-open-closed-triangle-all-stages`. Four original holes are
closed. Every existing public signature and definition is preserved. The base-change
declaration moves earlier so its open and empty pullback cases can be used by the other
proofs. Its docstring now records the independent proof still required. Added proof-only
imports of `WeilSheaf.Localization`, `WeilSheaf.OpenImmersionRestriction`,
`WeilSheaf.LowerStarId`, and `WeilSheaf.UpperStarComp`.

The support comparison is proved: the fibre and cone of the open restriction unit are
closed-supported. Closed-support essential image and adjunction give orthogonality, so the
restriction map on Hom from an open-supported complex is bijective. Its uniqueness gives
naturality, and the two restrictions detect invertibility. Exact extension by zero has zero
closed restriction and identity open restriction by the existing adic APIs. These facts
also prove its adjunction with restriction, independently of compact-support base change;
composition of exact extensions follows by uniqueness of left adjoints.

For composition, proper base change supplies the proper/open exchange by comparing the
open and closed restrictions. Its identity-source case gives invariance under cartesian
proper refinement; the common refinement gives independence of compactification. Choose a
compatible triangle of compactifications, exchange the middle proper/open pair, compose
the extensions by zero and proper direct images, and compare with the chosen functors.
Comparing with the compactification `U → X → X` identifies Rj! with exact extension by zero.
For the open–closed triangle take the fibre of the actual closed unit and identify its first
vertex by support comparison. Finally apply triangulated Rf! and use composition and the
proved proper comparison to identify the image triangle's vertices. The only applications
of the remaining base-change theorem in these proofs concern proper morphisms.

Empty opens, empty complements and zero complexes are covered by the same arguments,
without a separate empty-scheme argument. All added
helpers are private and proved. The private extension functor is a real construction from
the existing exact extension by zero, with proved boundedness and constructibility. Its
irreducibility keeps routine comparisons from unfolding the full subcategory construction.

## Proved and sorry left

Closed four of the five original holes (namespace `AlgebraicGeometry.WeilComplex`):

- `nonempty_derivedLowerShriek_toComplex_iso_of_isOpenImmersion`.
- `exists_distTriang_openClosed`.
- `nonempty_derivedLowerShriek_comp_iso`.
- `exists_distTriang_derivedLowerShriek_openClosed`.

The only remaining `sorry` is the original
`AlgebraicGeometry.WeilComplex.nonempty_upperStar_derivedLowerShriek_iso`
(`prop-functor-package`, base-change clause; `thm-cbc-qbar`). Its statement is unchanged.
It still needs the actual bounded constructible adic proper exchange, its compatibility
with Frobenius, exact extension-by-zero base change, and independent refinement comparisons.
The comparisons in this delivery depend on that theorem and cannot close it circularly.

No holes added and no split-offs. This closes four original holes from existing named
obligations; it does not claim that compact-support composition is now sorry-free in its
transitive dependencies. The assigned file compiles with the required single-file compiler
without warnings other than the original remaining sorry.

## No longer needed

No original imports removed and no modules withdrawn. No additional holed `Sheaf.*`
statement module is needed: the source-library localization API and compactification
geometry suffice to reduce the four claims to the existing base-change obligation.
`Compactification.CommonRefinement` and `Compactification.Triangle` were tested as direct
proof imports and removed: the required compactification API is already transitively available.
The second reader removed the redundant `Compactification.Triangle` import after compiling
a copy without it; deleting any of the other four added proof imports fails to compile. The earlier self-pullback and empty-pullback
arguments for Rj! were removed in favor of the common-refinement comparison. Consequently
no separate empty-scheme homology lemma or identity-pullback comparison remains in the proof.

In particular `Sheaf.AlgebraicGeometry.OpenClosedRecollement` is not imported for these
Weil-complex proofs. The finite/integral/rational coefficient transport route of
`prop-sf-open-closed-triangle-all-stages` is not needed for its attached weakened Weil claim.
The generic étale compact-support composition theorem is not applied to the different Weil
categories. These nodes are not globally pruned: their full coefficient-stage units retain
their stated proof routes, and coefficient transport remains relevant to base change.

## Where the brief, the DAG or earlier work was wrong

The stated `lem-cbc-open-closed-recollement` declaration concerns finite étale coefficients,
not the source-library Weil-complex categories, so it cannot be applied directly here.
The proved `WeilSheaf.Localization` API provides the support argument. Likewise the generic
étale compact-support composition declaration does not directly prove Weil composition;
the compactification geometry and the actual Weil functors must be compared. Several broad
package dependencies use different coefficient models, and compactification coherence has
no direct attached declaration for these Weil functors.

The source already documents that `exists_distTriang_openClosed` asserts only vertex
isomorphisms, not the canonical counit, unit and functoriality of the full blueprint statement.
This delivery preserves that signature; its chosen triangle uses the actual closed unit.
The proof-record updates distinguish the attached source-library claims from the stronger
coefficient-stage statements and preserve all of the latter's original proof steps.

An existing duplicate of the base-change statement is
`WeilComplex.nonempty_iso_derivedLowerShriek_upperStar` in `WeilSheaf.LowerShriekOperations`;
it is itself sorry and was not imported to relabel the remaining obligation. The condensed
proper base-change theorem uses a different module-object coefficient model and assumes
separated structure morphisms for all schemes. The present signatures allow quasi-separated
nonseparated schemes, so applying that theorem would additionally require coefficient-model
comparisons and locality; no separatedness hypothesis was added here.


## Second reading by F1

1. **Interfaces: PASS.** Compared the delivered module with the repository using both the
   textual diff and `stage3_delivery.diff_module`. All six existing declaration signatures
   are byte-for-byte unchanged; no existing definition body, visibility, public import or
   statement changed. Only the four reported theorem bodies changed. The remaining
   base-change theorem was moved, with its signature preserved. No change record is needed.
2. **Proof and construction: PASS.** Read the whole module, including the support-Hom
   argument, derived extension construction, refinement comparisons and composition chain.
   Compiled the delivered file successfully (8.2 seconds before import cleanup). A scratch
   copy with `#print axioms` for every declaration compiled successfully (9.5 seconds).
   All axioms are among `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` from open
   obligations; no forbidden declaration or option appears. The four generic support
   helpers, `extensionComplex`, its disjoint-support property and its restriction comparison
   use only the three allowed axioms. Other helpers can also depend on existing imported
   obligations, so closing four local holes does not certify the transitive closure.
   The only local hole is the unchanged base-change theorem. Its expanded docstring gives
   the independent coefficient, Frobenius, pullback and refinement proof required to avoid
   a circular proof. Extension by zero is constructed by lifting the actual exact functor;
   no arbitrary data are chosen from an unproved existence theorem.
3. **Split statements and edge cases: PASS.** No split-offs, new public declarations, new
   nodes or new holes. The private support helpers quantify over all objects without a
   nonzero or nonempty hypothesis; zero complexes, the empty open and the empty complement
   satisfy the same restriction, orthogonality and triangle arguments. The compactification
   comparisons require the cartesian refinement property explicitly and use the established
   common refinement; no density or nonemptiness is assumed. Every call of the remaining
   base-change theorem has a proper right vertical morphism (the original proper map or its
   closed pullback).
4. **Route and pruning: PASS after import cleanup.** Searched the source and Sheaf libraries
   for extension adjunction/composition and the Mathlib triangulated API for orthogonal Hom
   comparisons. Loogle confirmed
   `ObjectProperty.leftOrthogonal.map_bijective_of_isTriangulated`; it needs an additional
   triangulated localization structure and does not shorten this argument from the available
   adjunction and support data. The generic étale composition and recollement declarations
   have different coefficient categories; replacing the proof with them would require
   unproved transport. Removed the redundant proof-only import
   `WeilConjectures.Compactification.Triangle`: the whole file compiles without it. Tested
   deletion of each of the other four added imports; each produces a missing declaration or
   instance error. No original import or old proof-dependency edge is removed. The original
   coefficient-stage proof steps are preserved verbatim, and neither unit record is edited;
   both have pre-existing empty `realized` entries. The attached Weil vertex-isomorphism
   statement is explicitly distinguished from the stronger canonical coefficient-stage
   triangle, whose proof route is retained. No module is claimed globally pruned.
5. **DAG: PASS.** Both delivered node files change only `proof`, `proof_deps` and
   `proof_origin`. Their old steps remain verbatim, their added paragraphs describe the actual
   Weil support/refinement/composition arguments, and each `proof_deps` is exactly the union
   of its steps' `uses`. Statements, sources, unit assignments and Lean attachment records
   are untouched. There are no new node records to validate.

Second-reading changes: removed one redundant proof import and corrected its description in
this report; no proof or statement needed repair. The delivery closes the four named local
holes listed above and adds zero holes; the base-change obligation remains open.
