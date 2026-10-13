## What changed

Completed the proof of `AlgebraicGeometry.local_finite_free_homology_natural` in
`Sheaf.AlgebraicGeometry.LocalFiniteFreeHomologyNatural`, with its signature unchanged.
The proof specializes the existing functorial derived-Hom comparison, transports its
homology through exact open restriction, precomposes with the augmentation into restricted
K-injective coefficient resolutions, and inverts the coefficient-resolution comparison.
All three comparisons are natural transformations of the whole coefficient category.
No derived category on the open in the supplied ambient universe is introduced.

Added proof-only imports of `Sheaf.AlgebraicGeometry.HomComplexRestrictSchemeNatural`,
`Sheaf.Algebra.Homology.StrictlyPerfectHomQuasiIso`,
`Sheaf.Algebra.Homology.KInjectiveRestrictOpen`,
`Sheaf.Algebra.Homology.QuasiIsoHomComplexMap`, and
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`.
All original public imports and all existing public signatures remain unchanged.
Local irreducibility annotations prevent the elaborator from expanding homology and
termwise complex functors while checking functor reassociations. The larger heartbeat
budget applies only to this theorem, within the unchanged single-file time limit.

Updated the original node's proof, proof dependencies, and proof provenance to match
this construction. Added the two ordinary-complex lemmas below, with source and complete
proofs in words. Their edge cases include zero complexes, rank-zero free terms, empty
opens/spaces, bounds with an empty support interval, and unbounded coefficient complexes.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.local_finite_free_homology_natural`
(node `lem-sc-local-finite-free-homology-natural`). There are no sorries in the item's
module. Its complete Lean proof depends on two newly stated smaller theorems:

- `AlgebraicGeometry.homComplex_restrict_scheme_natural`, node
  `lem-sc-hom-complex-restrict-scheme-natural`, in
  `Sheaf.AlgebraicGeometry.HomComplexRestrictSchemeNatural`: `:= by sorry`.
  This concerns only the ordinary complex functor and its restriction, with no derived
  category, finite-free resolution, coefficient single complex, or homology degree.
- `AlgebraicGeometry.quasiIso_homComplex_map_of_bounded_finiteFree`, node
  `lem-sc-strictly-perfect-hom-quasi-iso`, in
  `Sheaf.Algebra.Homology.StrictlyPerfectHomQuasiIso`: `:= by sorry`.
  This concerns only preservation of a quasi-isomorphism by ordinary internal Hom.
  It has no open immersion, augmentation, derived category, or natural-isomorphism goal.

Hole counts: one closed, two added. This is a decomposition, not an independent proof
or a reduction in the total hole count. The natural-transformation assembly,
augmentation comparison, K-injective transport, and homology inversions are proved.

## No longer needed

Removed the following proof imports and their direct planned dependency edges:

- `Sheaf.Paper.DerivedInternalHomRestrictOpen`, node
  `lem-sc-derived-internal-hom-restrict-open`. The proof uses the ambient functorial
  comparison and ordinary natural restriction instead; it does not localize on the open.
- `Sheaf.Algebra.Homology.DerivedHomFiniteFreeModel`, node
  `lem-sc-derived-hom-finite-free-model`. The proof directly applies Hom to the
  coefficient-resolution transformation and proves its homology maps invertible.

Their respective dependency closures are unnecessary through this item; other users
may still need them. No unit statement or unit proof step is bypassed: the parent unit's
`realized` lists do not designate this node as a replacement for any unit step.

## Where the brief, the DAG or earlier work was wrong

The originally cited derived-restriction and finite-free-model declarations are only
objectwise `Nonempty` isomorphisms. Their signatures do not supply the coefficient
naturality needed by this item, despite naturality being mentioned in their prose.
Choosing their components arbitrarily would not prove a naturality square. The new
restriction theorem explicitly supplies the missing ordinary functor-level comparison.

The existing bounded-above finite-free acyclic-Hom lemma assumes a bounded-below
coefficient complex. A general functorial K-injective resolution has no such supplied
bound. The new quasi-isomorphism preservation lemma uses BOTH bounds of E and requires
no coefficient bound, by the finite-column filtration. No existing statement is changed.

Read the canonical Stacks pages for Tags 08DL (Lemma 20.42.3) and 08DM
(Lemma 20.46.9); the local clone does not contain cohomology.tex.

## New nodes

`lem-sc-hom-complex-restrict-scheme-natural` is the ordinary internal-Hom restriction
comparison natural in every coefficient complex. Its module is
`lean/Sheaf/AlgebraicGeometry/HomComplexRestrictSchemeNatural.lean`. Source:
https://stacks.math.columbia.edu/tag/08DL, the ordinary Hom part of the construction.

`lem-sc-strictly-perfect-hom-quasi-iso` is preservation of arbitrary quasi-isomorphisms
by Hom from a bounded finite free complex. Its module is
`lean/Sheaf/Algebra/Homology/StrictlyPerfectHomQuasiIso.lean`. Source:
https://stacks.math.columbia.edu/tag/08DM, via the cone and finite-column filtration.

No existing signature or exported elaboration attribute was changed, and no other
module was adapted. The static checker nevertheless classifies the explicit local
attribute commands as an interface change. Their scope and users are recorded in
`coord/changes/local-finite-free-homology-natural-elaboration.md`.

The first dry run required LeanSearch records in addition to the successful
LeanFinder/Loogle and source-grep searches. Both LeanSearch queries returned
Internal Server Error; these unavailable searches are recorded without asserting
any match or no-match result.

## Second reading by T2

1. Compared the existing module with the repository version by diff. Its complete
   theorem signature is byte-for-byte identical; no definition or target changed.
   All new imports in the item are proof-only. The local attributes do not export
   a changed elaboration environment; their explicit change record is present.
2. Compiled both new modules and the item with lcompile.py. A scratch copy of the
   complete item, with three `#print axioms` commands appended, compiled cleanly:
   each declaration uses only propext, Classical.choice, Quot.sound and sorryAx.
   The only textual holes are the two named, documented split theorems. There are
   no definitions or forbidden axiom/unsafe/opaque/extern commands in the delivery.
3. Read both split signatures and their docstring arguments against Stacks Tags
   [08DL](https://stacks.math.columbia.edu/tag/08DL) and
   [08DM](https://stacks.math.columbia.edu/tag/08DM). Verdict: true, strictly smaller
   than the item, and sufficient. Restriction retains the local maps and preserves
   arbitrary products; projectionwise compatibility gives coefficient naturality.
   For bounded finite free E, a finite filtration of Hom(E,cone(s)) has exact
   finite-free Hom columns; cone compatibility gives the quasi-isomorphism.
   Zero E, rank-zero terms, empty U, and an empty bound interval give zero complexes;
   unbounded coefficient complexes cause no infinite-column convergence issue.
   Repeated LeanFinder search using exact internal Hom/acyclic/perfect wording,
   Loogle overHomObjIso search, and source searches in Mathlib, upstream and Sheaf
   found no exact replacement. Existing objectwise Nonempty comparisons do not
   supply naturality, and the existing acyclic-Hom theorem requires a target bound.
   Neither split can be closed by the available component APIs in a few minutes.
4. Read the proof from its derived comparison downward through the natural
   restriction, augmentation and coefficient-resolution transformations. Their
   homology inversions prove precisely the original natural-isomorphism goal.
   The two removed proof imports and their node edges are fully listed above.
   The old def-pur-hom-complex edge is retained explicitly: its functor is used,
   and its module remains a public import through DerivedInternalHom. The parent
   unit's realized statement and step lists are empty, and no designated unit
   step or chapter route is replaced. Verdict: valid decomposition, one hole
   closed and two added, not a net proof gain.
5. Checked all three node statements against Lean, source/proof/search/creation
   fields of the new nodes, and the uses/proof_deps union. The original node now
   names the actual comparison route and dependencies. Verdict: consistent.

Second reading changed: removed the unused local CY binding; restored the explicit
original def-pur-hom-complex proof dependency and its corresponding step use; added
this independent review. No signatures, definitions, or existing docstrings changed.
