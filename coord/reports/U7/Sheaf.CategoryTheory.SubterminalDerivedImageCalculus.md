## What changed

Filled `CategoryTheory.SubterminalImageCalculus.subterminal_derived_image_calculus` without
changing its statement, its public records, or the four independent derived-category universes.
All new helpers are private and proved. No source-library file changes.

The five pairs use the existing exact derived restriction and right derived direct image,
with the chain-transpose normalization proved from the derived unit factorization. Existing
site restriction/relocalization theorems supply K-injective preservation. Exact localization
compositors give both normalization equations. The ordinary cross-restriction theorem is
applied degreewise, then transferred to arbitrary derived objects through K-injective
resolutions. The comparison records and all six overlap identities follow by adjunction
naturality, triangle identities, and conjugate adjoint isomorphisms.

The proof uses local sheafification instances and generic component lemmas to keep
instance search and adjunction matching in the stated universes.
These local settings do not change exported definitions, instances, or public signatures.

Updated the item's DAG proof, proof dependencies, and proof origin to this route. Removed
only obsolete entries from its approved tool-use list. The sole definition repair removes
an identity compositor from `restrictionComp`; its
mathematical map is unchanged. See `coord/changes/U7-subterminal-restriction-compositor.md`.
The current downstream importer is
`Sheaf.Paper.TransverseTameOpenShriekExchange`; it does not use `restrictionComp` or
any declaration in this namespace, and needs no adaptation. The theorem has the same binders and conclusion;
explicit universe annotations select
the intended existing instances without changing its elaborated statement.

Repair of return C-190f6 (returned head `190f6fbecdc`): compared the retained Lean
proof and DAG route with current `sheaf-dag`. The current item still has its original
single hole; the retained packet supplies its complete proof. Its public imports,
public declaration signatures (modulo explicit universe annotations), and unit route
remain unchanged. No rework or quarantine row applies to this item.

The landing failure concerns the reviewer's fix path, not the Lean proof. The record
is included as `coord/changes/U7-subterminal-restriction-compositor.md`. Any reviewer
fix must name that full repository path, including `coord/changes/`; the bare basename
is not a file of the delivery. The record remains open until the maintainer verifies
the global build. This packet needs no basename-only reviewer fix.

Validation: the public signature/import, zero-hole, line-width, and permitted-node-field
checks pass. The fresh server compile passed in 36.4 seconds with no warnings.
`deliver3.py` fetches current `sheaf-dag`, commits the packet on that base, runs its
axiom probe and preflight, and pushes the resulting delivery branch.

## Proved and sorry left

Closed the single original hole in
`CategoryTheory.SubterminalImageCalculus.subterminal_derived_image_calculus`
(`lem-sp-subterminal-derived-image-calculus`). No holes added, no statements split off,
and no `sorry` remains in the delivered module.

## No longer needed

Removed these proof imports:

- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`: use the existing independent-ring
  restriction and relocalization preservation interfaces and their exactness interfaces.
- `Sheaf.CategoryTheory.Sites.SliceSubtoposSitePresentation`: the ordinary module
  restriction/direct-image adjunctions already exist in Mathlib.
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`: the source library already constructs the
  required right derived functor and normalized adjunction.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`,
  `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`, and
  `Mathlib.Algebra.Homology.DerivedCategory.KInjective` as direct imports: the used declarations
  are available through the more specific proof imports.

The item's proof no longer directly needs nodes
`lem-pur-site-restriction-module-adjunction-exact`,
`lem-trf-slice-subtopos-site-presentation`,
`lem-weil-pbc-kinjective-total-derived`, or `lem-weil-pbc-kinjective-hom-derived`.
These are removals from this item's route, not withdrawals of their modules or declarations.
No Lean module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The redundant identity complex compositor in
`restrictionComp` caused expensive definitional-equality searches; the equivalent termwise
restriction comparison avoids this, with the change documented for independent review. The planned constructions duplicate existing
ordinary slice adjunctions and the source library's derived-adjunction construction.
The W-to-U and W-to-V comparisons and the six overlap identities admit formal adjunction
proofs; separate product computations for those fields are unnecessary. The genuinely
geometric cross calculation is supplied by the existing ordinary overlap theorem.

## Second reading by U7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
