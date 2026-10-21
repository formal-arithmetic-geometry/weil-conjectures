## What changed

Completed `CategoryTheory.DerivedInternalHomSectionsModel.derived_internalHom_sections_model`
in `Sheaf.Algebra.Homology.DerivedInternalHomSectionsModel`. All four clauses now have
complete proofs: the natural representative comparison, the natural comparison for the
full derived sections complex, the global Hom complex and its component formula, and the
additive cohomology equivalence in every integer degree. The existing proof of
`tensorRightAdjoint_iso` and every existing statement and definition are preserved.

The proof constructs the canonical sections-to-derived-sections comparison from Mathlib's
right derived functor unit. To show it invertible on Hom(A,I), choose a K-flat replacement
P of A. Both the sheaf Hom map and its ordinary sections map are quasi-isomorphisms; the
latter is proved using homology of the external Hom complex and bijectivity of localization
on morphisms into shifted K-injectives. Naturality then reduces invertibility to Hom(P,I).
The final cohomology equivalence uses the same external Hom calculation.

Reused the independently landed theorem
`CochainComplex.isKInjective_homComplex_of_isKFlatOfUniverses` in
`Sheaf.Algebra.Homology.KInjectiveHomComplexOfUniverses`. It supplies exactly the
independent-universe form of Stacks Tag 0A96 needed here.

All proof-only imports remain private. Reused private proved comparison lemmas via
`import all`, without modifying their source modules. No existing public signature,
source-library module, definition, target, consumer or visibility is changed. Updated the
item's proof route to cite the existing independent-universe theorem. The local proof-command record is
`coord/changes/K5-derived-internal-hom-sections-local-proof-commands.md`. Preflight
conservatively requests it for the scoped open/omit and local irreducibility commands;
there is no public interface change or forced consumer adaptation.

## Proved and sorry left

Closed the sole original hole:
`CategoryTheory.DerivedInternalHomSectionsModel.derived_internalHom_sections_model`
(node `lem-sfb-derived-internal-hom-sections-model`).

The already proved `tensorRightAdjoint_iso` remains proved.

Holes closed: 1. Holes added: 0. Holes left in the delivered Lean module: 0.
No result is split off with `sorry`. Existing imported statements retain their own proof
status; this packet neither inserts holes into them nor claims to have proved them.

## No longer needed

Removed the item's direct proof import
`Sheaf.Algebra.Homology.KInjectiveHomComplex`, replacing its insufficient two-universe
interface with the existing proved generalization. The item's proof dependency
`lem-pur-hom-kflat-into-kinjective` is replaced by
`lem-coef-hom-kflat-into-kinjective-independent-coefficients`.

Removed the direct proof import
`WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap`, using
`Sheaf.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses` instead. The direct dependency
`lem-pur-rhom-well-defined` is replaced by `lem-pur-rhom-well-defined-universes`.

Removed the unused direct proof import
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom` and the item's direct
proof dependency `def-pur-sheaf-hom`: the imported Hom-complex and global-comparison APIs
already supply the needed data. The Hom-sheaf definition remains a dependency of the
recorded Hom complex. Removed only the two obsolete corresponding entries for the old
quasi-isomorphism and K-injectivity lemmas from `tool_uses`; no maintainer approvals added.

The item does not use `lem-sc-derived-hom-tensor-total` or the global-cochain detour of
the old K-injectivity node. These are not newly imported. No modules are withdrawn, and
no claim is made that an adopted source module or a dependency still used elsewhere is
globally pruned. The blueprint unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The planned mathematical argument is valid, but its original Hom-K-injectivity dependency
and its original Hom quasi-isomorphism import do not accept the independently varying
coefficient universe of this item. The already landed independent-universe
quasi-isomorphism theorem solves the latter mismatch. The independently landed
K-injectivity theorem solves the former without shrinking universes, changing the Hom definition, adding hypotheses,
or weakening any conclusion. Naturality of the sections comparison is established before
choosing the auxiliary K-flat resolution, so no functorial K-flat choice is assumed.

## Second reading by K5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
