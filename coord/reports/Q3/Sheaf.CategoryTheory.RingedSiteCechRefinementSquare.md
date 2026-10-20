## What changed

Repaired the returned delivery against the current item source after the batch rollback.
The sandbox module was rebuilt from the repository version, preserving the current ringed
statements and their existing proof bodies. Reapplied only the completed abelian proof and
its private import of the fully proved new module
`Sheaf.CategoryTheory.RingedSiteCechRefinementSquareAbelianExists`.
The stale imports and applications of the absent witness and edge-uniqueness modules are gone.

Proved `CategoryTheory.ringedSite_cech_refinement_square_abelian` with its exact existing
statement. The new existence theorem constructs strict lifts into pushed-forward injective
resolutions, compares arbitrary resolutions by augmentation homotopies, and treats arbitrary
injective replacements by homotopy equivalences. Exact inverse image makes direct image
preserve injectives. The parent proves uniqueness by choosing one roof and cancelling its
invertible target comparison and replacement homology map.

Both modules compile through lcompile (0.3 and 18.1 seconds). A separate compilation with
`#print axioms` confirmed that both the abelian theorem and the new existence theorem use
exactly `propext`, `Classical.choice`, and `Quot.sound`. No existing public signature,
attribute, public import, or definition changes. No consumer adaptation is needed.

## Proved and sorry left

Closed one of the current item's two holes:
`CategoryTheory.ringedSite_cech_refinement_square_abelian`.
Proved the new theorem `CategoryTheory.ringedSite_cech_refinement_square_abelian_exists`.

One existing hole remains: `CategoryTheory.ringedSite_cech_refinement_square_rest`
(node `lem-weil-pbc-ringed-site-cech-refinement-square-rest`). Its current statement is
marked disputed for the missing hypothesis described below. The main ringed theorem
continues to depend on that existing hole. Zero holes are added and zero are split off.
This packet is one proof, not a decomposition or a claim that the ringed result is proved.

## No longer needed

Removed these direct proof imports from the item:

- `Mathlib.Algebra.Homology.ModelCategory.Injective`
- `Sheaf.Algebra.Homology.BoundedBelowInjectiveResolutionMono`
- `Sheaf.CategoryTheory.Sites.InjectiveModuleCechAcyclic`
- `WeilConjectures.Algebra.Homology.FirstQuadrantAugmentation`
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic`
- `WeilConjectures.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy`
- `Sheaf.CategoryTheory.SitePullbackAbelianExact`
- `Sheaf.CategoryTheory.DoubleComplexTotal`
- `Sheaf.CategoryTheory.SiteCoveringAxioms`
- `Sheaf.CategoryTheory.Sites.DirectImageInjectiveEvaluationAcyclic`
- `WeilConjectures.CategoryTheory.SiteCechComplex`

The new proved helper imports the exactness theorem it uses. The earlier ringed construction
is still pending; its lower dependencies remain in the DAG. No module or node is withdrawn,
no global pruning is claimed, and the proper-base-change unit route is retained.
The abelian argument needs no integer-ring module-category equivalence, Cech augmentation,
or nontrivial monomorphic injective replacement: the identity replacement proves existence.
The parent DAG keeps its pending ringed construction and records the direct abelian proof.

## Where the brief, the DAG or earlier work was wrong

The returned packet assumed that the ringed witness and edge-uniqueness modules were still
present. The batch rollback removed them and restored the ringed-rest hole. This repair
starts from that restored file instead of retaining those obsolete imports and proofs.
The previous report's zero-hole count is therefore corrected to one existing hole left.

STATEMENT-DISPUTED: `ringedSite_cech_refinement_square_rest` accepts an arbitrary cochain map
`γ`, without the tuple formula connecting it to `h`. On the one-object category with the
identity topology, identity site functor, integer ring and coefficient module, and singleton
identity cover, take `h = 𝟙` and `γ = 0`. In degree zero, the normalized edges and the
normalized direct-image roof are identities. The last equality would assert `𝟙 = 0` on ℤ.
The declaration is marked accordingly; its statement and existing sorry are unchanged.
This defect is in the auxiliary theorem: the main ringed theorem does constrain γ by the
tuple formula. The proved abelian theorem is independent of both ringed declarations.

The original abelian plan uses the integer-ring module specialization. Exact abelian
inverse image gives a direct proof in the stated abelian categories. Terminality is not
needed by the stronger resolution calculation; both terminality hypotheses remain intact.
The new proof works in degree zero, with zero coefficients, and with identity site functors;
it uses no positive-degree restriction, covering index, or nonzero coefficient assumption.

## New nodes

`lem-weil-pbc-ringed-site-cech-refinement-square-abelian-exists`, implemented by
`Sheaf.CategoryTheory.RingedSiteCechRefinementSquareAbelianExists`, records the fully proved
existence and arbitrary-resolution normalization of the abelian roof, including strict-unit
lifts and the adjoint-coefficient formula. The parent supplies uniqueness. Its retained
search records and proof have been checked against the sandbox source.
No statement or definition was changed, so no change record is required.

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
