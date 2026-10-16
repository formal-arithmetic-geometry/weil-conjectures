## What changed

Proved `AlgebraicGeometry.Etale.affine_globalSections_limit_isColimit_of_directed`
without changing its signature. Replaced the direct construction of a limit-site sheaf by
Gabriel-Popescu localization, using Mathlib's fully faithful module embedding and exact left
adjoint. A private proof first obtains abelian-group continuity from the existing
`globalSections_limit_comparison`; a second obtains module continuity by the exact forgetful
functor and reflection of colimits. The general proof constructs a module-valued sheaf using
the right adjoint, applies module continuity, preserves the colimit by the left adjoint, and
transports along explicit diagram and cocone isomorphisms.

Added `ExactFunctorAffineEtaleSheafification`: a finite-limit-preserving coefficient functor
preserves finite affine matching conditions, so the sheafification unit is an isomorphism on
affine objects. Added `ExactFunctorAffinePullbackSections`: constructs the coefficient-change
and inverse-image comparisons and proves their compatibility with the exact canonical
section maps in the item. Its unit compatibility uses the adjunction unit equation; its
composition compatibility is proved by mates. Supporting section-map identity, composition,
and naturality lemmas are proved in that module.

Updated the item's proof description and DAG route. The new modules contain complete proofs,
not postponed obligations. No existing definition or statement changed, and no consumer
adaptation is needed. Public imports occur only where public constructions or signatures need
the imported declarations. All three files compile together without warnings using lcompile;
the main signature was also compared verbatim with the original.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Etale.affine_globalSections_limit_isColimit_of_directed`.

The item and both new comparison theorems were audited with `#print axioms`; each uses
only `propext`, `Classical.choice`, and `Quot.sound`. The two principal constructed
isomorphisms were audited with the same result.

Added 0 holes. No `sorry` remains in any of the three delivered modules. In particular,
`AlgebraicGeometry.Scheme.exactFunctor_affine_toSheafify_isIso` and
`AlgebraicGeometry.Etale.coefficientPullbackSectionsIso_comp` are proved, together with all
supporting definitions and lemmas. This is a proof, not a decomposition into new holes.

## No longer needed

Removed the proof import `Sheaf.Paper.EtaleFiniteDataDescent` from the item. Its node
`lem-weil-pbc-etale-finite-data-descent` is no longer a direct proof dependency of this item.
The old route's varying model categories, colimits over models, construction of a sheaf on
the limit site, and direct universal-property comparison are unnecessary here. Finite-data
descent may remain needed by other proofs, including the scalar continuity infrastructure;
this delivery makes no global withdrawal claim about that shared module.

All remaining imports are used: in particular `WeilConjectures.CategoryTheory.Pro.Generating`
provides the finite-hypercover classes and the precoverage sheaf-condition criterion, while
`FullAffineEtaleTopos` provides the proved dense affine inclusion. No blueprint unit realization
is bypassed: this item's unit `sk-prop-h2` has no realized step or statement at this node.

## Where the brief, the DAG or earlier work was wrong

No statement was found false. The DAG's direct construction is a possible plan, but is longer
than needed once Mathlib's Gabriel-Popescu theorem and the library's scalar continuity theorem
are used. The proof and proof dependencies now describe the actual localization route.
The coefficient comparisons are proved here rather than split off again.

## New nodes

`lem-weil-pbc-exact-coefficient-affine-sheafification` records the finite affine matching
argument and dense-subsite sheafification comparison, in
`Sheaf.AlgebraicGeometry.ExactFunctorAffineEtaleSheafification`. It is fully proved. Empty
covers are included by the finite-multifork criterion, and no affineness of the base S is
assumed: pairwise intersections are taken over each affine covering target.

`lem-weil-pbc-exact-coefficient-affine-section-naturality` records the constructed coefficient
isomorphisms and their compatibility with inverse-image section maps, in
`Sheaf.AlgebraicGeometry.ExactFunctorAffinePullbackSections`. It is fully proved. Only X and Y
are required affine; the fixed base S is arbitrary. All coefficient data come from specified
adjunctions, finite matching limits and isomorphisms, with no arbitrary existential witness.

For both nodes real leansearch, loogle/leanfinder and grep searches were run and recorded.
They found finite-limit/sheaf and adjunction ingredients, but no theorem with the full affine
coefficient comparison. No change record is required because all existing signatures and
public imports are unchanged.

## Second reading by A4

1. **Signatures and accidental changes — pass.** Compared the delivered item with the
   repository version. The existing theorem signature and all existing declaration
   signatures are byte-for-byte unchanged; the report declares the two added comparison
   nodes and no definition or statement change.
2. **Proof and axioms — pass.** Compiled the item and its two added modules with
   `lcompile.py`; no errors or warnings occurred. Searched the delivered Lean files for
   `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, and `implemented_by`; none occur.
   The audited declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
3. **Split-off statements — pass.** The two new node statements are strictly smaller
   coefficient-change lemmas, are needed by the item proof, have source and proof prose,
   and are not duplicate library declarations. Their node records and Lean declarations
   agree.
4. **Route and pruning — pass.** The proof follows the scalar continuity theorem, exact
   module reduction, and Gabriel–Popescu localization. The removed finite-data-descent
   import is unused; remaining imports are used. The unit route is retained.
5. **DAG agreement — pass.** The item's `proof`, `proof_deps`, and `proof_origin` and the
   two new node records match the proof and imports as written.

I changed only this report section during second reading; no Lean proof or statement
needed repair.
