## What changed

Repaired the returned delivery by removing the private declaration
`AlgebraicGeometry.Scheme.AffineProEt.geometric_adjunction`. Its statement duplicated
word for word the existing `exists_closedSiteAdjunction` statement in
`Sheaf.AlgebraicGeometry.ProEtale.ClosedSiteAdjunction`. The same Hom-equivalence and
invertible-unit construction is now a local proof term inside
`affine_closed_site_functor_properties`, so the target theorem and all public signatures
remain unchanged. Importing `ClosedSiteAdjunction` here would create a cycle because that
module imports this one, so the construction cannot be replaced by a module import.

The repaired module compiles without warnings. The prior import pruning and proof remain
unchanged; the change record records those earlier import changes.

## Proved and sorry left

Closed 1 existing hole:
`AlgebraicGeometry.Scheme.AffineProEt.affine_closed_site_functor_properties` (node
`lem-weil-pbc-affine-closed-site-functor-properties`). Added 0 holes and 0 split-off
statements. No `sorry` remains in the delivered module. The second reader independently checked
`#print axioms` for this theorem and `closedSiteLiftInclusion`: both use only
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.

## No longer needed

The duplicate private helper `geometric_adjunction` is no longer a declaration. No
additional imports or DAG nodes were removed in this repair. The earlier pruning removed
these direct imports:

- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`
- `Sheaf.CategoryTheory.SpecialCocontinuousCoverings`
- `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`
- `Sheaf.RingTheory.ProEtale.ClosedLiftMap`
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`
- `Mathlib.AlgebraicGeometry.Scheme`
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`
- `Sheaf.RingTheory.IndPrincipalZariski`
- `WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine`
- `WeilConjectures.RingTheory.ProEtale.ClosedLift`
- `Mathlib.CategoryTheory.Sites.Precoverage`
- `Mathlib.RingTheory.Ideal.GoingDown`
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`
- `Sheaf.RingTheory.IndEtaleStability`
- `Mathlib.RingTheory.Ideal.Maximal`
- `Sheaf.CategoryTheory.SiteCoveringAxioms`
- `WeilConjectures.CategoryTheory.SpecialCocontinuousCoverings`

The earlier pruning also removed the direct DAG dependencies
`def-weil-pbc-fpqc-covering`, `def-weil-pbc-ind-etale-algebra`,
`def-weil-pbc-sites-and-cohomology`, `def-weil-pbc-special-cocontinuous-functor`,
`lem-exc-closed-lift-filtered`, `lem-galois-fpqc-covering-base-change`,
`lem-weil-pbc-flat-ring-map-iff-flat-affine`, and
`lem-weil-pbc-ind-etale-stability`.

The second reading additionally removed `def-weil-pbc-proetale-site` from
`proof_deps` and the proof steps: its recorded Lean declaration is
`proEtaleDerivedCategory`, which is unused here. The affine precoverage and topology
actually used belong to `def-weil-pbc-ind-etale-basis`. This changes no statement
dependency or Lean source.

## Where the brief, the DAG or earlier work was wrong

The returned delivery correctly identified that the private geometric-adjunction
proposition duplicated the downstream theorem. The downstream theorem cannot be imported
here: `ClosedSiteAdjunction` imports `AffineClosedSiteFunctorProperties`, so doing so
would close an import cycle. The repair removes the duplicate declaration entirely and
keeps the proof as a local construction, which preserves the target route without adding
a second named theorem. No target statement or definition was changed.

## New nodes

None.

## Earlier second reading (a previous round; superseded)

1. **Returned point repaired.** The declaration `geometric_adjunction` is absent from the
source. A repository-wide statement scan shows no newly declared theorem or lemma with the
same proposition as `exists_closedSiteAdjunction`. The target theorem still has its exact
original signature, and `lcompile.py` compiles it without warnings.

2. **Cycle check.** `ClosedSiteAdjunction` imports this module, so importing it here would
create a cycle. The adjunction construction is therefore retained as a local proof term,
with no duplicate named declaration. The existing public theorem remains available to its
own importers and is unchanged.

3. **Pruning record.** The earlier import-pruning changes are documented in
`coord/changes/affine-closed-site-functor-properties-import-pruning.md`; no additional
imports, declarations, nodes, or downstream modules were changed in this repair. The
static import-prune check and the delivery compiler both pass.


## Second reading by E1

1. **Interfaces: PASS.** Compared the complete delivered module with the repository
   version and checked its declaration table. The existing theorem's statement is
   byte-identical, and both the signature and body of `closedSiteLiftInclusion` are
   byte-identical. All additional declarations are private helpers; no public data
   construction was changed. The public import pruning is explicitly recorded in
   `coord/changes/affine-closed-site-functor-properties-import-pruning.md`.

2. **Proof and axioms: PASS.** Independently compiled the 667-line module with
   `lcompile.py` (4.7 seconds, no warnings). Compiled a scratch copy with
   `#print axioms` for both public declarations: exactly `propext`,
   `Classical.choice`, and `Quot.sound`. No `sorry`, new axiom, unsafe declaration,
   opaque declaration, foreign implementation, or proof hole inside data occurs.
   The algebra equivalence is eliminated inside a proof of bijectivity, and its
   formula on quotient representatives specifies the map. The site adjunction is
   constructed from the explicit `siteHomMap` and its proved bijectivity; no
   arbitrary witness of an unproved existence theorem supplies public data.

3. **Split statements and edge cases: PASS.** There are no split-off statements,
   new public lemmas, new nodes, or added holes. Checked the quotient and kernel
   arguments for arbitrary ideals, including the unit ideal, and the specialization
   argument for the zero ring: a prime is required before maximal-ideal existence
   is invoked. Empty covering families are allowed; finite extraction uses `Fin n`
   with no positivity assumption. The private covering lemmas impose no nonempty
   index or nonempty scheme hypothesis.

4. **Route and pruning: PASS after metadata correction.** Read the sources online
   because the literature files are absent locally:
   [Stacks 09BK](https://stacks.math.columbia.edu/tag/09BK) and
   [Stacks 097P](https://stacks.math.columbia.edu/tag/097P).
   The proof follows their algebra adjunction, closed fibre, specialization,
   flat going-down, and covering-refinement route. Read the imported algebra
   adjunction and units theorems, and Mathlib's `Flat.generalizingMap` and
   `Adjunction.isCocontinuous_iff_coverPreserving`. Independently repeated a Loogle
   search for the latter and searched the library for the site adjunction.
   `exists_closedSiteAdjunction` imports this item and derives its conclusion from
   this theorem, so using it here would be circular. The returned duplicate helper
   is absent. No shorter independent existing site theorem was found.
   The unit `sk-thm-properbasechange` and its `realized` nodes are unchanged; this
   auxiliary argument bypasses none of its three steps.

5. **DAG agreement: PASS after correction.** Checked all seven steps against the
   Lean: existing functors and coordinate structures; algebra Hom equivalence,
   naturality and quotient pushout; compact finite subcovers; base-change covers
   and right-adjoint limit preservation; Jacobson-radical specialization; flat
   generalization lifting; and the adjunction cocontinuity criterion.
   The cited algebra theorems provide exactly the bijectivity, reduction and unit
   reflection used. `Flat.generalizingMap` is the scheme form of the cited flat
   going-down node. Removed the unused `def-weil-pbc-proetale-site` proof dependency
   and replaced its covering-step reference with the affine-basis node. The final
   `proof_deps` is exactly the union of the steps' `uses`; only `proof`,
   `proof_deps`, and `proof_origin` differ from the repository node.

Second-reading changes: metadata pruning and this report; no Lean proof needed
repair. Recompiled the original downstream evaluation, adjunction, inverse-image
left-adjoint, and specialization-restriction modules against a freshly compiled
copy of the delivered module; all pass without warnings. The first, second and
fourth are the current direct importers; the left-adjoint module is an additional
indirect consumer. Updated the change record's verification wording accordingly.
