## What changed

Proved `AlgebraicGeometry.Scheme.ProEt.generic_component_site_comparison` in
`Sheaf.AlgebraicGeometry.GenericComponentSiteComparison`, preserving its full signature
and the three existing public imports. Local irreducibility attributes keep the
chosen component functor and projection, as well as the explicit component coordinates, folded during proof
elaboration. Private comparison isomorphisms are irreducible to avoid repeated unfolding.
Added private proved helpers and private proof imports only. The existing
`component_continuous` theorem from `Sheaf.AlgebraicGeometry.AffineComponentSiteProjection`
is registered solely as a local instance; no duplicate continuity theorem is declared.
No other Lean module changes.

The proof identifies the canonical chosen component functor with the existing explicit
component construction by its geometric characterization. Over an algebraically closed
field it proves that construction is a dense subsite: affine objects have totally
disconnected spaces and unchanged stalks, and thus are component objects on their actual
connected components. Fullness, faithfulness, and reflection of covers are proved
explicitly. Restriction is therefore an equivalence, and so is its left adjoint.

The two comparison isomorphisms are constructed on test objects first. The relative
comparison is the pullback universal property for component objects. The absolute
comparison uses the bijection between maps into relative profinite test schemes and
continuous label maps. Coordinate uniqueness proves inverse laws and naturality. The
resulting direct-image isomorphisms give the stated inverse-image isomorphisms by
adjunction mates. The existing point-pullback composition comparison finishes the
structural comparison.

Updated `lem-zl-generic-component-site-comparison` to record this proof route. There are
no new nodes, statement changes, existing definition changes, or consumer adaptations.
The preflight-requested scope record is
`coord/changes/generic-component-site-comparison-proof-scopes.md`; it lists all twelve
downstream consumers and documents the local attributes and unchanged theorem signature.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Scheme.ProEt.generic_component_site_comparison`
(node `lem-zl-generic-component-site-comparison`).

Added 0 holes. Remaining holes in the delivered Lean module: none. Every private helper
is proved. No obligations are split off. The full module compiled through `lcompile.py` in 31.6
seconds after fixing unwanted unfolding and two explicit conversions. A temporary
lower heartbeat setting used for diagnosis was removed before final delivery.

## No longer needed

No existing import is removed: the three public imports are retained for the statement.
The following planned proof dependencies are not needed directly by this proof:

- `lem-weil-pbc-fibre-product-affine-spectra`: the existing pro-etale base-change functor
  supplies the fibre, and Mathlib supplies its affine instance; no tensor presentation
  of this particular fibre is needed.
- `lem-weil-pbc-ind-etale-stability` (`Sheaf.RingTheory.IndEtaleStability`): the existing
  classification for affine weakly etale schemes over the geometric field suffices.
- `det-pe-condensed-point-basis` (`Sheaf.Paper.CondensedPointBasis`): use the already
  proved affine classification and stalk results of
  `Sheaf.Paper.GeometricFieldProfiniteDenseSubsite` instead.
- `lem-weil-pbc-locally-constant-prime-spectrum`: its use is encapsulated in the existing
  geometric-field classification and relative-label results, rather than repeated here.
- `lem-weil-pbc-site-equivalence-is-morphism-of-sites`
  (`WeilConjectures.CategoryTheory.SiteEquivalenceMorphismOfSites`): Mathlib's dense-subsite
  sheaf equivalence and adjunction equivalence transfer give the required result directly.
- `sk-def-sfb-pullback-from-point` (`Sheaf.AlgebraicGeometry.ProEtalePointPullback`): the
  statement uses the set-valued inverse image; its specified adjunction and composition
  isomorphism already live in the retained point-pullback interfaces.

These are local dependency removals; no module is withdrawn, and no claim is made that
other targets or consumers cease to need them. The affine-basis dependency is retained.

## Where the brief, the DAG or earlier work was wrong

The planned separate ind-etale base-change calculation is unnecessary: the proved
geometric-field affine classification applies to all affine weakly etale objects.
Consequently `hind` is not mathematically needed by this proof, but its binder is
preserved exactly. Empty schemes and empty profinite sets are covered by the same
universal properties, with no nonemptiness assumptions.

The proof uses existing proved private construction lemmas via `import all`; those
constructions and their modules are unchanged. The geometric-field dense-subsite and
relative-label nodes are generic tools, not replacements for the unit's route. The
unit record has no realized statement or step assigned to this auxiliary node, and the
parent's component-site argument is preserved.

Searches from the interrupted work are retained in `searches.jsonl`: LeanFinder,
Loogle, and grep found no theorem providing this complete comparison. The sandbox and
original budget metadata were retained when resuming; no clock metadata was changed.

## Second reading by W5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
