## What changed

Filled the sole remaining sorry in
`WeilConjectures.SixFunctors.Etale.Derived.EtaleLocalization`.
The proof follows all three steps of
`lem-etale-exceptional-locality-arbitrary-schemes` without changing its route.

First substitute the composite for h. A compactification of the composite gives
an immersion U into Z ×_Y X: its composite with the first projection is the
compactification's open immersion. The second projection is proper, and u is
quasi-compact, so `HasCompactification.of_isImmersion` supplies a compactification
of u. The canonical graph comparison identifies the chosen Ru_! with derived
exact etale sum extension. Transport its derived adjunction to Ru_!, compose
with the adjunction for f, and use compact-support composition to identify the
left adjoint with R(u ≫ f)_!. Right-adjoint uniqueness gives the required
isomorphism, after the existing exact/left-derived inverse-image comparison.

Added three private proof imports: compactification constructions, unbounded
compact-support composition, and the canonical etale graph comparison. Every
existing signature, attribute, public import, definition, and docstring is
unchanged. No other module or node needs adaptation. No new lemmas are introduced.

Validation: lcompile.py compiled the completed module without warnings (4.2 s).
An additional temporary #print axioms probe compiled (4.6 s) and showed propext,
Classical.choice, Quot.sound, and sorryAx inherited from existing dependencies;
this delivery claims a complete proof from the existing stated dependencies,
not elimination of their remaining holes. The diagnostic command was removed.

## Proved and sorry left

Closed 1 of 1 existing holes:
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_comp_leftDerivedUpperStar_of_etale`
(node `lem-etale-exceptional-locality-arbitrary-schemes`).

Zero sorry declarations remain in the item. Zero holes added; zero split off.
The existing proof of
`AlgebraicGeometry.Etale.isIso_of_isIso_leftDerivedUpperStar_map_of_surjective`
is unchanged. All dependencies were already stated in the library.

## No longer needed

None. No imports, declarations, nodes, or modules are removed or withdrawn.
All five declared proof dependencies of the locality node remain used.
The blueprint unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The node's reviewed_proof metadata records an earlier hole-free delivery, but
the current source again has the locality sorry. The present delivery fills
the actual current source hole using the node's unchanged plan. No mathematical
statement correction or process workaround is needed.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
