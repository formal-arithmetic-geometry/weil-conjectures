## What changed

Proved `AlgebraicGeometry.existsUnique_factor_through_point_blowup` in
`Sheaf.AlgebraicGeometry.PointBlowdownFactorization`, preserving its exact statement
and public imports. Added the private proof import
`Sheaf.AlgebraicGeometry.RegularPointBlowupFunctions` and applied its existing theorem
`isIso_structureSheafMap_point_blowup`.

The proof follows all five existing DAG steps and Stacks Project, Resolution of
Surfaces, Tag 0C5J (`resolve.tex`, lemma-factor-through-contraction, read in full).
The singleton exceptional image gives a point in the exceptional fibre. The
complement isomorphism supplies all other preimages and injectivity off the centre.
Local Noetherianity gives properness of the blowup, hence a closed quotient map.
The continuous-map quotient lift descends the underlying map. A proved private
helper descends the sheaf map using the inverse canonical direct-image map.
At each point, choose a preimage; stalk composition and `isLocalHom_of_comp` prove
locality. Another proved private helper cancels the direct-image isomorphism and
uses surjectivity on points to prove uniqueness.

No new mathematical result is assumed and no new node is needed. The existing
DAG proof and dependency list already describe this argument. The unit route is
preserved (`sk-thm-sf-ctf-stability`, whose realized lists are empty).

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.existsUnique_factor_through_point_blowup`
(node `lem-sfb-point-blowdown-factorization`).

Added 0 holes; split off 0 statements. No `sorry` remains in this module or is
added elsewhere. Both private helpers are completely proved. The imported
`AlgebraicGeometry.isIso_structureSheafMap_point_blowup` retains its existing hole
in its existing module and node `lem-sfb-regular-point-blowup-functions`; this
packet does not alter that module.

## No longer needed

Removed the direct private import
`Mathlib.Geometry.RingedSpace.LocallyRingedSpace`: its API is publicly imported
by the new, necessary `RegularPointBlowupFunctions` dependency.
No DAG dependency or module is pruned: all five existing proof dependencies remain
used (complement isomorphism, blowup properness, proper implies closed, canonical
structure-sheaf isomorphism, and locally ringed-space morphisms).

## Where the brief, the DAG or earlier work was wrong

None. The existing auxiliary handles lower local-dimensional components and its
nonempty-fibre hypothesis follows from the stated singleton-image assumption.
Neither equidimensionality, separatedness of the target, nor extra regularity
hypotheses are used. The argument is valid for arbitrary target schemes.

Searches through the prescribed `msearch.py` services (LeanFinder, Loogle, grep)
and direct searches of Mathlib and both project roots found no existing blowdown
factorization theorem. Mathlib does supply the closed-map quotient lift and the
stalk locality cancellation used here.

## Second reading by X7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
