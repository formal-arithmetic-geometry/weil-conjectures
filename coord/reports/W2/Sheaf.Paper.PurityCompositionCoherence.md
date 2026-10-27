## What changed

Decomposed the invertibility hole in Sheaf.Paper.PurityCompositionCoherence using
an explicit inverse candidate and its two inverse equations. The item constructs
IsIso from that inverse and both equations, then transports it through the intermediate
realization unit and final coefficient equivalence. All original signatures,
definitions, public imports, options and visibility are unchanged. Two private proof
imports are added. No existing module is adapted and no change record is needed.

StandingExceptionalCompositionInverse constructs the candidate directly: at V=f!g!L,
apply the inverse f Hom bijection and inverse g Hom bijection to the identity,
precompose with the inverse compact-support compositor, then transpose through gf.
No data is chosen from a mere existence statement or a postponed theorem.
StandingExceptionalCompositionInverseLeft and StandingExceptionalCompositionInverseRight
state the two separate inverse equations. Each has its own source, full proof in words
and DAG node. Both are strictly smaller than invertibility and are required by the
item’s explicit IsIso constructor; neither asserts existence of an inverse or IsIso.

Validation: all four delivered Lean modules compiled in import order through lcompile.
The equations are typed for arbitrary separated finite-type maps of finite-type schemes,
without smoothness or absolute separatedness. The natural-Hom proof applies also to empty
schemes, zero objects and the zero finite ring. No unit route has been bypassed.

## Proved and sorry left

Original holes: 2. Fully proved without new holes: 0.
Decomposed 1 original hole:
WeilConjectures.PurityFiniteSetting.isIso_compositionExceptionalMap.
Its proof from the two new equation statements is complete and compiles.

Two new holes are left, each proof exactly by sorry:
AlgebraicGeometry.ProEtale.standingExceptionalComposition_inverse_hom
(node lem-pur-standing-composition-inverse-hom), and
AlgebraicGeometry.ProEtale.standingExceptionalComposition_hom_inverse
(node lem-pur-standing-composition-hom-inverse).

One original hole remains unchanged:
WeilConjectures.PurityFiniteSetting.smoothPurityCompositionCoherence
(node thm-pur-composition-coherence).

Total delivered holes: 3. Holes closed: 1; holes added: 2; this is a decomposition,
not a net proof or a claim of target completion. The explicit inverse definition has zero holes.

## No longer needed

No imports removed, nodes pruned or modules withdrawn. The invertibility reduction
uses the same canonical origin compositor and Hom bijections already imported by
StandingExceptionalComposition. The remaining main theorem retains its dependency plan
and the blueprint unit’s route. Unsuccessful private helper experiments and a definition
presentation repair were discarded; they are not part of this delivery.

## Where the brief, the DAG or earlier work was wrong

The orientation-descent dependency CompositionModelOrientationDescent imports this item
for its canonical comparison definitions. tools/import_direction.py may confirms importing
it here would create a cycle. The remaining main theorem is left untouched; this delivery
does not invent a replacement statement or remove that dependency.

The smooth composition_tensor_mate cannot alone prove isIso_compositionExceptionalMap,
whose domain includes nonsmooth maps. Its general invertibility argument is the
natural-equivalence argument recorded in the new equation docstrings. A long direct
formalization established representative naturality and the generic inverse criterion
in diagnostic files, but final conversion through the concrete functor presentations
could not be made to pass kernel checking within the per-file limit. The delivered
reduction exposes the two actual inverse-equation steps for further work; it does not
move IsIso to an equivalent renamed theorem.

Searches: LeanSearch and LeanFinder returned adjunction Hom naturality lemmas and
representability ingredients; Loogle returned Iso.mk and Yoneda uniqueness lemmas.
Mathlib and local searches found no standing pro-etale compositor inverse equation.
The generic naturality and Iso constructor declarations were read. All three search
kinds are recorded in the new nodes. The latest composition blueprint and unit route
were read. No existing declaration is removed or weakened.

## New nodes

The node def-pur-standing-composition-inverse records the explicit reverse-transpose
construction in Sheaf.Paper.StandingExceptionalCompositionInverse.

The node lem-pur-standing-composition-inverse-hom records c ≫ b = id in
Sheaf.Paper.StandingExceptionalCompositionInverseLeft.

The node lem-pur-standing-composition-hom-inverse records b ≫ c = id in
Sheaf.Paper.StandingExceptionalCompositionInverseRight.

The existing def-pur-composition-comparisons node’s proof, proof_deps and proof_origin
now record the explicit inverse and both inverse equations. Its statement and Lean
attachment are unchanged. The remaining main theorem’s node is unchanged.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
