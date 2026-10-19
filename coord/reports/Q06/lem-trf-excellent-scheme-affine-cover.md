## Worker report

The module `Sheaf.AlgebraicGeometry.ExcellentSchemeAffineCover` states
`AlgebraicGeometry.isExcellent_of_affine_open_cover`.  It uses the existing Mathlib
scheme notion (`AlgebraicGeometry.Scheme`) and the project definition
`IsExcellent` from `Sheaf.RingTheory.ExcellentRing`.

The hypotheses and conclusions render the node as follows:

* `{X : Scheme.{u}}` is the scheme in the first sentence.
* `{I : Type v}` and `U : I → X.Opens`, together with
  `hcover : TopologicalSpace.IsOpenCover U`, express the arbitrary-index affine open
  covering `X = ⋃ i, U i`.  No finiteness or nonemptiness of `I` is imposed.
* `haff : ∀ i : I, IsAffineOpen (U i)` says every member is an affine open
  subscheme.
* `hexc : ∀ i : I, IsExcellent Γ(X, U i)` says each coordinate ring
  `O_X(U_i)` is excellent.
* The first conjunct
  `∀ V : X.Opens, IsAffineOpen V → IsExcellent Γ(X, V)` is the assertion for every
  affine open subscheme `V ⊆ X`.
* The second conjunct quantifies every open subscheme `W : X.Opens` and every
  `V : (W.toScheme).affineOpens`, asserting
  `IsExcellent Γ(W.toScheme, V)`.  The canonical affine-open basis therefore gives
  the required affine cover of each open subscheme, with its restricted structure
  sheaf represented by `W.toScheme`.

The statement dependencies read and used are:

* `def-pc-scheme`: `AlgebraicGeometry.Scheme` from Mathlib's
  `Mathlib.AlgebraicGeometry.Scheme` (the `Scheme` and `Opens` objects used above).
* `def-exc-excellent-ring`: `IsExcellent` from
  `Sheaf.RingTheory.ExcellentRing` (its full definition is the conjunction of
  quasi-excellence and universal catenarity).

The source proof also names `lem-trf-g-ring-affine-cover`,
`lem-trf-j2-affine-cover`, `lem-trf-universally-catenary-affine-cover`, and
`pqf-def-locnoeth`; these are proof dependencies only and have no recorded Lean
modules in the DAG, so the stage-2 statement imports the available definition
modules and leaves the theorem proof as `sorry`.

Edge cases checked: an empty index type can cover only the empty scheme; the empty
scheme and empty open subscheme are handled by the same affine-open basis (and the
zero coordinate ring); the empty affine open is allowed; `I` and all scheme universes
remain arbitrary; and no finite-cover or quasi-compactness assumption was added.
The identity open `W = ⊤` recovers the first conclusion through the ambient scheme.

Searches recorded on the node were reviewed: LeanSearch and LeanFinder semantic
queries, Loogle queries for `Excellent`, and grep searches for excellence, G-ring,
J-2, and catenary found no existing Mathlib theorem or predicate.  Project searches
(`rg` over `WeilConjectures` and `lean/Sheaf`, and DAG searches) found no declaration
of this affine-cover theorem.  The existing `IsExcellentScheme` predicate in
`Sheaf.Paper.OrgogozoInductionData` is a different, already-defined global predicate;
it is not needed to state the two clauses here, so no duplicate definition is made.

## Second reading by Q06

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
