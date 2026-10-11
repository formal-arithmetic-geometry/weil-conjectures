## Worker report

The module `Sheaf.AlgebraicGeometry.ProjectionFormulaLocality` states locality of the
projection-formula map.  It uses schemes `X Y`, a morphism `f : X ⟶ Y`, derived objects
`E : D(O_X)` and `K : D(O_Y)`, an index type `I`, opens `U : I → Y.Opens`, and the cover
hypothesis `∀ y, ∃ i, y ∈ U i`.  The morphism `φ` has source
`(Rf_* E) ⊗ K` and target `Rf_*(E ⊗ Lf^* K)`, rendered by
`((schemeDerivedDirectImage f).obj E) ⊗ K ⟶
(schemeDerivedDirectImage f).obj (E ⊗ ((derivedPullback f).obj K))`.
The conclusion `IsIso φ ↔ ∀ i, IsIso (...)` renders the global isomorphism criterion
and each restriction criterion using
`(schemeOpenRestriction Y (U i)).mapDerivedCategory.map φ`.

The dependency declarations used are `AlgebraicGeometry.schemeDerivedCategory`
(`Sheaf.AlgebraicGeometry.DerivedCategory`),
`AlgebraicGeometry.schemeDerivedDirectImage`
(`Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`),
`AlgebraicGeometry.derivedPullback` (`Sheaf.AlgebraicGeometry.DerivedPullback`), and
`AlgebraicGeometry.schemeOpenRestriction`
(`Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps`).
The tensor is Mathlib's monoidal tensor on the globally installed
`schemeDerivedTensorMonoidal` instance.

Edge cases checked: the index type is arbitrary (including empty); the cover hypothesis
then correctly rules out an empty cover on a nonempty scheme, while allowing the empty
scheme; opens may repeat or be empty; no finiteness or nonemptiness assumption is added.
The searches recorded in the node were reviewed: LeanFinder found only
`AlgebraicGeometry.IsLocalAtTarget.iff_of_openCover`; Loogle found only generic
`CategoryTheory.Functor`; grep found no derived projection-formula declaration.  Searches
of `lean/Sheaf` and the upstream `WeilConjectures` checkout found no matching scheme-level
statement.  No `STATEMENT-DISPUTED` issue was found.

## Earlier second reading (a previous round; superseded)

The node and module were read together.  The scheme and derived-category hypotheses are
represented by the explicit binders and typeclass parameters.  The open-cover clause is
represented by `I`, `U`, and `hcover`; the two clauses of the iff are represented by
`IsIso φ` and the quantified restricted maps.  The canonical projection-formula map is
represented by the explicitly typed `φ` argument, whose source and target are exactly the
objects displayed by the node.  No hypotheses or edge cases were dropped.

## Second reading by Q1

The node introduces a morphism of schemes `f : X ⟶ Y`, assumes it is quasi-compact and
quasi-separated, introduces derived objects `E : D(O_X)` and `K : D(O_Y)`, an index type
`I`, an indexed family of opens `U : I → Y.Opens`, and the cover condition
`∀ y, ∃ i, y ∈ U i`.  Its conclusion compares `IsIso φ` for the projection-formula
map from `(Rf_* E) ⊗ᴸ K` to `Rf_*(E ⊗ᴸ Lf* K)` with `IsIso` of every restriction
along `schemeOpenRestriction Y (U i)`.

The Lean renders these as `(f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]`,
`E : schemeDerivedCategory X`, `K : schemeDerivedCategory Y`, `(I : Type v)`,
`(U : I → Y.Opens)`, and `(hcover : ∀ y : Y, ∃ i : I, y ∈ U i)`.  The displayed
`φ` has exactly the node's source and target, and the conclusion is
`IsIso φ ↔ ∀ i, IsIso ((schemeOpenRestriction Y (U i)).mapDerivedCategory.map φ)`.
The explicit `φ` binder is the Lean representation of the node's canonical
projection-formula map; no other morphism or condition is introduced.

The first reading omitted the node's quasi-compact and quasi-separated hypotheses.
I added the corresponding Mathlib typeclass binders and imports.  No other mismatch
was found.  The index type permits the empty index, while `hcover` correctly rules
that out for a nonempty `Y`; empty opens and repeated opens remain allowed, and the
empty scheme is covered.  No characteristic, finiteness, or universe restriction is
added.  Existing-declaration searches (LeanFinder/Loogle and grep of Mathlib,
`WeilConjectures`, and `lean/Sheaf`) found no scheme-level projection-formula
locality statement; only generic open-cover locality declarations were present.
The repaired module compiles cleanly with `lcompile.py`.
