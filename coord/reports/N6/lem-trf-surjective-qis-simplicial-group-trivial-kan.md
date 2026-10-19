## Worker report

The module `Sheaf.AlgebraicTopology.SurjectiveQuasiIsoTrivialKan` states
`CategoryTheory.SimplicialObject.trivialKanFibration_of_surjective_of_quasiIso` with proof `sorry`.
It uses Mathlib's alternating-face complex, extension along `ComplexShape.embeddingUpNat.op`,
and the exact boundary-lifting predicate `SSet.modelCategoryQuillen.I.rlp`.

The hypotheses render the node clauses as follows. `X Y : SimplicialObject AddCommGrpCat.{u}`
are simplicial abelian groups, and `f : X ⟶ Y` is their natural transformation. The hypothesis
`hsurj : ∀ n : ℕ, Function.Surjective (f.app (Opposite.op (SimplexCategory.mk n)))` is degreewise
surjectivity for every nonnegative degree. The hypothesis `hqis` asserts `IsIso` on every integer
homology map of the extended alternating-face chain map. Mathlib's alternating-face differential
is the alternating sum in positive degrees and the extension is zero outside nonnegative degrees,
so this renders the stated associated complex, including the zero degree map to zero. The
conclusion is `SSet.modelCategoryQuillen.I.rlp` on
`Functor.whiskerRight f (forget AddCommGrpCat.{u})`, the underlying simplicial-set map.

Dependency declarations used are `CategoryTheory.SimplicialObject` from
`Mathlib.AlgebraicTopology.SimplicialObject.Basic`, `HomologicalComplex.homologyMap` from
`Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`, `SSet` from
`Mathlib.AlgebraicTopology.SimplicialSet.Basic`, and `SSet.modelCategoryQuillen.I` with
`CategoryTheory.MorphismProperty.rlp` from
`Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations`.

Edge cases checked: degree zero is included in `hsurj`; the empty boundary gives vertex lifting;
negative integer degrees are zero under extension; zero groups and identity maps are allowed; no
freeness, projectivity, boundedness, or nonemptiness hypothesis is added.

Searches made: `msearch.py` leanfinder and leansearch for a surjective quasi-isomorphism of
simplicial abelian groups, loogle for `alternatingFaceMapComplex` and homology maps, grep of
Mathlib AlgebraicTopology/DoldKan and SimplicialObject, and `rg` of upstream WeilConjectures and
project `lean/Sheaf`. These found the generic simplicial-set model predicate and alternating-face
complex but no theorem stating this result. The exact item id has no upstream declaration.

## Second reading by N6

The module and node were reread against Stacks Tag 08P1 and Definition 08NL. Every binder and
clause matches: the alternating-face complex is extended on integer degrees, component maps are
those of `f`, surjectivity includes degree zero, and the conclusion tests all boundary inclusions.
No mismatch, hollow definition, or new node was found.

## Statement corrected

The old statement cited `def-weil-pbc-trivial-kan-fibration`, which is listed in
`coord/route-pivot-dropped.txt`, so the route-pivot gate rejected the dependency edge. The
correction removes only that DAG citation and `stmt_deps` edge. The conclusion remains the exact
Mathlib `SSet.modelCategoryQuillen.I.rlp` predicate, which is the same boundary lifting property,
including degree zero, described by Stacks Tags 08P1 and 08NL. The sole citer
`lem-trf-cotangent-sheaf-model` holds: its use of the item's trivial-Kan conclusion is unchanged.
