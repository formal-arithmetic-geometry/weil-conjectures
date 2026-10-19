## Worker report

The module `lean/Sheaf/AlgebraicTopology/MarkedSharpAnodyneRestriction.lean` states
`SSet.Marked.marked_sharp_anodyne_restriction` with `sorry` as its proof.  It uses the
canonical marked simplicial set API already recorded in the project.  The witness `e`
is a family, for every `K`, quasicategory `C`, and chosen proof that `C` is a
quasicategory, of isomorphisms

`mapSharp (sharp K) (natural C) ≅ (ihom K).obj (Enhanced.core C).toSSet`.

The first conjunct renders the clauses of the node's mapping identity and its
underlying-map normalization: for every degree `n`, degree `m`, sharp marked map `f`,
`x : K.obj m`, and `a : n ⟶ m`, the component of `e.hom` evaluates to
`f.val.app m (x, SSet.stdSimplex.objEquiv.symm a.unop)`.  The `.val` on the left
extracts the simplex of `C` from the corresponding simplex of the core.  Thus the
marked map and the same underlying simplicial map are identified with maps into
`C^≃`, including degree zero.

The second conjunct renders restriction naturality.  For every `r : K' ⟶ K`, the
marked precomposition map `mapSharpPre (sharpMap r) (natural C)` followed by the
chosen identification equals `(MonoidalClosed.pre r).app (Enhanced.core C).toSSet`
after the identification for `K'`.

The third conjunct renders postcomposition naturality.  For every map `f : C ⟶ D`
between quasicategories, `(ihom K).map (Enhanced.coreMap f)` after the
identification for `C` equals `mapSharpPost (sharp K) (naturalMap f)` followed by the
identification for `D`.

The final conjunct renders the anodyne restriction assertion.  For every `j : K ⟶ L`
that is degreewise injective (`Function.Injective (j.app n)` for every
`n : SimplexCategoryᵒᵖ`) and a realization weak homotopy equivalence, and every
quasicategory `C`, the restriction
`mapSharpPre (sharpMap j) (natural C)` has the right lifting property against
`SSet.modelCategoryQuillen.I`, i.e. every boundary inclusion, including `n = 0`.
No nonemptiness condition is introduced.

Canonical declarations used:

* `Sheaf.AlgebraicTopology.MarkedPointCartesianModel`:
  `SSet.Marked`, `SSet.Marked.sharp`, `SSet.Marked.natural`,
  `SSet.Marked.sharpMap`, `SSet.Marked.mapSharp`, `SSet.Marked.mapSharpPre`, and
  `SSet.Marked.mapSharpPost`.  These give the pair `(X,M_X)`, degenerate and maximal
  markings, products, and the marked mapping simplicial set exactly as in the node.
  This is the declaration family recorded by `lem-coef-marked-point-cartesian-model`.
* `Sheaf.AlgebraicTopology.MarkedFlatCategoricalEquivalenceTest`:
  `SSet.Marked.naturalMap`, the canonical map of natural markings.  The declaration
  transports inverse-edge witnesses and degenerate edges, rather than using an
  arbitrary map.
* `Sheaf.CategoryTheory.IsofibrationPullbackLimit`:
`SSet.Enhanced.coreMap`, the canonical restriction of a simplicial map to the
existing cores; the restriction clause itself uses the internal-hom map on the
core target, and postcomposition uses `(ihom K).map (Enhanced.coreMap f)`.
* `Sheaf.CategoryTheory.EnhancedDiagramsCones` (recorded dependency
  `def-cbc-enhanced-diagrams-cones`): `SSet.Enhanced.core`, the internal hom, and the
  functor simplicial set convention.
* `Sheaf.AlgebraicTopology.KanQuillenRightProper` (recorded dependency
  `lem-coef-kan-quillen-right-proper`): `Enhanced.IsWeakHomotopyEquivalence` and the
  Kan--Quillen boundary lifting class `SSet.modelCategoryQuillen.I.rlp`.
* `def-weil-size-convention` is the recorded metatheoretic size convention; the module
  uses one explicit input universe `u` throughout.

No dependency node was changed.  The marked API and `coreMap` declarations above are
already existing declarations in the project and are imported to avoid private copies;
the item's recorded dependency list supplies the enhanced, size, and Kan--Quillen
notions.

Edge cases checked before writing: `K` and `L` may be empty; `C` may be empty when it
satisfies the quasicategory predicate; `n = 0` is included in `I.rlp`; no vertex or
nonemptiness assumption is present; degenerate edges are always marked by `flat` and
`natural`; the product marking is coordinatewise; and every construction remains in
the input universe `u`.

Searches made:

* `msearch.py ... leanfinder "fully marked simplicial mapping complex restriction along a Kan trivial cofibration is a trivial Kan fibration and equals the core of a functor quasicategory"`: eight generic nerve/truncation hits, no marked mapping or restriction theorem.
* `msearch.py ... loogle "SSet.Marked.mapSharp, SSet.Marked.natural, SSet.Marked.sharp, SSet.Enhanced.coreMap"`: no Mathlib hits (these are project declarations).
* `msearch.py ... grep "Marked|mapSharp|naturalMap|coreMap|sharp_anodyne" Mathlib/AlgebraicTopology`: no Mathlib hits.
* `rg` over `WeilConjectures/` for `marked_sharp_anodyne_restriction`, `MapSharp`,
  `mapSharp`, `naturalMap`, and `coreMap`: no upstream declaration of this item;
  the project-side search found only the canonical declarations listed above.
* `rg` over `dag/nodes` for marked mapping and sharp/anodyne names: the existing
  `lem-coef-marked-point-cartesian-model` node supplies the marked API, while no node
  states this item's sharp restriction theorem.

Compilation with `scompile.py` passed for the module with no errors or warnings (the
single expected `sorry` declaration warning is suppressed by the module option).

## Second reading by Q01

I reread the node statement against the corrected signature.  The family `e` now has
target `(ihom K).obj (Enhanced.core C).toSSet`, so its vertices are functors landing
in the core of `C`; the explicit component formula has the required `.val` extraction
and records all simplicial degrees.  The restriction clause uses the internal-hom map
on the core target, and the postcomposition clause uses
`(ihom K).map (Enhanced.coreMap f)`.  The final conjunct keeps exactly the
degreewise-injective and weak-homotopy-equivalence hypotheses and states all boundary
lifts through `I.rlp`, including degree zero.  Empty inputs and universe `u` remain
unrestricted.  No node statement text or hypothesis was changed.

## Returned correction repaired

The returned review identified that `Enhanced.core ((ihom K).obj C)` is the core of
the whole functor quasicategory, whereas the node requires `Fun(K,C^≃)`.  For
`K = C = Δ[1]`, these have different vertex sets, so the former target made the
theorem false.  The module and its recorded `lean.statement` now use
`(ihom K).obj (Enhanced.core C).toSSet`, with the corrected component, restriction,
and postcomposition clauses above.  The docstring's first proof step was corrected to
factor through `Fun(K,C^≃)`.
