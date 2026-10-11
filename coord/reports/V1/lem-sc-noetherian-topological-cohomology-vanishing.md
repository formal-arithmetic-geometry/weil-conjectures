## Worker report

The module `Sheaf.Topology.NoetherianTopologicalCohomologyVanishing` states
`TopCat.isZero_noetherian_topological_cohomology_of_dimension_bound`. It uses the
Mathlib notion `TopologicalSpace.NoetherianSpace X` for the node's Noetherian
hypothesis, `topologicalKrullDim X ≤ (d : WithBot ℕ∞)` for the dimension bound,
and `Sheaf.H' F q (⊤ : Opens X)` for the degree-q cohomology of the abelian sheaf
on the opens of X. The conclusion is `IsZero` of that additive-group object,
rendering that the cohomology group is zero. The integer degree in the prose is
represented by `q : ℕ`, the degree type of the recorded cohomology declaration.

The Lean signature renders each clause as follows:

- `X : Type u` with `[TopologicalSpace X]` introduces the topological space.
- `[NoetherianSpace X]` is the Noetherian hypothesis.
- `d : ℕ` and `hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞)` give the
  nonnegative integer and the topological Krull dimension bound.
- `F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}` is an abelian
  sheaf on the opens of X.
- `q : ℕ` and `hq : d < q` express the degree above the bound.
- `IsZero (Sheaf.H' F q (⊤ : Opens X))` states vanishing of the cohomology.

The dependency declarations used are `topologicalKrullDim` from
`Mathlib.Topology.KrullDimension` (the recorded declaration for
`def-kun-topological-krull-dimension`) and `CategoryTheory.Sheaf.H'` from
`Mathlib.CategoryTheory.Sites.SheafCohomology.Basic` (the recorded declaration
for `def-sc-topological-abelian-cohomology`). The open-site instances for
sheafification and Ext are supplied by the imported Mathlib site modules.

Edge cases checked: the empty space is admitted by `NoetherianSpace X` and has
`topologicalKrullDim X = ⊥`, hence satisfies every displayed finite bound; d = 0
and q > 0 are admitted; q is necessarily nonnegative as required by `Sheaf.H'`.
No extra separation, quasi-compactness, irreducibility, or nonemptiness
hypothesis was added.

Searches made: `msearch.py V1 lem-sc-noetherian-topological-cohomology-vanishing
leanfinder "For a Noetherian topological space of finite Krull dimension d, sheaf
cohomology H^q(X,F) vanishes for every abelian sheaf F and q>d"` returned eight
nearby homological zero results (including `CochainComplex.isZero_of_isGE` and
`DerivedCategory.isZero_of_isLE`) but no topological Noetherian cohomology
statement. `msearch.py ... loogle "topologicalKrullDim, Sheaf.H'"` returned
zero hits because `Sheaf.H'` was not recognized by Loogle. The grep search
`msearch.py ... grep "vanishing.*Noetherian|subsingleton_H_of_topologicalKrullDim"
Mathlib` returned no direct theorem (only the unrelated scheme-module result in
slopmaster2); the same grep over `WeilConjectures` returned the unrelated
`AlgebraicGeometry.Scheme.Modules.subsingleton_H_of_topologicalKrullDim_lt` and
other textual matches. Direct `rg`/`grep` searches of the project and upstream
source found no declaration of this theorem. The dependency declarations were
opened at `Mathlib/Topology/KrullDimension.lean` (`topologicalKrullDim`) and
`Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean` (`Sheaf.H'`).

## Earlier second reading (a previous round; superseded)

Read the node statement and module signature together. The Noetherian class,
dimension inequality, abelian sheaf object, degree inequality, and `IsZero`
conclusion all occur with the same objects and hypotheses; the empty-space case
is included. The two dependency declarations are imported directly and no
private duplicate notion is introduced. The file compiles cleanly with the
expected `sorry` warning.

## Second reading by V1

I independently read the item node, its Stacks source (Proposition 02UZ,
cohomology-proposition-vanishing-Noetherian), the dependency records, and the
Lean file. The node introduces a topological space X, assumes NoetherianSpace X,
chooses an integer d ≥ 0 with topological Krull dimension dim X ≤ d, introduces
an abelian sheaf F on X, and concludes H^q(X,F)=0 for every integer q>d.
The Lean renders these respectively as `(X : Type u) [TopologicalSpace X]`,
`[NoetherianSpace X]`, `(d : ℕ)` and
`hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞)`,
`F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}`, and the binders
`(q : ℕ) (hq : d < q)` followed by
`IsZero (Sheaf.H' F q (⊤ : Opens X))`. `topologicalKrullDim` is exactly the
recorded dependency `def-kun-topological-krull-dimension`, and `Sheaf.H'` is
exactly `def-sc-topological-abelian-cohomology`; no private or specialized
replacement is introduced. The quantifier order and all hypotheses match the
node, with no extra separation, quasi-compactness, irreducibility, or
nonemptiness assumptions.

The empty space is admitted (its dimension is below every finite d), d = 0 is
allowed, and q is any natural number strictly above d. The universe of F and
X is shared, so no case is excluded by an independent universe. Zero sheaves
and zero cohomology objects are covered by `IsZero`; no characteristic
hypothesis occurs in the source or node. The source proof is documented in the
statement docstring step by step (dimension and irreducible-component
inductions, the constant-sheaf base case, and the extension-by-zero reduction).

I searched Mathlib and the upstream project with LeanSearch, LeanFinder/Loogle,
and grep for Noetherian topological cohomology vanishing and for combinations
of `topologicalKrullDim` and `Sheaf.H'`. These found only the primitive
notions and an unrelated scheme-module theorem, so this declaration is not an
existing duplicate. The file compiles cleanly with only the permitted `sorry`
proof warning. No mismatch was found and no source, node, or Lean change was
needed in this second reading.
