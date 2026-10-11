## Worker report

The module `Sheaf.AlgebraicGeometry.ZariskiDimensionBound` states
`AlgebraicGeometry.isZero_zariskiCohomology_of_dimension_bound`, with proof `sorry`.
No definitions, dependency modules, new nodes, or statement corrections are needed.

Hypothesis and conclusion correspondence:
- Scheme X: `(X : Scheme.{u})`.
- Quasi-compact: `[CompactSpace X]`, with no Hausdorff condition.
- Locally Noetherian: `[IsLocallyNoetherian X]`. Together these are exactly the
  node's Noetherian hypothesis.
- Nonnegative integer bound d: `(d : ℕ)`. Every nonnegative integer has this form.
- Topological dimension at most d: `hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞)`.
- Every abelian sheaf F on the small Zariski site:
  `(F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})`.
  The topology uses open subsets and inclusion arrows, with pointwise covering sieves.
- Every degree q above d: `(q : ℕ) (hq : d < q)`; since d is nonnegative,
  all integer degrees satisfying q > d are natural degrees.
- Vanishing of H^q(X_Zar,F): `IsZero (Sheaf.H' F q (⊤ : X.Opens))`.
  This is zero as an abelian-group object, exactly the node's recorded cohomology
  declaration specialized to the whole-space open. It imposes no condition on F.

Dependency declarations inspected and used:
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, via Noetherian import.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`, via Noetherian import.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Mathlib.CategoryTheory.Sites.Spaces`: `TopologicalSpace.Opens.grothendieckTopology`.
  `TopCat.Sheaf` in `Mathlib.Topology.Sheaves.Sheaf` is definitionally the same category;
  its full definition and docstring were inspected.
- `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`: `CategoryTheory.Sheaf.H'`.
  Its full signature and docstring were inspected. The Grothendieck sheaf, HasExt,
  and abelian-group AB imports supply its existing instances; no extra hypothesis
  or private cohomology definition is introduced.

Edge cases: the empty scheme has dimension bottom, so satisfies the bound for every
natural d; there is no Nonempty hypothesis. For d = 0, q is any positive degree.
The zero sheaf is allowed. Schemes with dimension infinity do not satisfy any finite
bound, as required. No irreducibility, separatedness, affineness, torsion restriction,
or coefficient field is imposed. Universe u is explicit and arbitrary; the opens
category and abelian groups use the matching universe required by H'.

Searches for an existing statement (msearch.py, item lem-sc-zariski-dimension-bound):
- LeanFinder: "Cohomology of any abelian Zariski sheaf on a Noetherian scheme vanishes
  above its topological Krull dimension". Eight hits: injective-dimension criteria,
  derived t-structure vanishing, and Sheaf.H; no matching statement.
- Loogle: "topologicalKrullDim, Sheaf.H". No hits, unknown identifier Sheaf.H.
- Mathlib grep: "subsingleton_H_of_topologicalKrullDim|vanishing.*Noetherian".
  Five hits concerning ring order of vanishing; no matching cohomology theorem.
- LeanSearch: "Cohomology of an abelian sheaf on a Noetherian scheme vanishes above
  its Krull dimension". Unavailable: Internal Server Error.
- rg in WeilConjectures for the item id: no hits. Searches for topologicalKrullDim,
  Zariski dimension, and the proposed declaration name found no matching theorem.
  The nearby Scheme.Modules dimension vanishing concerns module cohomology, not this
  arbitrary abelian sheaf statement.
- rg in lean/Sheaf and dag/lean_names_upstream.json for the proposed name and
  Zariski dimension bound: no matching declaration. The general topological
  vanishing node has no Lean record and is a proof dependency only.

The local literature files are absent on this machine. Opened and read the source
https://stacks.math.columbia.edu/tag/02UZ: Proposition 20.20.7 states the dimension
bound for any abelian sheaf on a Noetherian topological space. Specializing to the
scheme's underlying space is exactly the node's proof, reproduced in the docstring.
No node faults or STATEMENT-DISPUTED issues were found.

Validation: lcompile.py compiled the module cleanly (2 seconds), with no warnings.

## Second reading by M1

I independently read the node statement, its dependency records, and
`Sheaf.AlgebraicGeometry.ZariskiDimensionBound` line by line. The objects and
hypotheses correspond as follows:

- The scheme (X) is `(X : Scheme.{u})`; quasi-compactness is the instance
  `[CompactSpace X]`, and locally Noetherian is `[IsLocallyNoetherian X]`.
  These are exactly the two clauses of the node's Noetherian-scheme
  hypothesis, with no separatedness, irreducibility, or finiteness condition.
- The integer bound is `(d : ℕ)`, and the dimension inequality is
  `hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞)`, matching the node's
  `dim X ≤ d`, including the empty scheme and the bottom dimension case.
- An arbitrary abelian sheaf on the small Zariski site is
  `(F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})`; the site is
  precisely the opens site recorded by `def-sc-zariski-site`.
- The degree and strict inequality are `(q : ℕ) (hq : d < q)`, so every
  degree above the bound is covered, including `d = 0`; no positive-degree or
  nonzero-sheaf assumption is added.
- The conclusion is `IsZero (Sheaf.H' F q (⊤ : X.Opens))`, the recorded
  object-valued cohomology at the whole-space open, which is the dependency
  declaration for Zariski cohomology. The zero sheaf is therefore included.

I checked the edge cases explicitly: the empty scheme is admitted, `d = 0`
forces only positive `q`, the zero sheaf is admitted, and no finite-dimensional
or characteristic assumption beyond the displayed bound is introduced. The
universe `u` is shared by the scheme, opens, and abelian groups, so no case is
lost through an independent universe.

I repeated the existing-definition searches (LeanFinder/Loogle, LeanSearch,
and grep in Mathlib, `WeilConjectures`, and `lean/Sheaf`). They found no
matching theorem or project declaration; `TopologicalSpace.Opens.grothendieckTopology`
and `CategoryTheory.Sheaf.H'` are the existing dependency declarations used
here. The Stacks source is Proposition 02UZ, whose Noetherian-space theorem
has exactly the stated dimension-bound conclusion.

No mismatch was found, so no source or node change was needed. The module
compiled cleanly with `lcompile.py`; its only proof is the required `sorry`.
