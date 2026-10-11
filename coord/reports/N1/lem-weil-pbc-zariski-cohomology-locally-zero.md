## Worker report

The module states that for a scheme `X`, an abelian sheaf `G` on the small Zariski site, an injective resolution `I`, a positive degree `q`, a class `ξ` in the degree-`q` cohomology presheaf at the terminal open, and a point `x`, there is an open `U` containing `x` on which the restriction of `ξ` is zero. The cohomology groups and restriction are rendered by Mathlib's `Sheaf.cohomologyPresheaf`: the map along `(homOfLE (show U ≤ ⊤ from le_top)).op` is exactly restriction from `X` to `U`. The theorem proof is `sorry`, as required for stage 2.

The hypotheses and clauses render as follows. `X : Scheme.{u}` is the scheme; `G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}` is an abelian sheaf on its small Zariski site; `I : InjectiveResolution G` is the chosen injective resolution; `q : ℕ` and `hq : 0 < q` express positive degree; `ξ : (G.cohomologyPresheaf q).obj (op ⊤)` is a cohomology class over `X`; and `x : X` is the point. The conclusion `∃ U : X.Opens, x ∈ U ∧ ... = 0` gives an open neighbourhood and says the restriction map sends `ξ` to zero. The map is induced by the inclusion `U ≤ ⊤` through the contravariance of the cohomology presheaf.

Dependency declarations used: `Sheaf.AlgebraicGeometry.ZariskiOpenRestrictionInjectives` (theorem `AlgebraicGeometry.zariski_open_restriction_injectives` and `AlgebraicGeometry.zariski_open_restriction_injectiveResolution`); `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic` (`CategoryTheory.Sheaf.cohomologyPresheaf`, `CategoryTheory.Sheaf.H'`); `Mathlib.CategoryTheory.Preadditive.Injective.Resolution` (`CategoryTheory.InjectiveResolution`); and `Mathlib.Topology.Sheaves.Sheaf` (`TopologicalSpace.Opens.grothendieckTopology`). The dependency module supplies the restriction preservation of injectives and resolutions used in the source setup.

Edge cases checked: `q` is constrained only by `0 < q`, so every positive integer is included; `U` is any open containing `x`, including `⊤`; no nonemptiness or separation hypothesis on `X` is imposed; and the class `ξ` may be zero. The restriction map uses the canonical inclusion into `⊤` and therefore also handles `U = ⊤`.

Searches for an existing local-vanishing theorem: `msearch.py leanfinder` queried “positive degree sheaf cohomology class vanishes on an open neighborhood of every point” and found none; `msearch.py loogle` queried `CategoryTheory.Sheaf.cohomologyPresheaf` and `CategoryTheory.Sheaf.H` and found only the generic cohomology constructions; `msearch.py grep` and `rg` searched Mathlib and `WeilConjectures` for local cohomology vanishing and found no matching theorem. The existing Mathlib cohomology presheaf is used directly rather than redeclared.

## Earlier second reading (a previous round; superseded)

The node and module were read together. `X`, `G`, `I`, `q > 0`, `ξ`, and `x` correspond one-for-one to the source statement. The existential open, membership condition, and zero restriction clause are present. Restriction is the presheaf map along the inclusion `U ≤ ⊤`; injective-resolution data is represented by `InjectiveResolution G` and the dependency module records its restriction properties. No extra geometric hypothesis or excluded edge case was introduced.

## Second reading by N1

I reread the node, its Stacks source place, the dependency records, and the Lean file
independently. The node introduces the following data and hypotheses, with the corresponding
Lean rendering and verdict:

- A scheme `X` is `{X : Scheme.{u}}`; this is the same small Zariski-site scheme and does
  not impose separatedness, Noetherianity, or nonemptiness.
- An abelian sheaf `\mathcal G` on `X_Zar` is
  `G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}`. This is the same site
  and coefficient category as [def-sc-zariski-site] and
  [def-weil-pbc-sites-and-cohomology].
- The node permits an arbitrary injective resolution `\mathcal G \to \mathcal I^\bullet`;
  Lean binds this as `(I : InjectiveResolution G)`. The restriction-resolution facts are
  supplied by `AlgebraicGeometry.zariski_open_restriction_injectiveResolution` from
  `Sheaf.AlgebraicGeometry.ZariskiOpenRestrictionInjectives`.
- A positive integer degree is `(q : ℕ) (hq : 0 < q)`, exactly the node's `q > 0`.
- A class in degree-q cohomology over the terminal open is
  `ξ : (G.cohomologyPresheaf q).obj (op ⊤)`. This is Mathlib's existing
  `CategoryTheory.Sheaf.cohomologyPresheaf`; the dependency record for
  [def-sc-zariski-cohomology] records this as the cohomology object.
- A point is `(x : X)`, with the same underlying scheme point and no extra condition.
- The conclusion is
  `∃ U : X.Opens, x ∈ U ∧ ... = 0`. The restriction map is the contravariant
  cohomology-presheaf map along
  `homOfLE (X := X.Opens) (x := U) (y := ⊤) le_top`, followed by `.op`; hence it maps
  the terminal-open class to the class over `U`, exactly the restriction in the node.
  The zero is in the target additive group. All clauses and quantifier order agree.

The only mismatch found was a statement-convention issue: the first-reading Lean used
`homOfLE (show U ≤ ⊤ from le_top)`, which introduces a hidden `have` in a declaration.
I changed it to the explicitly typed direct term
`homOfLE (X := X.Opens) (x := U) (y := ⊤) le_top`; the node's `lean.statement` was
updated verbatim and the module still compiles. No mathematical hypothesis or conclusion
was changed. The explicit `[HasExt ...]` is the Mathlib infrastructure required to form
`cohomologyPresheaf` (the recorded cohomology dependency uses the same infrastructure),
not an additional geometric or finiteness hypothesis.

Edge cases checked: `q = 0` is excluded exactly by `hq`; every positive natural is allowed;
`U = ⊤` is allowed; the empty scheme has no points and the conclusion is vacuous; the
class `ξ` may be zero; no assumption excludes the zero sheaf; and the universe is shared
between `Scheme`, the Zariski sheaf, and `AddCommGrpCat`, as required by the site encoding.

Existing-definition searches were repeated with the worker's LeanFinder/Loogle/grep
queries and with `rg` over `WeilConjectures/` and the repository's `lean/Sheaf/`.
Mathlib contains only the generic `Sheaf.cohomologyPresheaf`, `Sheaf.H'`, and restriction
infrastructure; neither Mathlib nor the project contains a theorem asserting local
vanishing of positive-degree Zariski cohomology classes. The dependency declaration
`AlgebraicGeometry.zariski_open_restriction_injectives` was opened and its exactness,
injective-preservation, and restricted-resolution statements match the node's cited
setup, so no duplicate or dependency repair is needed.

Compilation after the repair succeeds with `lcompile.py`; the declaration has only the
required `sorry` proof.
