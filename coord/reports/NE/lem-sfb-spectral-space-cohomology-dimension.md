## Worker report

The module `Sheaf.Topology.SpectralSpaceCohomologyDimension` states
`TopCat.Sheaf.subsingleton_H'_top_of_spectralSpace_of_dimension_le`.
Its only theorem proof is `by sorry`; it introduces no definition, instance, or helper theorem.
The declaration docstring contains all nine steps of the node's proof.

Statement correspondence, hypothesis by hypothesis and clause by clause:

- A topological space T is `(T : Type u) [TopologicalSpace T]`.
- Spectrality is the recorded Mathlib class `[SpectralSpace T]`.
- The nonnegative integer bound is `(d : ℕ)`; this parametrizes exactly the integers d ≥ 0.
- The upper bound on topological Krull dimension is
  `(hd : topologicalKrullDim T ≤ (d : WithBot ℕ∞))`. This is an upper bound, not an
  equality, and the bottom value for the empty space is retained.
- Every abelian sheaf is covered by the arbitrary binder
  `(F : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})`.
- Every cohomological degree above d is `(q : ℕ) (hq : d < q)`.
- The cohomology group is the recorded `CategoryTheory.Sheaf.H' F q ⊤`, on the
  site of opens of T, with an explicit, canonically supplied HasExt instance.
  The top open computes global cohomology. As explained in the recorded dependency,
  Ext from its free abelian sheaf computes the right-derived global sections.
- Vanishing is `Subsingleton` of this abelian group: a group has a zero element, so
  subsingleton is exactly the assertion that every class is zero.
- The empty space is included: there is no Nonempty binder, and the dimension
  hypothesis allows bottom. No NoetherianSpace assumption occurs.

Dependency declarations read and used:

- `Mathlib.Topology.Spectral.Basic`, `SpectralSpace`: T0, compact, quasi-sober,
  quasi-separated, and a compact-open basis. T0 plus quasi-sober gives the node's sobriety.
- `Mathlib.Topology.KrullDimension`, `topologicalKrullDim`: `Order.krullDim` on
  `IrreducibleCloseds T`, valued in `WithBot ℕ∞`.
- `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`, `CategoryTheory.Sheaf.H'`:
  the cohomology presheaf evaluated at an object, here the top open. The full signature,
  its cohomology-presheaf definition, and surrounding docstrings were read.
- `WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf`,
  `CategoryTheory.Sheaf.isGrothendieckAbelian_of_essentiallySmall'`, together with
  `CategoryTheory.IsGrothendieckAbelian.enoughInjectives` and
  `CategoryTheory.hasExt_of_enoughInjectives`, supplies the Ext instance as an explicit
  term. These are consequences for the site, not extra hypotheses on T or F.

All recorded proof-dependency modules are imported, with ordinary imports for proof-only
material. The Mathlib matches for enough injectives on sites and module categories are
also imported. The two proof-only nodes
`lem-sfb-punctured-spectral-neighborhood-dimension` and
`lem-sfb-quasi-compact-restriction-acyclicity` have no recorded Lean declaration at this
writing; their proof steps remain documented, and they do not supply any object needed
by this theorem's signature. No import was omitted for a cycle.

Edge cases checked mathematically before drafting:

- Empty T has dimension bottom, so satisfies every natural upper bound; all sheaf
  cohomology is zero, and the signature excludes no such T.
- d = 0 gives positive-degree vanishing on a dimension-zero spectral space, agreeing
  with profinite cohomology vanishing. It does not assert vanishing of global sections.
- q = 0 cannot satisfy d < q. q = d is also excluded, as the source requires.
- A dimension strictly below d still satisfies hd; no dimension-realizing chain is required.
- The zero sheaf is allowed. No finiteness or torsion constraint is imposed on F.
- Space and coefficient universes use the established common universe convention for
  topological abelian sheaves and `H'`. The theorem is universe-polymorphic; a larger
  common universe accommodates a given space and its coefficient groups. There is no
  independently undersized universe for test objects or indexing sets.

Searches for an existing statement (2026-10-22):

- `msearch.py` leanfinder, query “Cohomology of abelian sheaves on a spectral topological
  space vanishes above its Krull dimension”: 8 hits, including `Sheaf.H`,
  `Sheaf.cohomologyPresheaf`, derived-category t-structure vanishing and injective-dimension
  criteria. None gives the spectral-space dimension bound.
- `msearch.py` loogle, query `topologicalKrullDim, CategoryTheory.Sheaf.H`: 0 hits.
- `msearch.py` grep, query
  `spectral.*cohomolog|cohomolog.*Krull|cohomologicalDimension`: 9 hits, all spectral-sequence
  or spectral-object infrastructure, not spectral topological spaces.
- `msearch.py` leansearch, query “Spectral space cohomology vanishes in degrees above
  topological Krull dimension”: 8 hits consisting of dimension/spectral-space definitions,
  scheme spectrum facts, and the locally Artinian criterion. No matching theorem.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` with the same concepts found spectral-limit
  continuity, profinite vanishing and Noetherian vanishing. The signature of
  `TopCat.Sheaf.subsingleton_H_of_topologicalKrullDim_lt` in
  `WeilConjectures.Topology.Sheaves.GrothendieckVanishing` was read: it requires
  `[NoetherianSpace X] [QuasiSober X]`, so does not state this node.
- `rg` for the item id in `lean/WeilConjectures` found no declaration. Project hits in
  `ZeroDimensionalBaseAffineGlobal` only cite the item in a proof docstring.
- `rg` in `dag/lean_names_upstream.json` and the topology source directories found no
  declaration of this spectral-space cohomology bound.

Source checked: `literature/stacks-project/cohomology.tex`, proposition
`proposition-cohomological-dimension-spectral` (Tag 0A3G), including its simultaneous
induction proof. Part (1) agrees with the node; an upper bound d yields the stated form.
No statement correction or disputed statement is needed. No new nodes or dependency
repairs are needed.

Validation: the delivered file compiled cleanly both as a sandbox module and at its
library module path through the prescribed `scompile.py`; no warnings or errors were
reported. The node changes only in `lean`, whose signature is copied verbatim from the
file. All variables and the universe are explicit; `autoImplicit` is disabled.

## Second reading by NE

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
