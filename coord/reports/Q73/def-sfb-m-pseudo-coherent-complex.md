## Worker report

Defines `AlgebraicGeometry.Scheme.IsMPseudoCoherent` in
`Sheaf.AlgebraicGeometry.MPseudoCoherentComplex`. The definition has real predicate data,
no theorem and no `sorry`. Only the item's `lean` field changes. No new nodes,
dependency modules, or statement correction are needed.

Source read: `literature/stacks-project/cohomology.tex`,
`definition-pseudo-coherent` (Tag 08CB), clauses (1) and (3),
`lemma-pseudo-coherent-independent-representative` (Tag 08CC), clause (1) and proof,
and `definition-strictly-perfect` (Tag 08C4). Tag 08CC permits the displayed maps to
be derived-category maps. The definition does not choose a chain representative of L.
The current blueprint unit is `sk-thm-sf-ctf-stability`; this is a supporting definition,
not that unit's own statement.

Hypotheses and clauses:

- A scheme Y: `(Y : Scheme.{u})`. There is no quasi-compactness, separation,
  Noetherian, or quasi-coherent-cohomology hypothesis.
- An integer m: `(m : ℤ)`. All integers, including negative integers, are allowed.
- An object of the category of all module sheaves: `(L : schemeDerivedCategory Y)`.
  `HasDerivedCategory.{w}` for Y and its open subschemes supplies the localization
  infrastructure, using the standard `SheafOfModules` abelian instances. The module
  adds no chosen abelian structure and no equality between universes u and w.
- An open covering: `∀ x : Y, ∃ U : Y.Opens, x ∈ U ∧ ...`. This is the pointwise
  equivalent of existence of an arbitrary open cover with the following local data:
  given a cover, choose a member containing each x; conversely the opens with local
  data cover Y. One can index the converse by the set of qualifying opens, so there
  is no extra bound on the size of a cover and no finite-cover assumption.
- For each covering open, a complex P: the existential `P : CochainComplex
  (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U)) ℤ` uses precisely the
  module category required by the recorded `Scheme.IsStrictlyPerfect`.
- Strict perfection: `IsStrictlyPerfect Y U P` is used directly. Its definition
  requires finite degree support and each term to be a retract of a finite free
  module. It is not replaced by the stronger condition of being termwise free.
- P as a complex of modules on the open subscheme: `Equivalence.functor` of the
  fixed Mathlib `Scheme.Modules.overEquiv U`, with source and target categories
  explicitly specified, followed by `mapHomologicalComplex (ComplexShape.up ℤ)`.
  This is canonical transport from the over-site to the open subscheme; equivalences
  preserve zero objects, finite free modules and retracts. No arbitrary transport
  map or additional hypothesis is introduced.
- Its image in the derived category: `DerivedCategory.Q.obj` applied to that
  transported complex.
- The local comparison: `∃ α : ... ⟶ (derivedPullback U.ι).obj L`. Its codomain is
  exactly Lj*L on U.toScheme, using the recorded derived pullback construction.
- H^j is an isomorphism for j > m: `∀ j : ℤ, m < j → IsIso
  ((DerivedCategory.homologyFunctor ... j).map α)`. Cochain indexing gives H^j.
- H^m is surjective: `Epi ((DerivedCategory.homologyFunctor ... m).map α)`.
  Epimorphisms in the abelian category of module sheaves mean sheaf-surjectivity
  (locally liftable sections, equivalently surjectivity on stalks), as required;
  no surjectivity on sections of every open is asserted.
- Dependence on m: m is a parameter outside the entire local existential, so each
  degree can have a different cover, complex, rank, bounds, and morphism. There is
  no global boundedness condition.

Recorded dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`,
  `Scheme.Hom`, and the canonical inclusion `U.ι`.
- `def-pc-derived-category`: `WeilConjectures.AlgebraicGeometry.DerivedCategory`,
  `AlgebraicGeometry.schemeDerivedCategory`. It publicly supplies Mathlib's
  `DerivedCategory.Q` and `DerivedCategory.homologyFunctor`.
- `def-pc-perfect-complex`: `WeilConjectures.AlgebraicGeometry.PerfectComplex`,
  `AlgebraicGeometry.Scheme.IsStrictlyPerfect`. Its signature and complete
  finite-support/retract definition were read, rather than inferred from its name.
- `def-pc-derived-pullback`: `WeilConjectures.AlgebraicGeometry.DerivedPullback`,
  `AlgebraicGeometry.derivedPullback`; read the canonical transported construction,
  its `HasDerivedCategory` binders and its source/K-flat docstring.
- Mathlib's `AlgebraicGeometry.Scheme.Modules.overEquiv`, from
  `Mathlib.AlgebraicGeometry.Modules.Sheaf`, transports the over-site module category
  to the module category of the open subscheme. Naming `Equivalence.functor` with
  explicit categories uses the common `SheafOfModules` category instances.

Edge cases checked mathematically before writing:

- Empty Y: the pointwise covering condition is vacuous, matching the empty cover.
- Zero L: a zero strictly perfect complex supplies local approximations in every m.
- Strictly perfect L: the local identity gives every m, after the canonical transport.
- A vector space M in cohomological degree m on Spec k: the condition forces M to
  be finite dimensional. At cutoff m+1 the zero approximation works, verifying the
  strict inequality and the special epimorphism condition at m.
- Non-quasi-compact schemes: bounds and ranks vary with the open; no global upper
  cohomology bound or uniform finite rank is imposed.
- Negative m and empty covering members: there is no natural-number truncation or
  condition on empty opens that excludes them; empty opens can always be omitted.

Searches (2026-10-24 UTC; raw service results in sandbox `searches.jsonl`):

- msearch LeanFinder: `m pseudo coherent derived complex on a scheme locally admits
  strictly perfect approximations isomorphism above m surjection in degree m`.
  Eight hits on derived bounds/fractions and complex factorizations, no definition.
- msearch Loogle: `"PseudoCoherent"`. Zero hits.
- msearch grep of Mathlib: `PseudoCoherent|pseudo.?coher|StrictlyPerfect`. Zero hits.
- msearch LeanSearch: `m pseudo coherent complex locally strictly perfect approximation
  isomorphism cohomology greater than m surjective at m`. Eight hits on truncations,
  homology and quasi-isomorphisms; no match.
- rg of `lean/WeilConjectures` and `lean/Sheaf` for
  `IsMPseudoCoherent|mPseudoCoherent|m_pseudo|MPseudo`: the ring definition
  `DerivedCategory.IsMPseudoCoherent` is for ModuleCat, not schemes; the landed
  `AlgebraicSpace.IsMPseudoCoherent` is on the small etale algebraic-space model,
  not D(O_Y). Neither is the requested notion on schemes.
- rg/grep for the exact node id in `lean/WeilConjectures`: no hits.
- rg of `dag/lean_names_upstream.json` for the node id and `IsMPseudoCoherent`:
  no hits. The proposed full name does not already occur in the project sources.

No statement dispute or node fault found. Server single-file compilation through
`scompile.py` passed in sandbox mode (9.2 s) and library module mode (10.2 s),
with no errors or warnings.

## Second reading by Q73

I reopened the unchanged node statement and the final module and performed a separate
clause-by-clause rereading; no second agent was started, as the dispatch brief forbids it.
The scheme, arbitrary integer, and all-module derived category match the three inputs.
The pointwise neighbourhood quantifier is equivalent to the stated arbitrary open cover.
The complex is checked with the dependency's own strictly perfect predicate before being
transported by the canonical equivalence, and its derived image is the domain of α.
The codomain is the specified derived pullback along U.ι, not a newly supplied map.
The H^j condition has j > m, and the H^m condition is only epic, matching both clauses.
All local choices lie inside the fixed-m predicate. The arbitrary localization universe
is retained without restricting scheme universes or requiring quasi-coherence.
No mismatch or correction was found during this rereading.
