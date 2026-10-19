## Worker report

The delivery states `SSet.SegalSpace.segal_space_inner_anodyne_locality` in
`Sheaf.AlgebraicTopology.SegalSpaceInnerAnodyneLocality`. Its only theorem proof is
`sorry`. It introduces no definitions, selects no replacement, and changes no existing
definition or natural-language statement. Three already landed statement dependencies
are added to identify the interfaces used: `def-coef-homotopy-segal-space`,
`lem-coef-simplicial-space-reedy-cartesian`, and
`lem-coef-segal-categorical-equivalence-dk`.

I read the item's statement, source, all six proof steps, its original statement
dependency and its complete recorded declaration interface. I also read the statements
and records of the seven proof dependencies and the three added statement dependencies.
The newly used declarations were read with their signatures and docstrings in their
own source files. A graph traversal verified that none of the three added nodes reaches
the item, so these additions do not create a dependency cycle.

The model of the statement is the existing Reedy presentation, not the ordinary category
of strict natural transformations used as a replacement for coherent mapping spaces.
A space-valued simplicial presheaf is represented by a levelwise Kan simplicial diagram
`W : SimplexCategoryᵒᵖ ⥤ SSet.{u}`. For every Reedy fibrant replacement `i : W ⟶ V`,
the existing simplicial complex `mappingSpace (Segal.discreteSpace K) V` computes
`Map(dK,W)`. The recorded Reedy/cartesian interface identifies every simplicial space
as cofibrant; its enriched mapping complex into a fibrant diagram computes the derived
mapping space. Reedy replacement exists by the recorded Reedy model structure, so
quantifying over every such replacement is not a vacuous extra hypothesis. This is the
same replacement convention already used by `lem-coef-segal-inverse-evaluation`.
It is essential to replace the target: the strict mapping complex into a general
levelwise Kan diagram need not be the derived mapping space.

Hypotheses and clauses, in order:

* The fixed small universe is the explicitly bound `universe u`. `SSet.{u}` and its
  levels are small; the category of all such diagrams lives in `Type (u+1)`. The
  simplex indexing category is Mathlib's `SimplexCategory`. There is no equality
  imposed between independent size parameters and no finiteness assumption on K or L.
* The space-valued simplicial diagram is the binder
  `W : SimplexCategoryᵒᵖ ⥤ SSet.{u}` together with
  `HomotopySegal.IsHomotopySegalSpace W`. The first component of that existing
  predicate says every value is Kan, exactly the chosen model of spaces.
* The homotopy Segal condition is the second component of that same predicate:
  every `HomotopySegal.comparison W n` is a realization weak equivalence. Its
  `target W n` retains `n+2` edges and `n+1` joining paths in `W₀`. The comparison
  restricts to consecutive edges and inserts constant paths at shared vertices.
  Hence these are homotopy pullbacks, rather than ordinary pullbacks. The index
  `n : ℕ` covers exactly all outer degrees at least two.
* `Segal.discreteSpace K` is the already defined discrete diagram `dK`:
  `K ⋙ Functor.const SimplexCategoryᵒᵖ`. Its value at an outer degree is constant
  in the inner simplicial direction, on the set `K_n`.
  `Segal.discreteSpaceMap f` is the canonical degreewise map induced by f.
* `K L : SSet.{u}` and `f : K ⟶ L` are arbitrary small simplicial sets and an
  arbitrary simplicial map. `innerAnodyneExtensions f` expresses the stated
  inner-anodyne condition. I read Mathlib's definition and its equality with
  retracts of transfinite composites of pushouts of coproducts of inner horns
  (`innerAnodyneExtensions_eq_retracts_transfiniteCompositions`). This is exactly
  ordinary simplicial-set saturation, with degreewise set colimits. It is not
  a presheaf-homotopy-colimit saturation substituted for the input condition.
* The first conclusion is
  `Enhanced.IsWeakHomotopyEquivalence
    (mappingSpacePre (Segal.discreteSpaceMap f) V)`
  for every `V`, `i`, `IsReedyFibrant V`, and `IsReedyWeakEquivalence i`.
  Its source is the model for `Map(dL,W)` and its target the model for `Map(dK,W)`.
  The map is actual restriction. The replacement map is assumed weak only in
  each outer degree; it is not required to be a chosen functorial replacement,
  a cofibration, an isomorphism, or a map satisfying any stronger condition.
* Naturality in the arrow is the second conjunction. For a commuting square
  `f ≫ b = a ≫ f'`, it asserts `b* ≫ f* = f'* ≫ a*`. Each map is the same existing
  `mappingSpacePre` applied to the actual discrete image. The equation is typed
  on `Map(dL',V) ⟶ Map(dK,V)`, with the contravariant directions checked.
* Naturality in W is the third conjunction. For every target map `g : V ⟶ V'`,
  it asserts `f* ≫ g_* = g_* ≫ f*`, using `mappingSpacePost` with dK and dL on
  the respective sides. These two naturality identities hold for all arrows and
  target diagrams, hence in particular for the inner-anodyne arrows and fibrant
  representatives in the first clause. They are equations of simplicial maps
  from the existing simplicial internal-hom bifunctor. They retain all simplices
  and their operators. Its composition and enriched functoriality supply the
  coherences, rather than selecting unrelated inverses on mapping-space components.
* No completeness predicate occurs anywhere. Reedy fibrancy is imposed only on
  V, the representative used to compute derived maps, never on W itself.

Dependency declarations used:

* `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.IsWeakHomotopyEquivalence`, the realization/component/based
  homotopy-group convention of the original statement dependency.
* `Sheaf.CategoryTheory.HomotopySegalSpace`:
  `SSet.HomotopySegal.IsHomotopySegalSpace`, with its existing path-model
  `target` and `comparison`. No private Segal predicate is introduced.
* `Sheaf.AlgebraicTopology.SimplicialSpaceReedyCartesian`:
  `SSet.SegalSpace.mappingSpace`, `mappingSpacePre`, `mappingSpacePost`,
  `IsReedyWeakEquivalence`, and the Reedy mapping-space interpretation.
  `IsReedyFibrant` is publicly provided there from its recorded
  `Sheaf.AlgebraicTopology.SegalCartesianExponent` interface.
* `Sheaf.AlgebraicTopology.SegalCategoricalEquivalence`:
  `SSet.Segal.discreteSpace` and `discreteSpaceMap` only. Its downstream
  categorical-equivalence theorem is not used to replace the statement.
* `Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Basic`:
  `SSet.innerAnodyneExtensions` and the cell-generation equality recorded by
  the Mathlib proof dependency `lem-coef-inner-horn-cell-generation`.
* `Sheaf.CategoryTheory.SpaceYonedaDensity`: the recorded
  `CategoryTheory.Spaces.space_yoneda_density`, imported non-publicly for the
  existing proof plan. The other non-Mathlib proof dependencies currently have
  no recorded module, so there is no published module of theirs to import.
  No unstated proof dependency is turned into an assumption of the theorem.

Edge cases checked before writing:

* The empty simplicial set, the empty target diagram, and identity maps are
  permitted; there is no nonemptiness or basepoint hypothesis. A map out of dK
  into the empty diagram exists precisely in the cases dictated by the actual
  mapping complex. Inner-anodyne maps preserve vertices, so empty/nonempty cases
  do not furnish a counterexample.
* Outer degrees zero and one are unrestricted by the Segal comparison. The
  existing `n+2` indexing begins at the two-edge case. Its joining-path target
  is the homotopy pullback for the unique inner two-horn.
* The input saturation includes arbitrary small transfinite constructions and
  retracts, including identities and empty attaching coproducts; no finite-cell
  or countability restriction is substituted.
* The naturality square directions were checked by their mapping-space source
  and target, including the identity square and target identity.
* Replacing W by an arbitrary Reedy equivalent V does not discard the identity
  replacement when W is already fibrant. Quantification does not require a
  special or injective replacement.

Searches for an existing exact statement (all run for Q141 and this item):

* `msearch.py leanfinder`, query: "An inner anodyne map induces an equivalence of
  derived mapping spaces into a homotopy Segal simplicial space". Eight hits,
  all strict Segal simplicial-set/nerve results; no space-valued homotopy Segal
  derived-mapping locality result. I read the returned strict Segal/quasicategory
  signatures and Mathlib's `Quasicategory/StrictSegal.lean`.
* `msearch.py loogle`, query: `"StrictSegal", "InnerAnodyne"`. Zero hits.
* `msearch.py grep`, query:
  `SegalSpace|Segal.*[Ii]nnerAnodyne|[Ii]nnerAnodyne.*Segal`. Zero hits.
* `msearch.py leansearch`, query: "Inner anodyne locality of space valued homotopy
  Segal diagrams". Eight hits concerning strict Segal structures, nerves,
  quasicategories, coskeleta and the Kan model generating class. None states
  locality in the coherent space-valued presheaf category.
* `rg` of the upstream `WeilConjectures` tree for this item's id and for
  `homotopySegal|[Dd]erivedMapping|Segal.*[Ll]ocal` found no exact statement.
* `rg` of the project's `lean/Sheaf` found the homotopy Segal, discrete-diagram
  and Reedy mapping-space constructions above. Existing vertical-division and
  coherent-realization inner-anodyne theorems concern different functors and
  conclusions. The existing inverse-evaluation theorem concerns the walking
  isomorphism and invertible arrows, not arbitrary inner-anodyne restrictions.
* `rg` of Mathlib, upstream, `lean/Sheaf`, and `dag/lean_names_upstream.json` for
  `SegalSpaceInnerAnodyneLocality|segal_space_inner_anodyne_locality` found no
  pre-existing declaration with this module/name.

Source verification: I opened https://arxiv.org/html/2311.13362v1 and read
Definitions 6.1--6.3, Proposition 6.4, Corollary 6.5 and Corollary 6.6 with its
proof. The terminal monoidal specialization gives the horn-locality and Segal
condition used here, without completeness. The module's docstring retains the
item's additional degreewise-set cell-transfer argument rather than assuming
that the discrete inclusion preserves arbitrary homotopy pushouts.
WANTED: an archived copy of this source in the project's literature collection;
the shared literature directory was kept read-only.

No statement fault or `STATEMENT-DISPUTED` issue was found. No dependency repair
or new definition node is needed. The only changed node fields are `lean` and
the three added, already landed entries of `stmt_deps`.

Validation: `scompile.py Q141 lem-coef-segal-space-inner-anodyne-locality` compiled
the delivered module through the prescribed server/overlay wrapper, with no
errors or warnings. Every Lean line is at most 100 characters. All universes
and variables are explicitly bound with `autoImplicit false`.

## Second reading by Q141

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
