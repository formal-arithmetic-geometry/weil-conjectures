## Worker report

The module `Sheaf.AlgebraicGeometry.FlatRelationQcImageIntersections` states
`AlgebraicGeometry.flat_relation_qc_image_intersections`, with its sole proof `sorry`.
No definitions, new nodes, dependency repairs, or statement corrections are needed.
The node copy changes only `lean`.

Read the item, every statement dependency and its recorded declarations, all proof
dependency records, and Stacks `groupoids.tex`, Tag 0APA,
`lemma-first-observation`, including its proof. The source proof establishes the
claimed facts without using groupoid laws. The module docstring gives the five
accepted proof steps and their DAG dependencies for stage 3.

Hypothesis and conclusion correspondence:

- Schemes `R,V`: `{R V : Scheme.{u}}`; the universe `u` is explicitly declared.
- Quasi-separated `V`: `[QuasiSeparatedSpace V]`. The recorded scheme notion is
  identified with this by `quasiSeparatedSpace_iff_quasiSeparated`, which says
  exactly `QuasiSeparatedSpace V ↔ QuasiSeparated (terminal.from V)`.
- Scheme morphisms `s,t`: `(s t : R ⟶ V)`.
- Flat and quasi-compact `s,t`: `[Flat s] [QuasiCompact s] [Flat t]
  [QuasiCompact t]`. In particular neither local finite presentation nor local
  finite type nor a relation law is assumed. The finite-type dependency defines
  quasi-compactness separately; only that clause is used.
- Every quasi-compact open `H`: `(H : V.Opens) (hH : IsCompact (H : Set V))`.
- The specified image `E`: always the literal set `t '' (s ⁻¹' (H : Set V))`.
  There is no arbitrary image or auxiliary map in the statement.
- Compactness in the induced topology: the first conjunct is `IsCompact E`.
  Mathlib `isCompact_iff_compactSpace` identifies this with compactness of the
  subtype, without a Hausdorff requirement.
- Generalization stability: the second conjunct quantifies `y ∈ E` and `y' : V`
  and states `y ∈ closure ({y'} : Set V) → y' ∈ E`. This is the exact closure
  direction of the node.
- A containing quasi-compact open exists: the third conjunct is
  `∃ H₂ : V.Opens, IsCompact (H₂ : Set V) ∧ E ⊆ (H₂ : Set V)`.
- Every such `H₂`: the fourth conjunct universally quantifies `H₂ : V.Opens`
  with precisely its compactness and containment hypotheses.
- Its family is the set
  `{U : Set V | U ⊆ (H₂ : Set V) ∧ IsOpen U ∧ IsCompact U ∧ E ⊆ U}`.
  Since `H₂` is open in `V`, a subset of `H₂` is relatively open exactly when
  it is open in `V`. The topology on that subset induced from `H₂` is the
  topology induced from `V`, so its compactness is the same. Consequently this
  predicate describes exactly the node's family, using ambient subsets to avoid
  coercion images between two different powersets.
- Nonemptiness is `.Nonempty` on precisely this family; the final equality is
  `E = ⋂₀` that same family in `Set V`.
- Each member is also a quasi-compact open of `V`: membership literally includes
  `IsOpen U ∧ IsCompact U`. This clause is encoded in the family predicate, not
  appended as a redundant tautological conjunct. A set of subsets of `V` is
  set-indexed, and its nonemptiness is explicit.
- No equivalence relation or invariance hypothesis occurs.

Statement dependency declarations used (the source signatures and docstrings
were read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom`, with its category notation `⟶`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`:
  `AlgebraicGeometry.QuasiSeparated` and its absolute characterization above;
  `QuasiSeparatedSpace` is the topological compact-open intersection condition.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`, whose
  affine-section definition is equivalent to the stalkwise condition by
  `Flat.iff_flat_stalkMap`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: the dependency module;
  `AlgebraicGeometry.QuasiCompact` from
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` is its relevant recorded
  declaration, defining compact preimages of compact opens.
- `Mathlib.Topology.Defs.Filter`: `IsCompact` and the associated `CompactSpace`
  convention, both without separation hypotheses.

All recorded proof interfaces are imported as proof dependencies where not
already statement imports: affine opens and affine compactness, compact ranges,
`Flat.generalizingMap`, the quasi-separated affine-cover criterion, scheme
prespectral/spectral instances, and
`Topology.generalizations_isCompact_sInter_isCompactOpen` from the upstream
`WeilConjectures.Topology.SpectralGeneralizations`. The upstream spectral theorem
and its full proof docstring were read; its retired `Sheaf` twin is not imported.

Edge cases checked before writing:

- Empty `H` or empty source: `E` is empty, compactness and generalization
  stability hold, and the empty open is a valid `H₂`.
- Empty `E` with arbitrary admissible `H₂`: the family contains the empty open,
  so its ambient intersection is empty; the family itself remains nonempty.
- Empty `H₂`: its family consists of the empty subset, giving exactly the
  empty image, rather than the universe from an empty indexing family.
- Identity maps: `E = H`, and `H` itself belongs to each applicable family.
- A DVR spectrum: if the closed point belongs to `E`, the closure condition
  requires its generic generalization to belong to `E`, in the correct direction.
- `V` need not be quasi-compact; only the chosen `H₂` is. The type of the family
  imposes no finiteness or countability restriction, and all universes are bound.

Searches actually run through `msearch.py` for this group and item:

- LeanFinder: `For flat quasi compact maps s t from a scheme R to a quasi
  separated scheme V the image t of s preimage of a compact open is compact
  stable under generalization and the intersection of compact open neighborhoods`.
  Eight hits: quasi-compact preimage statements, `Flat.generalizingMap`, and
  compactness equivalences; no theorem with all the item's clauses.
- Loogle: `AlgebraicGeometry.QuasiCompact, IsCompact`. Six hits:
  `quasiCompact_iff_forall_isAffineOpen`, `Scheme.Hom.isCompact_preimage`,
  `QuasiCompact.isCompact_preimage`, `QuasiCompact.mk`, `quasiCompact_iff`,
  `Scheme.Hom.isCompact_preimage_singleton`; no complete match.
- Mathlib grep: `image.*[Ii]nter.*[Cc]ompact|[Gg]eneri[cz]ation.*[Cc]ompact`
  under `AlgebraicGeometry`. One unrelated intersection-of-preimages calculation
  in `AffineTransitionLimit.lean:1301`; no complete match.
- LeanSearch: `The image of a quasi compact open under a flat scheme map is
  compact stable under generalization and an intersection of compact open
  neighborhoods`. Eight hits on quasi-compact preimages, flat generalizing
  maps, quasi-compactness constructors/recursors and base change; no complete match.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `flat.*relation|generalizations_isCompact|sInter.*isCompactOpen|qcImage|qc_image`
  found the reusable spectral theorem and unrelated results, not this statement.
  Searching `0APA` found the parent invariant-neighbourhood theorem, whose
  hypotheses involve a descent datum and whose conclusion does not state this
  node. It is not an existing match.
- Exact-name checks in `dag/lean_names_upstream.json`, Mathlib,
  `lean/WeilConjectures` and `lean/Sheaf` for
  `flat_relation_qc_image_intersections|FlatRelationQcImageIntersections` returned
  no declaration. The prescribed recursive grep for this node id in
  `lean/WeilConjectures` also returned no match.

No statement dispute or node fault was found. The example CompactObject module
is now withdrawn and has no declarations; the module-mode public-section format
was taken from current statement modules and the standing brief instead.

Validation: `scompile.py Q108 lem-a1-flat-relation-qc-image-intersections` compiled
the delivered module in sandbox and library modes with no errors or warnings
(reported 7.6 seconds and 27.8 seconds). Delivery preflight follows.

## Second reading by Q108

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
