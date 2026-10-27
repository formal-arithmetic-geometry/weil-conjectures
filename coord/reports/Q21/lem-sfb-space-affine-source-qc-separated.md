## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceAffineSourceQCSeparated` states
`AlgebraicGeometry.AlgebraicSpace.quasiCompact_separated_of_affine_etale`.
Its sole theorem has proof `sorry`; no definitions or proofs are added.

Clause-by-clause correspondence:

- The size convention is implemented by the explicit `universe u` and
  `{S : Scheme.{u}}`; the scheme and presheaf universes are those of the
  existing algebraic-space interface. There are no coefficient or derived
  categories in this statement. `set_option autoImplicit false` forbids
  auto-bound parameters.
- An arbitrary scheme S and algebraic space Y over S are rendered by
  `{S : Scheme.{u}} (Y : AlgebraicSpace S)`.
- Absolute quasi-separatedness is `hY : IsAbsolutelyQuasiSeparated Y`.
  This is the existing affine-pair characterization of quasi-compactness
  of the absolute diagonal over Spec Z, including for a non-quasi-separated S.
  I read its definition and node and checked Stacks `spaces-properties.tex`,
  `lemma-characterize-quasi-separated`, Tag 0AHR, conditions (1) and (3).
  The already-landed node `def-sfb-space-absolute-quasi-separated` is added to
  `stmt_deps` under brief-stage2 section 5, STMT_DEPS MAY GAIN LANDED NODES.
  The natural-language statement is unchanged.
- The affine scheme over S is `(U : Over S) [IsAffine U.left]`.
  Bundling its structural morphism adds no restriction: a scheme mapping to
  Y inherits its morphism to S. Mathlib's `IsAffine` says the canonical map
  to Spec of global sections is an isomorphism.
- The morphism j is `(j : yoneda.obj U ⟶ Y.obj.obj)`, using exactly the
  representable-source natural-transformation interface of the space definition.
- Its étaleness is `hj : IsEtale j`: representability and étaleness on every
  scheme base change, with no surjectivity assumption.
- Quasi-compactness of j is the first conjunct `IsQuasiCompactPresheafMap j`.
  Unfolding the dependency definition quantifies over every affine scheme Z
  mapping to Y and asks for a quasi-compact scheme U' with a representable
  surjective étale map to the fibre product. This is precisely the atlas-based
  quasi-compactness in the node's specified sense.
- Separatedness is the second conjunct `IsSeparatedPresheafMap j`.
  Unfolding it gives `IsRepresentableWith` closed immersion for the canonical
  relative diagonal `diagonalPresheafMap j`: every scheme test is represented
  by a scheme with closed-immersion projection.
- No quasi-compactness of Y, condition on S, or nonemptiness is assumed.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`;
  the scheme definition and morphism structure were read with their docstrings.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsAlgebraicSpace`, `IsRepresentableWith`, and `IsEtale`.
  The space is the full subcategory of fppf sheaves with representable diagonal
  and a representable surjective étale scheme atlas. All signatures and
  relevant docstrings were read.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyQuasiSeparated`, with its
  full affine-pair definition.
- `Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal`:
  `AlgebraicGeometry.AlgebraicSpace.IsQuasiCompactPresheafMap`,
  `diagonalPresheafMap`, and `IsSeparatedPresheafMap`. Its locality theorem
  is not used as a hypothesis; the definitions are used directly.
- `def-weil-size-convention` has a convention-only Lean record, with no
  declaration or module to import. Universes are explicit in this module.

The recorded proof dependencies are imported for stage 3: the space fibre-product
module (`fibreProduct_isAlgebraicSpace`, `etale_fibreProduct_isScheme`), Mathlib
`Pullbacks` (`pullbackSpecIso`), `Morphisms.QuasiSeparated` (affine qcqs and
`quasiCompact_of_compactSpace`), `Morphisms.Separated` (affine schemes and
morphisms from separated schemes are separated), `Morphisms.Proper`
(`IsProper`, with `IsSeparated` as the diagonal definition), and
`Morphisms.ClosedImmersion` (`IsClosedImmersion.isStableUnderBaseChange`).
The theorem docstring carries both proof steps of the node, including the
absolute scheme product and both closed-immersion base changes.

Source checked: `literature/stacks-project/spaces-perfect.tex`, Tag 08IL,
`lemma-tor-qc-qs`, first proof paragraph. It assumes only quasi-separatedness
of the algebraic space and explicitly asserts both properties for affine étale j.

Edge cases checked before writing:

- U may be empty (Spec of the zero ring); its scheme tests and relative
  diagonal remain empty, with the required quasi-compactness and closed immersion.
- An affine test V may be empty; its fibre product is empty.
- Y may be empty; no nonempty-source map is asserted to exist.
- Y may be non-quasi-compact, for example an infinite disjoint union of affine
  schemes. The conclusion concerns the map and its affine tests, not Y itself.
- S may be non-quasi-separated. The existing absolute predicate, not the
  relative diagonal over S, is used; the proof product is over Spec Z.
- Y may be non-separated but quasi-separated. No affineness of U times_Y V
  is assumed; it need only be a quasi-compact scheme.
- Étale j need not be surjective or an immersion.

Searches for an existing statement (all run with `msearch.py`, group Q21,
item `lem-sfb-space-affine-source-qc-separated`):

- LeanFinder: `An etale morphism from an affine scheme to a quasi separated
  algebraic space is quasi compact and separated`. Eight hits, all scheme
  results, including `quasiCompact_affineProperty_iff_quasiSeparatedSpace`,
  `quasiSeparated_over_affine_iff`, and `quasiCompact_over_affine_iff`.
  None has an algebraic-space target.
- Loogle: `"QuasiSeparated", "QuasiCompact"`. Seven hits on scheme
  quasi-separated diagonals and quasi-compactness. No algebraic-space theorem.
- Mathlib grep: `QuasiSeparated.*[Aa]ffine|[Aa]ffine.*QuasiSeparated|AlgebraicSpace`
  in `AlgebraicGeometry`. Nine scheme-related hits; no algebraic-space declaration.
- LeanSearch: `A map from an affine scheme to a quasi separated algebraic space
  is quasi compact and separated`. Eight scheme-only hits, including
  `IsSeparated.of_isAffineHom` and `quasiCompact_over_affine_iff`; no exact match.
- Direct `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `AlgebraicSpace`, absolute-diagonal and quasi-separatedness predicates,
  and affine/quasi-compact combinations. The item appears in another theorem's
  proof docstring, with no declaration. The reusable absolute predicate was
  found in `AlgebraicSpaceAbsoluteQuasiSeparated.lean`; no theorem giving this
  conjunction was found. A further search for the proposed theorem name in both
  libraries, Mathlib, and `dag/lean_names_upstream.json` found no collision.

No disputed statement, new node, or dependency-interface repair is needed.

## Second reading by Q21

No independent worker reading: the dispatch brief prohibits starting other
agents and directs this worker to deliver. The maintainer performs the independent
review. The clause correspondence above is the author's own check.
