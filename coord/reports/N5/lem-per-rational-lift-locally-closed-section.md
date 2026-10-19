## Worker report

The module `Sheaf.AlgebraicGeometry.RationalLiftLocallyClosedSection` states
`AlgebraicGeometry.rationalLift_iff_locallyClosed_section`. Its only proof is `sorry`.
The node is changed only in `lean`; its statement, dependencies and reviewed stage-1
proof remain unchanged. This is a stage-2 delivery of the already split node, not
another split. The earlier attempt's live-wins refusal concerned splitting a node
that Q59 had already reviewed. The current live node has no Lean record, so there
is no recorded statement declaration to overwrite. No repair note exists for it.

Source checked directly: ILO, Travaux de Gabber, Exposé II, Proposition 2.2.3,
printed p. 27 (PDF page 33). It assumes exactly a locally finite type morphism
with Noetherian target and identifies the completely decomposed locus with points
contained in a subscheme admitting a section. Its proof uses an open of the
reduced closure of the point. The node's five-step affine proof is included in the
theorem docstring, with its dependency names, including the quotient-factorization
repair made in the stage-1 review.

Every hypothesis and conclusion clause is rendered as follows:

- Schemes `X` and `Y`: `{X Y : Scheme.{u}}`; arbitrary explicitly declared `u`.
- Noetherian `X`, in the node's finite affine Noetherian cover sense:
  `[IsNoetherian X]`. Mathlib's
  `isNoetherian_iff_of_finite_affine_openCover` identifies this with precisely
  the finite affine cover criterion and `IsNoetherianRing` of the affine rings.
  `IsNoetherianRing` means that all ideals are finitely generated, as in the
  dependency `def-weil-pbc-noetherian-ring`. This is scheme Noetherianity,
  including Noetherian coordinate rings, rather than just topological Noetherianity.
- The morphism `f : Y → X`: `(f : Y ⟶ X)`.
- Locally finite type, without any global finiteness condition:
  `[LocallyOfFiniteType f]`, the recorded dependency declaration.
- A point of `X`: `(x : X)`.
- Equivalence of (i) and (ii): `↔`.
- A lift `y` with `f(y) = x`: `∃ y : Y, f y = x ∧ ...`.
- The *induced* residue-field homomorphism is an isomorphism:
  `IsIso (f.residueFieldMap y)`. Its domain is `X.residueField (f y)`,
  identified with `X.residueField x` by the preceding equality. This is an
  isomorphism condition on the actual induced map, not an arbitrary field isomorphism.
- A locally closed subscheme: `∃ (Z : Scheme.{u}) (j : Z ⟶ X), IsImmersion j ∧ ...`.
  Mathlib's `IsImmersion.isImmersion_iff_exists` identifies this exactly with
  a closed immersion followed by an open immersion, as in the dependency's statement
  and `mathlib_match`. It does not require `j` to be a closed immersion into all of `X`.
- Containing `x`: `x ∈ Set.range j`; the subscheme need not have singleton image.
- The section over this subscheme: `∃ s : Z ⟶ Y, s ≫ f = j`.
  Lean's composition order is the displayed mathematical equality `f ∘ s = j`.
- No quasi-compactness or separation hypothesis on `Y` or `f` appears.

Dependency declarations were read with their signatures and docstrings in the
pinned source; the corresponding modules are publicly imported:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`; its finite-affine-cover use is expressed by
  `AlgebraicGeometry.IsNoetherian` from `Mathlib.AlgebraicGeometry.Noetherian`.
- `def-weil-finite-type-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `AlgebraicGeometry.Scheme.residueField` and
  `AlgebraicGeometry.Scheme.Hom.residueFieldMap`.
- `def-weil-closed-immersion`:
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`; the same dependency's `mathlib_match`
  supplies `AlgebraicGeometry.IsImmersion` and
  `AlgebraicGeometry.IsImmersion.isImmersion_iff_exists` from
  `Mathlib.AlgebraicGeometry.Morphisms.Immersion`.

All proof dependencies were inspected. Their recorded modules are imported,
including the Mathlib leaves for field-valued points, their naturality, prime
residue-field algebra, principal localizations, and quotient closed immersions.
The project proof dependency is
`Sheaf.AlgebraicGeometry.ClosedImmersionResidueFieldIso`, declaration
`AlgebraicGeometry.Scheme.Hom.isIso_residueFieldMap_of_isClosedImmersion`.
Proof-only imports are non-public. No missing or unusable dependency was found.

Edge cases checked before writing:

- Empty `X`: the pointwise statement has no instance `x` and is vacuous.
- Empty `Y` and a specified point `x`: both sides are false. A right-hand witness
  contains a point over `x`, so its section cannot map to the empty scheme.
- Closed `x`: the closed reduced point can serve; no open-neighbourhood requirement
  stronger than a locally closed subscheme is present.
- Non-locally-closed generic `x`: the open of its reduced closure can contain `x`;
  no assumption that `{x}` itself is locally closed is introduced.
- Nonreduced `X`: the construction uses `A/p`, and the statement assumes no reducedness.
- No affine algebra generators: the docstring takes the common denominator to be `1`.
- Non-quasi-compact or nonseparated `Y`: only a local affine neighbourhood of the
  chosen lift is used. The binders impose neither property.
- Identity `f`: its residue-field maps are isomorphisms and `Z = X`, `j = s = id`
  supplies the second side. Any characteristic is allowed.
- Universe: all schemes belong to `Scheme.{u}` for arbitrary `u`; the constructed
  affine subscheme has the same size as its ambient scheme. No independent test-object
  universe or size-restricting hypothesis appears.

Searches for an existing declaration:

- `msearch.py leanfinder`, query: “A rational lift of a locally finite type scheme
  morphism at a point extends to a section over a locally closed subscheme containing
  that point”. Eight hits, principally `AlgebraicGeometry.spread_out_of_isGermInjective'`,
  `Scheme.PartialMap.ofFromSpecStalk`, and stalk-lift lemmas. The spreading-out lemma's
  full signature and docstring were read: it starts with a map from a stalk spectrum
  and requires germ-injectivity. It does not state this residue-field/locally-closed
  equivalence; forming the reduced closure is an additional argument.
- `msearch.py loogle`, query:
  `AlgebraicGeometry.IsImmersion, AlgebraicGeometry.Scheme.Hom.residueFieldMap`.
  Successful search, zero hits.
- `msearch.py grep`, query:
  `rational.*lift|locally.closed.*section|section.*locally.closed`, subdirectory
  `AlgebraicGeometry`. Successful search, zero hits.
- `rg` over the source project's `WeilConjectures` and this project's `lean/Sheaf`,
  query `lem-per-rational-lift-locally-closed-section|rationalLift|rational_lift|locally.closed.*section|section.*locally.closed`.
  No upstream statement; the item identifier appears only as a proof-plan reference
  in `CompletelyDecomposedEtaleFiniteSubcover`. Other matches concern unrelated
  stratifications and rational coefficient maps. No duplicate declaration found.
- Read the dependency's immersion definition and factorization characterization,
  and the Noetherian finite affine cover equivalence, so no private notion was needed.

No statement correction, new node, dependency repair, or disputed statement is needed.

## Second reading by N5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
