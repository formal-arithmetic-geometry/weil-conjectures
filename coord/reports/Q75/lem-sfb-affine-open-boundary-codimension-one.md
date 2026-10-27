## Worker report

The module `Sheaf.AlgebraicGeometry.AffineOpenBoundaryCodimensionOne` states
`AlgebraicGeometry.affine_open_boundary_codimension_one`, with proof `sorry`.
No definition is introduced. The node's statement, dependencies and proof remain unchanged.
The theorem docstring contains all four steps of the node's proof and their dependencies.

Source checked: `literature/stacks-project/divisors.tex`,
`lemma-complement-affine-open` (Tag 0BCV), the dense-open clause, and the proof through
`lemma-complement-affine-open-immersion` (0BCU) and `lemma-affine-punctured-spec` (0BCR).
The node states precisely this dense-open clause, without requiring global Noetherianity,
integrality, reducedness, finite dimension or a field.

Clause-by-clause correspondence:

- A scheme X: `(X : Scheme.{u})`, with the universe explicitly declared and unrestricted.
- X is separated: `[X.IsSeparated]`. Mathlib's
  `Scheme.isSeparated_iff_isClosedImmersion_prod_lift` identifies this with the absolute
  diagonal being a closed immersion, as the node requires.
- X is locally Noetherian: `[IsLocallyNoetherian X]`, the dependency's recorded class.
- U is an open subscheme of X: `(U : X.Opens)`. Its canonical inclusion is the Mathlib
  open immersion `U.ι`; `U.toScheme` is the restricted scheme, so no arbitrary immersion
  or extra structure is supplied.
- U is affine: `(hU : IsAffineOpen U)`. The definition is `IsAffine U`, namely affineness
  of that open subscheme.
- U is dense: `(hDense : Dense (U : Set X))`, equivalent to
  `closure (U : Set X) = Set.univ` by `dense_iff_closure_eq`.
- Z is any irreducible component of the closed boundary:
  `(Z : Set {x : X // x ∉ U})` and
  `(hZ : Z ∈ irreducibleComponents {x : X // x ∉ U})`. The complement is used as a
  subtype with its induced topology. Thus these are components of the boundary,
  not components of X that happen to miss U. The boundary is closed because U is open;
  no additional hypothesis is needed.
- xi is any generic point of Z: `(xi : X)` and
  `(hxi : IsGenericPoint xi (Subtype.val '' Z))`. The image places the same component
  in X. By definition this says `closure {xi} = Subtype.val '' Z`; it already implies
  xi belongs to Z. The boundary is closed, so this is equivalent to being generic in
  the boundary subspace. No point is chosen noncanonically and no uniqueness assumption
  is added.
- The local ring has dimension exactly one:
  `ringKrullDim (X.presheaf.stalk xi) = 1`. This is the actual structure-sheaf stalk
  with its commutative ring structure and Mathlib's Krull dimension in `WithBot ℕ∞`.
- If U = X, there are no boundary components. The theorem is universally quantified
  over Z with `hZ`, so this clause is correctly vacuous, without a separate conjunct.

Recorded statement dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`; the open-subscheme presentation uses the
  existing `Scheme.Opens` construction, rather than restating the predicate.
- `def-weil-irreducible-components`: Mathlib match
  `Mathlib.Topology.Irreducible`, `irreducibleComponents`, with definition
  `{s | Maximal IsIrreducible s}`. This is a usable Mathlib match and needs no repair.
- `def-sc-generic-point`: `Mathlib.Topology.Sober`, `IsGenericPoint`.
- `def-weil-pbc-krull-dimension-ring`: `Mathlib.RingTheory.KrullDimension.Basic`,
  `ringKrullDim`.

All their full signatures and docstrings were read in the pinned local Mathlib.
The public imports expose these notions, with the separated-scheme class supplied
by `Mathlib.AlgebraicGeometry.Morphisms.Separated` and scheme stalk dimension support
by `Mathlib.AlgebraicGeometry.Properties`.

Proof-only imports are `WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism`
(the recorded module, whose `Scheme.fromSpecStalk_local_properties` was read),
`Mathlib.RingTheory.Localization.Submodule`,
`Mathlib.RingTheory.Spectrum.Prime.Topology`, and
`Mathlib.AlgebraicGeometry.Morphisms.Affine`. The remaining already stated proof
dependencies are provided by the public Noetherian, Separated, Properties, Scheme,
OpenImmersion and AffineScheme modules. The proof prerequisite
`lem-sfb-affine-punctured-local-dimension` presently has neither a Lean record nor a
Mathlib match and consequently has no import yet. It is not needed to type the statement;
its future proof import is the maintainer's responsibility under stage 2 rule 7.

Edge cases checked before writing:

- X empty and U = X: the boundary is empty and has no irreducible components.
- Any affine X with U = X: again vacuous; no boundary point or component is forced.
- U empty and dense: X must be empty, so the same vacuous case applies.
- Spec of a DVR with U its generic point: U is dense affine and its unique boundary
  component is the closed point, whose local ring has dimension one.
- The standard affine chart of the projective plane: the boundary line has a
  dimension-one local ring at its generic point, although its closed points have
  dimension-two local rings. Quantification is correctly restricted to generic points.
- Reducible and nonreduced schemes remain allowed. Components are taken in the boundary
  subspace, and the dimension is of the original stalk, not its reduction or a
  quotient defining the boundary.
- Local Noetherianity is retained without adding quasi-compactness or global
  Noetherianity. The proof's Noetherian arguments take place on affine neighbourhoods.

Searches for an existing statement (all on 2026-10-24):

- `msearch.py ... leanfinder`, query: "The generic point of an irreducible component of
  the complement of a dense affine open in a separated locally Noetherian scheme has
  local ring of Krull dimension one". Eight hits: affine generic-point prime ideals,
  genericPoint_eq_bot_of_affine, scheme sobriety, function fields, locally Artinian
  schemes and height of closed points. None is the boundary theorem.
- `msearch.py ... loogle`, query: `AlgebraicGeometry.IsAffineOpen, ringKrullDim`.
  Zero hits.
- `msearch.py ... grep`, query:
  `complement.*affine|affine.*complement|codimension.*one`, subdirectory
  `AlgebraicGeometry`. Zero Mathlib hits.
- `msearch.py ... leansearch`, query: "The complement of a dense affine open in a
  separated locally Noetherian scheme has pure codimension one". Eight hits about
  Noetherian affine rings, quasi-separatedness, dominant open immersions,
  compactness of affine opens, zero loci and separated affine schemes; no match.
- `rg` of both `lean/WeilConjectures` and `lean/Sheaf` for
  `boundary.*codimension|affine.*boundary|complement.*affine|affine.*complement`:
  nearby results concern affine curve complements, Cartier boundary constructions,
  affine complements of ample divisors and smooth-group ample families; none states
  this general codimension theorem. The smooth-group module uses the later Cartier
  divisor construction, which is a different assertion with stronger hypotheses.
- `grep -rn 'lem-sfb-affine-open-boundary-codimension-one' lean/WeilConjectures`:
  no hits. `rg` for `affine_open_boundary_codimension_one` in Mathlib and both project
  trees: no existing declaration.
- Additional `rg` for `ringKrullDim.*= 1` in the two algebraic-geometry trees finds
  curve/DVR/normalization/branch statements, with no general dense-affine boundary
  result. No duplicate definition or exact existing statement was found.

No statement correction, new node, dependency repair, or disputed statement is needed.
Validation uses `scompile.py` for the delivered module and `deliver2.py --no-push`
for the complete packet; only the expected declaration-uses-sorry warning is permitted.

## Second reading by Q75

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
